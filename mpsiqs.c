#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>
#include <gmp.h>
#include <time.h>
#include <pthread.h>

#ifdef __APPLE__

#ifndef PTHREAD_BARRIER_H_
#define PTHREAD_BARRIER_H_

#define PTHREAD_BARRIER_SERIAL_THREAD 1

#include <errno.h>

typedef int pthread_barrierattr_t;
typedef struct
{
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    int count;
    int tripCount;
} pthread_barrier_t;


int pthread_barrier_init(pthread_barrier_t *barrier, const pthread_barrierattr_t *attr, unsigned int count)
{
	//attr=NULL;
    if(count == 0)
    {
        errno = EINVAL;
        return -1;
    }
    if(pthread_mutex_init(&barrier->mutex, 0) < 0)
    {
        return -1;
    }
    if(pthread_cond_init(&barrier->cond, 0) < 0)
    {
        pthread_mutex_destroy(&barrier->mutex);
        return -1;
    }
    barrier->tripCount = count;
    barrier->count = 0;

    return 0;
}

int pthread_barrier_destroy(pthread_barrier_t *barrier)
{
    pthread_cond_destroy(&barrier->cond);
    pthread_mutex_destroy(&barrier->mutex);
    return 0;
}

int pthread_barrier_wait(pthread_barrier_t *barrier)
{
    pthread_mutex_lock(&barrier->mutex);
    ++(barrier->count);
    if(barrier->count >= barrier->tripCount)
    {
        barrier->count = 0;
        pthread_cond_broadcast(&barrier->cond);
        pthread_mutex_unlock(&barrier->mutex);
        return 1;
    }
    else
    {
        pthread_cond_wait(&barrier->cond, &(barrier->mutex));
        pthread_mutex_unlock(&barrier->mutex);
        return 0;
    }
}

#endif // PTHREAD_BARRIER_H_
#endif // __APPLE__




#define md 4									//	# of threads

mpz_t n;										//	number to factor
size_t n_digits;
unsigned int num_p;								//	# of primes composing 'a'
unsigned int interval;							//	interval for "a" determination
float cap;										//	error accepted sieving with logarithm
unsigned long B;								//	smoothness bound
unsigned long num_pol;							//	polynomial range in which to sieve
unsigned long found_now=0, s_size=0;
mpz_t *total_pol=NULL, *smooth=NULL;
unsigned int *fact=NULL;

pthread_mutex_t mtx1;
pthread_barrier_t barr1;

struct thread_data
{
	pthread_t tid;
	unsigned long val;
	unsigned long *a;
	unsigned long *p;
	float *log_p;
	unsigned long p_size;
	unsigned long start;
};

char *error(char *msg)
{
	fprintf(stderr, "%s\n", msg);
	exit(EXIT_FAILURE);
}

void init()
{
	if (pthread_mutex_init(&mtx1, NULL))
		error("error in mutex init <mtx1>");
	if (pthread_barrier_init(&barr1, NULL, md))
		error("error in barrier init <barr1>");
}

void lock(pthread_mutex_t *mtx)
{
	if (pthread_mutex_lock(mtx))
		error("error in lock");
}

void unlock(pthread_mutex_t *mtx)
{
	if(pthread_mutex_unlock(mtx))
		error("error in unlock");
}

int legendre(unsigned long a, unsigned long m)
{
	unsigned int t;
	unsigned long app;
	a=a%m;
	//printf("%lu\n",m);
	t=1;
	while(a)
	{
		while(!(a%2))
		{
			a>>=1;
			if ((m%8==3) || (m%8==5))
				t=-t;
		}
		app=a;
		a=m;
		m=app;
		if ((a%4==3) && (m%4==3))
			t=-t;
		a=a%m;
	}
	if(m==1)
		return t;
	return 0;
}

void find_square_mpz(mpz_t x, mpz_t n, mpz_t p)			//solve x^2 congruent n mod p
{
	if (mpz_cmp_ui(p, 1)==0)
	{
		mpz_set_ui(x, 0);
		return;
	}
	
	unsigned long s=1, i;
	mpz_t n_app, app, app2, t, A, D, m, p_app;
	mpz_init(n_app);
	mpz_init_set(p_app, p);
	mpz_mod(n_app, n, p);
	//gmp_printf("n %Zd p %Zd\n", n_app, p);
	
	if (mpz_congruent_ui_p(p, 3, 8) || mpz_congruent_ui_p(p, 7, 8))
	{
		mpz_add_ui(p_app, p_app, 1);
		mpz_divexact_ui(p_app, p_app, 4);
		mpz_powm(x, n, p_app, p);
		//gmp_printf("first case:\n n=%Zd\n p=%Zd\n x=%Zd\n", n_app, p, x);
		mpz_clear(n_app);
		mpz_clear(p_app);
		return;
	}
	
	if (mpz_congruent_ui_p(p, 5, 8))
	{
		mpz_t c;
		mpz_init(c);
		mpz_add_ui(p_app, p_app, 3);
		mpz_divexact_ui(p_app, p_app, 8);
		mpz_powm(x, n, p_app, p);
		mpz_powm_ui(c, x, 2, p);
		if (!mpz_congruent_p(c, n, p))
		{
			mpz_set_ui(c, 2);
			mpz_sub_ui(p_app, p, 1);
			mpz_divexact_ui(p_app, p_app, 4);
			mpz_powm(c, c, p_app, p);
			mpz_mul(x, x, c);
			mpz_mod(x, x, p);
		}
		//gmp_printf("second case:\n n=%Zd\n p=%Zd\n x=%Zd\n", n_app, p, x);
		mpz_clear(n_app);
		mpz_clear(p_app);
		mpz_clear(c);
		return;
	}
	
	if (mpz_congruent_ui_p(p, 1, 8))
	{
		mpz_init_set_ui(x, 2);
		while(1)
		{
			if (mpz_legendre(x, p)==-1)
				break;
			mpz_add_ui(x, x, 1);
		}
		mpz_init_set(app, p_app);
		mpz_sub_ui(app, app, 1);
		while(mpz_divisible_2exp_p(app, s))
		{
			s++;
		}
		s--;
		mpz_init(t);
		mpz_init(A);
		mpz_init(D);
		mpz_init(m);
		mpz_tdiv_q_2exp(t, app, s);
		mpz_powm(A, n, t, p);
		mpz_powm(D, x, t, p);
		for(i=0; i<s; i++)
		{
			mpz_powm(app, D, m, p);
			mpz_mul(app, A, app);
			mpz_init(app2);
			mpz_ui_pow_ui(app2, 2, s-1-i);
			mpz_powm(app, app, app2, p);
			mpz_set_si(app2, -1);
			if (mpz_congruent_p(app, app2, p))
			{
				mpz_ui_pow_ui(app, 2, i);
				mpz_add(m, m, app);
			}
		}
		mpz_divexact_ui(m, m, 2);
		mpz_powm(D, D, m, p);
		mpz_add_ui(t, t, 1);
		mpz_divexact_ui(t, t, 2);
		mpz_powm(app2, n_app, t, p);
		mpz_mul(x, app2, D);
		mpz_mod(x, x, p);
		//gmp_printf("third case:\n n=%Zd\n p=%Zd\n x=%Zd\n", n_app, p, x);
		mpz_clear(n_app);
		mpz_clear(p_app);
		mpz_clear(t);
		mpz_clear(A);
		mpz_clear(D);
		mpz_clear(m);
		mpz_clear(app);
		mpz_clear(app2);
		return;
	}
		
	exit(EXIT_FAILURE);
}

void find_square(unsigned long *x_long, mpz_t n, unsigned long p)			//solve x^2 congruent n mod p
{
	unsigned long s=1, i;
	mpz_t n_app, app, app2, t, A, D, m, p_app, p_mpz, x;
	mpz_init(n_app);
	mpz_init(x);
	mpz_init_set_ui(p_mpz, p);
	mpz_init_set_ui(p_app, p);
	mpz_mod_ui(n_app, n, p);
	//gmp_printf("n %Zd p %Zd\n", n_app, p_mpz);
	
	if ((p%8==3) || (p%8==7))
	{
		mpz_add_ui(p_app, p_app, 1);
		mpz_divexact_ui(p_app, p_app, 4);
		mpz_powm(x, n, p_app, p_mpz);
		*x_long=mpz_get_ui(x);
		//gmp_printf("first case:\n n=%Zd\n p=%Zd\n x=%Zd\n", n_app, p_mpz, x);
		mpz_clear(n_app);
		mpz_clear(x);
		mpz_clear(p_mpz);
		mpz_clear(p_app);
		return;
	}
	
	if (p%8==5)
	{
		mpz_t c;
		mpz_init(c);
		mpz_add_ui(p_app, p_app, 3);
		mpz_divexact_ui(p_app, p_app, 8);
		mpz_powm(x, n, p_app, p_mpz);
		mpz_powm_ui(c, x, 2, p_mpz);
		if (!mpz_congruent_p(c, n, p_mpz))
		{
			mpz_set_ui(c, 2);
			mpz_sub_ui(p_app, p_mpz, 1);
			mpz_divexact_ui(p_app, p_app, 4);
			mpz_powm(c, c, p_app, p_mpz);
			mpz_mul(x, x, c);
			mpz_mod(x, x, p_mpz);
		}
		*x_long=mpz_get_ui(x);
		//gmp_printf("second case:\n n=%Zd\n p=%Zd\n x=%Zd\n", n_app, p_mpz, x);
		mpz_clear(n_app);
		mpz_clear(x);
		mpz_clear(p_mpz);
		mpz_clear(p_app);
		mpz_clear(c);
		return;
	}
	
	if (p%8==1)
	{
		mpz_set_ui(x, 2);
		while(1)
		{
			if (mpz_legendre(x, p_mpz)==-1)
				break;
			mpz_add_ui(x, x, 1);
		}
		mpz_init_set(app, p_app);
		mpz_sub_ui(app, app, 1);
		while(mpz_divisible_2exp_p(app, s))
		{
			s++;
		}
		s--;
		mpz_init(t);
		mpz_init(A);
		mpz_init(D);
		mpz_init(m);
		mpz_tdiv_q_2exp(t, app, s);
		mpz_powm(A, n, t, p_mpz);
		mpz_powm(D, x, t, p_mpz);
		for(i=0; i<s; i++)
		{
			mpz_powm(app, D, m, p_mpz);
			mpz_mul(app, A, app);
			mpz_init(app2);
			mpz_ui_pow_ui(app2, 2, s-1-i);
			mpz_powm(app, app, app2, p_mpz);
			mpz_set_si(app2, -1);
			if (mpz_congruent_p(app, app2, p_mpz))
			{
				mpz_ui_pow_ui(app, 2, i);
				mpz_add(m, m, app);
			}
		}
		mpz_divexact_ui(m, m, 2);
		mpz_powm(D, D, m, p_mpz);
		mpz_add_ui(t, t, 1);
		mpz_divexact_ui(t, t, 2);
		mpz_powm(app2, n_app, t, p_mpz);
		mpz_mul(x, app2, D);
		mpz_mod(x, x, p_mpz);
		*x_long=mpz_get_ui(x);
		//gmp_printf("third case:\n n=%Zd\n p=%Zd\n x=%Zd\n", n_app, p_mpz, x);
		mpz_clear(n_app);
		mpz_clear(x);
		mpz_clear(p_mpz);
		mpz_clear(p_app);
		mpz_clear(t);
		mpz_clear(A);
		mpz_clear(D);
		mpz_clear(m);
		mpz_clear(app);
		mpz_clear(app2);
		return;
	}
		
	exit(EXIT_FAILURE);
}

int solve(unsigned int *solution, unsigned long p_size, unsigned long s_size,
		  unsigned long *p)
{
	unsigned long i, j, k;
	mpz_t *esp_sum=alloca(p_size*sizeof(mpz_t));
	for(i=0; i<p_size; i++)
		mpz_init_set_ui(esp_sum[i], 0);
	mpz_t a, b, app, factor1, factor2;
	
	mpz_init_set_ui(a, 1);
	mpz_init_set_ui(b, 1);
	mpz_init(app);
	mpz_init(factor1);
	mpz_init(factor2);
	
	for(k=0; k<s_size; k++)
	{
		if (solution[k]!=0)
		{
			for(j=0; j<p_size; j++)
			{
				mpz_add_ui(esp_sum[j], esp_sum[j], fact[k*(p_size+1)+j+1]);
			}
			mpz_mul(a, a, smooth[k]);
			mpz_mod(a, a, n);
		}
	}
	
	for(j=0; j<p_size; j++)
	{
		if (mpz_cmp_ui(esp_sum[j], 0)>0)
		{
			mpz_set_ui(app, p[j]);
			mpz_divexact_ui(esp_sum[j], esp_sum[j], 2);
			mpz_powm(app, app, esp_sum[j], n);
			mpz_mul(b, b, app);
			mpz_mod(b, b, n);
		}
	}
	
	mpz_sub(app, a, b);
	mpz_gcd(factor1, app, n);
	//gmp_printf("a: %Zd b: %Zd\n", a, b);
	if (mpz_cmp_ui(factor1,1)!=0 && mpz_cmp(factor1, n)!=0)
	{
		mpz_divexact(factor2, n, factor1);
		gmp_printf("%Zd = %Zd * %Zd\n", n, factor1, factor2);
		return 1;
	}
	mpz_add(app, a, b);
	mpz_gcd(factor1, app, n);
	if (mpz_cmp_ui(factor1,1)!=0 && mpz_cmp(factor1, n)!=0)
	{
		mpz_divexact(factor2, n, factor1);
		gmp_printf("%Zd = %Zd * %Zd\n", n, factor1, factor2);
		return 1;
	}
	
	for(i=0; i<p_size; i++)
		mpz_clear(esp_sum[i]);
	mpz_clear(a);
	mpz_clear(b);
	mpz_clear(app);
	mpz_clear(factor1);
	mpz_clear(factor2);
	
	return 0;
}

void find_combinations(unsigned long punt, unsigned long n_size, unsigned long k_size, unsigned long *comb_size,
				  unsigned int **combinations, unsigned int *app_comb, unsigned int *app_size)
{
	unsigned long i, j;
	
	for(i=punt; i<n_size; i++)
	{
		app_comb[i]=1;
		(*app_size)++;
		if (*app_size==k_size)
		{
			(*comb_size)++;
			*combinations=realloc(*combinations, *comb_size*n_size*sizeof(unsigned int));
			for(j=0; j<n_size; j++)
				(*combinations)[((*comb_size)-1)*n_size+j]=app_comb[j];
		}
		find_combinations(i+1, n_size, k_size, comb_size, combinations, app_comb, app_size);
		app_comb[i]=0;
		(*app_size)--;
	}
}

unsigned int try_solutions(unsigned long p_size, unsigned long s_size, unsigned long dep_size, unsigned long *p, unsigned int *dep)
{
	unsigned long i, j;
	unsigned int *solution=malloc(s_size*sizeof(unsigned int));
	if (solution==NULL)
		error("error in solution malloc");
	
	for(i=0; i<dep_size; i++)
	{
		for(j=0; j<s_size; j++)
			solution[j]=dep[i*s_size+j];
		
		//printf("trying solution %lu/%lu\n", i+1, dep_size+1);
		if (solve(solution, p_size, s_size, p))
			return 1;
	}
	free(solution);
	return 0;
}

void new_print(unsigned int *bool_fact, unsigned int *sums, unsigned long size_or, unsigned long size_ver, unsigned long *sorting)
{
	unsigned long i, j;
	
	printf("bool_fact matrix:\n");
	for(i=0; i<size_ver; i++)
	{
		for(j=0; j<size_or; j++)
			printf("%u ", bool_fact[sorting[i]*size_or+j]);
		printf("\n");
	}
		
	printf("sums matrix:\n");
	for(i=0; i<size_ver; i++)
	{
		for(j=0; j<size_ver; j++)
			printf("%u ", sums[sorting[i]*size_ver+j]);
		printf("\n");
	}
}

unsigned int *complete_bit_gauss(unsigned int size_or, unsigned int *fact, unsigned long *dep_size)
{
	unsigned long row=0, col=0, j, end_row, i;
	unsigned int *dep;
	unsigned int row_bit_size=(s_size>>3) +1;
	mpz_t *sums=calloc(row_bit_size*s_size*sizeof(unsigned int), 1);
	if (sums==NULL)
		error("error in sums calloc");
	mpz_t *bool_fact=calloc(((size_or>>3)+1)*s_size*sizeof(unsigned int), 1);
	if (bool_fact==NULL)
		error("error in bool_fact calloc");
	
	for(j=0; j<s_size; j++)
	{
		//mpz_init(sums[j]);
		//mpz_init(bool_fact[j]);
		mpz_setbit(sums[j], j);
		for(i=0; i<size_or; i++)
			if (fact[j*size_or+i]%2)
				mpz_setbit(bool_fact[j], i);
	}
	
	while(col<size_or)
	{
		end_row=0;
		if(!mpz_tstbit(bool_fact[row], col))						//selecting pivot
		{
			j=row+1;
			while(j<s_size && !mpz_tstbit(bool_fact[j], col))
				j++;
			if (j<s_size)
			{
				mpz_swap(bool_fact[row], bool_fact[j]);
				mpz_swap(sums[row], sums[j]);
			}
			else 
				end_row++;
		}
		if (!end_row)
		{
			for(j=row+1; j<s_size; j++)
			{
				if (mpz_tstbit(bool_fact[j], col))
				{
					mpz_xor(bool_fact[j], bool_fact[j], bool_fact[row]);
					mpz_xor(sums[j], sums[j], sums[row]);
				}
			}
			row++;
		}
		col++;
	}
	*dep_size=s_size-row;
	dep=malloc(*dep_size*s_size*sizeof(unsigned int));
	if (dep==NULL)
		error("error in dep malloc");
	
	for(i=0; i<*dep_size; i++)
	{
		for(j=0; j<size_or; j++)
			dep[i*s_size+j]=mpz_tstbit(sums[row+i], j);
	}
	
	free(sums);
	free(bool_fact);
	
	return dep;
}

unsigned int *bit_gauss(unsigned int size_or, unsigned int *bool_fact, unsigned long *dep_size)
{
	unsigned int app;
	unsigned long row=0, col=0, j, end_row, i;
	unsigned int *dep;
	unsigned int row_bit_size=(s_size>>3) +1;
	mpz_t *sums=calloc(row_bit_size*s_size*sizeof(unsigned int), 1);
	if (sums==NULL)
		error("error in sums calloc");
	
	for(j=0; j<s_size; j++)
		mpz_setbit(sums[j], j);
	
	while(col<size_or)
	{
		end_row=0;
		if (!bool_fact[row*size_or+col])						//selecting pivot
		{
			j=row+1;
			while(j<s_size && !bool_fact[j*size_or+col])
				j++;
			if (j<s_size)
			{
				for(i=col; i<size_or; i++)
				{
					app=bool_fact[row*size_or+i];
					bool_fact[row*size_or+i]=bool_fact[j*size_or+i];
					bool_fact[j*size_or+i]=app;
				}
				mpz_swap(sums[row], sums[j]);
			}
			else 
				end_row++;
		}
		if (!end_row)
		{
			for(j=row+1; j<s_size; j++)
			{
				if (bool_fact[j*size_or+col])
				{
					for(i=col; i<size_or; i++)
					{
						bool_fact[j*size_or+i]^=bool_fact[row*size_or+i];
					}
					mpz_xor(sums[j], sums[j], sums[row]);
				}
			}
			row++;
		}
		col++;
		
	}
	*dep_size=s_size-row;
	dep=malloc(*dep_size*s_size*sizeof(unsigned int));
	if (dep==NULL)
		error("error in dep malloc");
	
	for(i=0; i<*dep_size; i++)
	{
		for(j=0; j<size_or; j++)
			dep[i*s_size+j]=mpz_tstbit(sums[row+i], j);
	}
	
	free(sums);
	return dep;
}

unsigned int *new_gauss_reduction(unsigned long size_or, unsigned int *bool_fact, unsigned long *dep_size)
{
	unsigned int app;
	unsigned long row=0, col=0, j, end_row, i;
	unsigned int *dep;
	unsigned int *sums=calloc(s_size*s_size*sizeof(unsigned int), 1);
	if (sums==NULL)
		error("error in sums calloc");
		
	for(j=0; j<s_size; j++)
	{
		sums[j*s_size+j]=1;
	}
	
	
	//new_print(bool_fact, sums, size_or, size_ver);
	while(col<size_or)
	{
		end_row=0;
		if (!bool_fact[row*size_or+col])						//selecting pivot
		{
			j=row+1;
			while(j<s_size && !bool_fact[j*size_or+col])
				j++;
			if (j<s_size)
			{
				//printf("swap rows %lu & %lu\n", row, j);
				for(i=col; i<size_or; i++)
				{
					app=bool_fact[row*size_or+i];
					bool_fact[row*size_or+i]=bool_fact[j*size_or+i];
					bool_fact[j*size_or+i]=app;
				}
				for(i=0; i<s_size; i++)
				{
					app=sums[row*s_size+i];
					sums[row*s_size+i]=sums[j*s_size+i];
					sums[j*s_size+i]=app;
				}
				//new_print(bool_fact, sums, size_or, size_ver);
			}
			else 
				end_row++;
		}
		if (!end_row)
		{
			for(j=row+1; j<s_size; j++)
			{
				if (bool_fact[j*size_or+col])
				{
					//printf("add rows %lu & %lu\n", j, row);
					for(i=col; i<size_or; i++)
					{
						bool_fact[j*size_or+i]^=bool_fact[row*size_or+i];
					}
					for(i=0; i<s_size; i++)
					{
						sums[j*s_size+i]^=sums[row*s_size+i];
					}
					
					//new_print(bool_fact, sums, size_or, size_ver);
				}
			}
			row++;
		}
		col++;
		
		//printf("gauss %lu/%lu\n", col, size_or);
	}
	*dep_size=s_size-row;
	dep=malloc(*dep_size*s_size*sizeof(unsigned int));
	if (dep==NULL)
		error("error in dep malloc");
	memcpy(dep, sums+row*s_size, *dep_size*s_size*sizeof(unsigned int));
	free(sums);
	
	return dep;
}

unsigned int *new_gauss_reduction_sorting(unsigned long size_or, unsigned int *bool_fact, unsigned long *dep_size)
{
	unsigned long app;
	unsigned long row=0, col=0, j, end_row, i;
	unsigned int *dep;
	unsigned int *sums=calloc(s_size*s_size*sizeof(unsigned int), 1);
	if (sums==NULL)
		error("error in sums calloc");
	unsigned long *sorting=malloc(s_size*sizeof(unsigned long));
	if (sorting==NULL)
		error("error in sorting malloc");
		
	for(j=0; j<s_size; j++)
	{
		sums[j*s_size+j]=1;
		sorting[j]=j;
	}
	
	
	//new_print(bool_fact, sums, size_or, size_ver, sorting);
	while(col<size_or)
	{
		end_row=0;
		if (!bool_fact[sorting[row]*size_or+col])						//selecting pivot
		{
			j=row+1;
			while(j<s_size && !bool_fact[sorting[j]*size_or+col])
				j++;
			if (j<s_size)
			{
				//printf("swap rows %lu & %lu\n", sorting[row], sorting[j]);
				app=sorting[row];
				sorting[row]=sorting[j];
				sorting[j]=app;
				
				//new_print(bool_fact, sums, size_or, size_ver, sorting);
			}
			else 
				end_row++;
		}
		if (!end_row)
		{
			for(j=row+1; j<s_size; j++)
			{
				if (bool_fact[sorting[j]*size_or+col])
				{
					//printf("add rows %lu & %lu\n", sorting[j], sorting[row]);
					for(i=col; i<size_or; i++)
					{
						bool_fact[sorting[j]*size_or+i]^=bool_fact[sorting[row]*size_or+i];
					}
					for(i=0; i<s_size; i++)
					{
						sums[sorting[j]*s_size+i]^=sums[sorting[row]*s_size+i];
					}
					
					//new_print(bool_fact, sums, size_or, size_ver, sorting);
				}
			}
			row++;
		}
		col++;
		
		//printf("gauss %lu/%lu\n", col, size_or);
	}
	*dep_size=s_size-row;
	dep=malloc(*dep_size*s_size*sizeof(unsigned int));
	if (dep==NULL)
		error("error in dep malloc");
	//memcpy(dep, sums+row*size_ver, *dep_size*size_ver*sizeof(unsigned int));
	for(i=0; i<*dep_size; i++)
		for(j=0; j<s_size; j++)
			dep[i*s_size+j]=sums[sorting[row+i]*s_size+j];
	free(sums);
	free(sorting);
	
	return dep;
}

unsigned long *find_primes(unsigned long bound, unsigned long *size)
{
	unsigned long i,j, count=1;
	mpz_t n_app;
	//unsigned long size=ceil(log(bound));
	unsigned long size_odds=ceil(bound/2)-1;
	unsigned int *odds=malloc(size_odds*sizeof(unsigned long));
	mpz_init(n_app);
	
	for(i=0; i<size_odds; i++)
		odds[i]=1;
		
	for(i=0; i<size_odds; i++)
	{	
		//printf("%lu\n", 2*i+3);
		if(odds[i])
		{
			mpz_mod_ui(n_app, n, 2*i+3);
			//printf("n_app %lu\n", mpz_get_ui(n_app));
			if (legendre(mpz_get_ui(n_app), 2*i+3)==1)
			{
				//printf("%lu\n", 2*i+3);
				count++;
			}
			else
				odds[i]=0;
			for(j=2*i+3+i; j<size_odds; j+=2*i+3)
				odds[j]=0;
		}
	}
	
	unsigned long *p=malloc(count*sizeof(unsigned long));
	p[0]=2;
	j=1;
	for(i=0;i<size_odds;i++)
	{
		if(odds[i])
		{
			p[j]=2*i+3;
			j++;
		}
	}
	mpz_clear(n_app);
	free(odds);
	//printf("%lu\n", j);
	*size=j;
	return p;
}

void multiply(unsigned long *sorting, unsigned long start, unsigned long count, unsigned int *b_fact, mpz_t *x,
			  unsigned long size_p, mpz_t *big_primes, unsigned long real_start)
{
	unsigned long i, j;
	for(i=1; i<count; i++)
	{
		mpz_mul(x[real_start+sorting[start+i]-1], x[real_start+sorting[start+i]-1], x[real_start+sorting[start]-1]);
		mpz_mod(x[real_start+sorting[start+i]-1], x[real_start+sorting[start+i]-1], n);
		mpz_pow_ui(big_primes[start+real_start+i], big_primes[start+real_start+i], 2);
		for(j=0; j<size_p; j++)
		{
			b_fact[(sorting[start+i]-1)*size_p+j]+=b_fact[(sorting[start]-1)*size_p+j];
			//mpz_add(fact[(sorting[start+i]-1)*size_p+j], fact[(sorting[start+i]-1)*size_p+j], fact[(sorting[start]-1)*size_p+j]);
		}
	}
}

void bubble_sort(unsigned long *sorting, mpz_t *big_primes, unsigned long start)
{
	unsigned long i, j, app;
	unsigned int swap=1;
	
	while(swap)
	{
		swap=0;
		for(i=0; i<found_now-1; i++)
		{
			for(j=i+1; j<found_now; j++)
			{
				if (mpz_cmp(big_primes[start+i], big_primes[start+j])>0)
				{
					app=sorting[i];
					sorting[i]=sorting[j];
					sorting[j]=app;
					mpz_swap(big_primes[start+i], big_primes[start+j]);
					swap=1;
				}
			}
		}
	}
}

/*mpz_t *sort(mpz_t *big_primes, unsigned int **b_fact, unsigned long size_p)
{
	unsigned long i, j, count=1, new_size=s_size-(found_now), real_found=found_now, start=s_size-(found_now);
	unsigned int *new_fact;
	unsigned long *sorting=malloc(found_now*sizeof(unsigned long));
	if (sorting==NULL)
		error("error in sorting malloc");
	mpz_t *new_x;
	mpz_t prime_app;
	
	for(i=0; i<found_now; i++)
		sorting[i]=i+1;
	
	printf("s_size sort %lu\n", s_size);
	//fflush(stdout);
	
	bubble_sort(sorting, big_primes, start);

	
	mpz_init_set(prime_app, big_primes[start]);
	if (mpz_cmp_ui(prime_app, 1)==0)
		new_size++;
	for(i=1; i<found_now; i++)
	{
		if (mpz_cmp_ui(big_primes[start+i], 1)>0)
		{
		if (mpz_cmp(prime_app, big_primes[start+i])==0)
			count++;
		else
		{
			if (count==1)
			{
				//gmp_printf("del1 row %lu\n", i-1);
				if (mpz_cmp_ui(prime_app, 1)>0)
					sorting[i-1]=0;
			}
			else if (mpz_cmp_ui(prime_app, 1)>0)
			{
				new_size+=(count-1);
				multiply(sorting, i-count, count, *b_fact, x, size_p, big_primes, start);
				//gmp_printf("del2 row %lu\n", i-count);
				sorting[i-count]=0;
			}
			else
				new_size+=count;
			count=1;
			mpz_set(prime_app, big_primes[start+i]);
		}
		}
		else
			new_size++;
	}
	if (count==1)
	{
		//gmp_printf("del3 row %lu\n", *s_size-1);
		if (mpz_cmp_ui(prime_app, 1)>0)
			sorting[found_now-1]=0;
	}
	new_fact=calloc(new_size*size_p*sizeof(mpz_t), 1);
	if (new_fact==NULL)
		error("error in new_fact calloc");
	new_x=calloc(new_size*sizeof(mpz_t), 1);
	if (new_x==NULL)
		error("error in new_x calloc");
	
	for(i=0; i<real_found; i++)
	{
		if (sorting[i]==0)
		{
			real_found--;
			for(j=i+1; j<real_found; j++)
			{
				sorting[j-1]=sorting[j];
				mpz_set(big_primes[start+j-1], big_primes[start+j]);
			}
			i--;
		}
	}
	
	for(i=0; i<start; i++)
		mpz_init_set(new_x[i], x[i]);
	
	for(i=0; i<real_found; i++)
	{
		mpz_init_set(new_x[i+start], x[start+sorting[i]-1]);
		for(j=0; j<size_p; j++)
			new_fact[i*size_p+j]=(*b_fact)[(sorting[i]-1)*size_p+j];
	}

	
	for(i=0; i<s_size; i++)
		mpz_clear(x[i]);
		
	for(i=real_found; i<found_now; i++)
		mpz_clear(big_primes[start+i]);
		
	s_size=new_size;
	found_now=real_found;
	printf("b_fact1 %d\n", (*b_fact)[2]);
	fflush(stdout);
	free(*b_fact);
	free(x);
	free(sorting);
	mpz_clear(prime_app);
	*b_fact=new_fact;
	printf("real_found %lu real_size %lu\n", found_now, s_size);
	return new_x;
}*/

/*unsigned int *b_smooth(unsigned int **old_fact, mpz_t **smooth, mpz_t **big_primes, unsigned long *p, unsigned long size_p)
{
	unsigned long i, j;
	mpz_t pol;
	mpz_init(pol);
	
	*big_primes=realloc(*big_primes, (s_size)*sizeof(mpz_t));
	if (big_primes==NULL)
		error("error in big_primes realloc");
	for(i=s_size-(found_now); i<s_size; i++)
	{
		mpz_init_set_ui((*big_primes)[i], 1);
	}
	
	//printf("size_p %lu found_now %lu\n", size_p, *found_now);
	//fflush(stdout);
	unsigned int *b_fact=calloc((size_p+1)*(found_now)*sizeof(unsigned int),1);
	if (b_fact==NULL)
		error("error in fact calloc");
		
	for(i=0; i<found_now; i++)
	{
		//mpz_pow_ui(pol, (*smooth)[s_size-(found_now)+i], 2);
		mpz_pow_ui(pol, total_pol[i], 2);
		
		mpz_sub(pol, pol, n);
		//gmp_printf("%Zd   : ", (*smooth)[*s_size-(*found_now)+i]);
		if (mpz_sgn(pol)==-1)
		{
			b_fact[i*(size_p+1)]=1;
			mpz_abs(pol, pol);
			//printf("- ");
		}
		for(j=1; j<size_p+1; j++)
		{
			while (mpz_divisible_ui_p(pol, p[j-1]))
			{
				b_fact[i*(size_p+1)+j]++;
				mpz_divexact_ui(pol, pol, p[j-1]);
			}
			if (b_fact[i*(size_p+1)+j]!=0)
				//gmp_printf("%lu^%u ", p[j-1], fact[i*(size_p+1)+j]);
			if (mpz_cmp_ui(pol, p[j-1])<0)
				break;
		}
		if (mpz_cmp_ui(pol, 1)>0)
		{
			mpz_set((*big_primes)[s_size-(found_now)+i], pol);
			//gmp_printf("* big prime %Zd ", pol);
		}
		//gmp_printf("* (a) %Zd\n", a_pol);
	}
	
	sort(*big_primes, &b_fact, size_p+1);
		
	*big_primes=realloc(*big_primes, s_size*sizeof(mpz_t));
	if (big_primes==NULL)
		error("error in big_primes realloc");
	*old_fact=realloc(*old_fact, s_size*(size_p+1)*sizeof(unsigned int));
	if (old_fact==NULL)
		error("error in old_fact realloc");
	//memcpy(*old_fact+((s_size)-(found_now))*(size_p+1), b_fact, (size_p+1)*(found_now)*sizeof(unsigned int));
	for(i=0; i<found_now; i++)
		for(j=0; j<size_p+1; j++)
			(*old_fact)[(s_size-found_now+i)*(size_p+1)+j]=b_fact[i*(size_p+1)+j];
	free(b_fact);
	mpz_clear(pol);
	

	return *old_fact;
}*/

void new_b_smooth(unsigned long *p, unsigned long size_p)
{
	unsigned long i, j, k=0;
	mpz_t pol;
	mpz_init(pol);
	unsigned int *app_fact=malloc((size_p+1)*sizeof(unsigned int));
	if (app_fact==NULL)
		error("error in app_fact malloc");

	
	//printf("size_p %lu found_now %lu\n", size_p, *found_now);
	//fflush(stdout);
	
	for(i=0; i<found_now; i++)
	{
		for(j=0; j<size_p+1; j++)
			app_fact[j]=0;
		mpz_pow_ui(pol, total_pol[i], 2);
		
		mpz_sub(pol, pol, n);
		//gmp_printf("%Zd   : ", pol);
		if (mpz_sgn(pol)==-1)
		{
			app_fact[0]=1;
			mpz_abs(pol, pol);
			//printf("- ");
		}
		for(j=1; j<size_p+1; j++)
		{
			while (mpz_divisible_ui_p(pol, p[j-1]))
			{
				app_fact[j]++;
				mpz_divexact_ui(pol, pol, p[j-1]);
			}
			//if (app_fact[j]!=0)
			//	gmp_printf("%lu^%u ", p[j-1], app_fact[j]);
		}
		if (mpz_cmp_ui(pol, 1)==0)
		{
			fact=realloc(fact, (s_size+k+1)*(size_p+1)*sizeof(unsigned int));
			for(j=0; j<size_p+1; j++)
				fact[(s_size+k)*(size_p+1)+j]=app_fact[j];
			smooth=realloc(smooth, (s_size+k+1)*sizeof(mpz_t));
			if (smooth==NULL)
				error("error in smooth realloc");
			mpz_init_set(smooth[s_size+k], total_pol[i]);
			k++;
		}
		//printf("\n");
	}
	
	s_size+=k;
	
	free(app_fact);
	mpz_clear(pol);
	
}

void *log_sieve_smooth(void *arg)
{
	unsigned long a_count;
	
	mpz_t a_pol, inv, b_si, app, app2, gamma;
	int brr;
	unsigned int zero2=0;
	unsigned long index, ni, comb_size=0;
	unsigned long i, j, k, start_index, count=0;
	struct thread_data td=*((struct thread_data *) arg);
	unsigned long p_size=td.p_size;
	unsigned long *p=td.p;
	unsigned long *a=td.a;
	float *log_p=td.log_p;
	unsigned long start=td.start+td.val;
	
	start-=2*interval;
	
	long *sol1=calloc(p_size*sizeof(long), 1);
	if (sol1==NULL)
		error("error in sol1 calloc");
	long *sol2=calloc(p_size*sizeof(long), 1);
	if (sol2==NULL)
		error("error in sol2 calloc");
	mpz_t *B_si=malloc(num_p*sizeof(mpz_t));
	if (B_si==NULL)
		error("error in B_si malloc");
	mpz_t *B_a_inv=malloc(num_p*p_size*sizeof(mpz_t));
	if (B_a_inv==NULL)
		error("error in B_a_inv malloc");
	mpz_t *p_pol=malloc(num_p*sizeof(mpz_t));
	if (p_pol==NULL)
		error("error in p_pol malloc");
	float *pol=malloc(2*num_pol*sizeof(float));
	if (pol==NULL)
		error("error in pol calloc");
	mpz_t *s_pol=malloc(2*num_pol*sizeof(mpz_t));
	if (s_pol==NULL)
		error("error in s_pol malloc");
	unsigned long *p_interval=malloc(interval*sizeof(unsigned long));
	if (p_interval==NULL)
		error("error in p_interval malloc");
	unsigned int *app_combinations=calloc(interval*sizeof(unsigned int), 1);
	if (app_combinations==NULL)
		error("error in app_combinations malloc");
	unsigned int **combinations=malloc(0);
	
	mpz_init(b_si);
	mpz_init(app);
	mpz_init(app2);
	mpz_init(a_pol);
	mpz_init(inv);
	mpz_init(gamma);
	for(i=0; i<num_p; i++)
	{
		mpz_init(p_pol[i]);
		mpz_init(B_si[i]);
		for(j=0; j<p_size; j++)
			mpz_init(B_a_inv[j*num_p+i]);
	}
	
	i=start;
	for(j=0; j<interval; j++)
	{
		p_interval[j]=p[i];
		i+=md;
	}
	//gmp_printf("cap: %f\n", cap);
	
	find_combinations(0, interval, num_p, &comb_size, combinations, app_combinations, &zero2);
	a_count=comb_size*0.33;
	
	do
	{
		
		j=0;
		mpz_set_ui(a_pol, 1);
		for(i=0; i<interval; i++)
		{
			if ((*combinations)[a_count*interval+i])
			{
				mpz_set_ui(p_pol[j], p_interval[i]);
				mpz_mul(a_pol, a_pol, p_pol[j]);
				j++;
			}
		}
		
		for(j=0; j<num_p; j++)
		{
			find_square_mpz(gamma, n, p_pol[j]);
			mpz_divexact(inv, a_pol, p_pol[j]);
			mpz_invert(inv, inv, p_pol[j]);
			mpz_mul(gamma, gamma, inv);
			mpz_mod(gamma, gamma, p_pol[j]);
			mpz_mul_ui(app, gamma, 2);
			if (mpz_cmp(app, p_pol[j])>0)
				mpz_sub(gamma, p_pol[j], gamma);
			mpz_set(B_si[j], a_pol);
			mpz_divexact(B_si[j], B_si[j], p_pol[j]);
			mpz_mul(B_si[j], B_si[j], gamma);
		}
		
		for(j=1; j<p_size; j++)
		{
			if (mpz_divisible_ui_p(a_pol, p[j])==0)
			{
				
				mpz_set_ui(app, p[j]);
				mpz_invert(inv, a_pol, app);
				
				for(k=0; k<num_p; k++)
				{
					mpz_mul_ui(B_a_inv[j*num_p+k], B_si[k], 2);
					mpz_mul(B_a_inv[j*num_p+k], B_a_inv[j*num_p+k], inv);
					mpz_mod(B_a_inv[j*num_p+k], B_a_inv[j*num_p+k], app);
				}
			}
		}
		
		for(index=1; index<pow(2, num_p-1); index++)
		{
			count=0;
			ni=0;
			if (index==1)
			{
				mpz_set_ui(b_si, 0);
				for(i=0; i<num_p; i++)
					mpz_add(b_si, b_si, B_si[i]);
					
				for(i=1; i<p_size; i++)
				{
					if (mpz_divisible_ui_p(a_pol, p[i])==0)
					{
						mpz_set_ui(app2, p[i]);
						mpz_invert(inv, a_pol, app2);
						mpz_set_ui(app, a[i]);
						mpz_sub(app2, app, b_si);
						mpz_mul(app2, inv, app2);
						
						mpz_add_ui(app2, app2, num_pol);
						
						mpz_mod_ui(app2, app2, p[i]);
						sol1[i]=mpz_get_ui(app2);
						mpz_add(app2, app, b_si);
						mpz_neg(app2, app2);
						mpz_mul(app2, inv, app2);
						
						mpz_add_ui(app2, app2, num_pol);
						
						mpz_mod_ui(app2, app2, p[i]);
						sol2[i]=mpz_get_ui(app2);
					}
					else
					{
						sol1[i]=-1;
						sol2[i]=-1;
					}
				}
			}
			else
			{
				mpz_set_ui(app, 2*(index-1));
				while(mpz_divisible_2exp_p(app, ni))
					ni++;
				ni--;
				//printf("ni %lu\n", ni);
				mpz_set_ui(app, (index-1));
				mpz_cdiv_q_2exp(app, app, ni);
				
				ni--;
				
				mpz_mul_ui(app2, B_si[ni], 2);
				if (!mpz_odd_p(app))
				{
					mpz_add(b_si, b_si, app2);
					for(i=1; i<p_size; i++)
					{
						if (mpz_divisible_ui_p(a_pol, p[i])==0)
						{
							mpz_ui_sub(app2, sol1[i], B_a_inv[i*num_p+ni]);
							mpz_mod_ui(app2, app2, p[i]);
							sol1[i]=mpz_get_ui(app2);
							mpz_ui_sub(app2, sol2[i], B_a_inv[i*num_p+ni]);
							mpz_mod_ui(app2, app2, p[i]);
							sol2[i]=mpz_get_ui(app2);
						}
					}
				}
				else
				{
					mpz_sub(b_si, b_si, app2);
					for(i=1; i<p_size; i++)
					{
						if (mpz_divisible_ui_p(a_pol, p[i])==0)
						{
							mpz_add_ui(app2, B_a_inv[i*num_p+ni], sol1[i]);
							mpz_mod_ui(app2, app2, p[i]);
							sol1[i]=mpz_get_ui(app2);
							mpz_add_ui(app2, B_a_inv[i*num_p+ni], sol2[i]);
							mpz_mod_ui(app2, app2, p[i]);
							sol2[i]=mpz_get_ui(app2);
						}
					}
				}
					
			}
			
			for(i=0; i<2*num_pol; i++)
				pol[i]=0.0f;
			for(i=1; i<p_size; i++)
			{
				if (sol1[i]!=-1)
					for(start_index=sol1[i]; start_index<2*num_pol; start_index+=p[i])
					{
						pol[start_index]+=log_p[i];
					}
				
				if (sol2[i]!=-1)
					for(start_index=sol2[i]; start_index<2*num_pol; start_index+=p[i])
					{
						pol[start_index]+=log_p[i];
					}
			}
			
			
			for(i=0; i<2*num_pol; i++)
			{
				if (pol[i]>cap)
				{
					mpz_init(s_pol[count]);
					mpz_mul_si(s_pol[count], a_pol, i-num_pol);
					mpz_add(s_pol[count], s_pol[count], b_si);
					count++;
				}
			}
			if (count)
			{
				lock(&mtx1);
				
				found_now+=count;
				total_pol=realloc(total_pol, found_now*sizeof(mpz_t));
				if (total_pol==NULL)
					error("error in total_pol realloc");
				for (i=0; i<count; i++)
				{
					mpz_init_set(total_pol[found_now-count+i], s_pol[i]);
					mpz_clear(s_pol[i]);
				}
				unlock(&mtx1);
			}
			
			
				
			//printf("pre-smooth found_now %lu\n", found_now);
			
			
			if (td.val==0)
			{
				//printf("ciclo\n");
				lock(&mtx1);
				if (found_now)
				{
					new_b_smooth(p, p_size);
					
					for(i=0; i<found_now; i++)
						mpz_clear(total_pol[i]);
					
					//printf("s_size: %lu found_now %lu\n", s_size, found_now);
					
					found_now=0;
					
				}
				unlock(&mtx1);
			}
			
			brr=pthread_barrier_wait(&barr1);
			if (brr!=0 && brr!=PTHREAD_BARRIER_SERIAL_THREAD)
				error("error in barrier wait");
			
			if (s_size>=(p_size+2))
					break;
		}
		
		a_count=(a_count+1)%comb_size;
		
		if (s_size>p_size+2)
			break;
	}
	while(1);
	
	free(pol);
	free(s_pol);
	for(i=0; i<num_p; i++)
	{
		mpz_clear(p_pol[i]);
		mpz_clear(B_si[i]);
		for(j=0; j<p_size; j++)
			mpz_clear(B_a_inv[j*num_p+i]);
	}
	mpz_clear(b_si);
	mpz_clear(app);
	mpz_clear(app2);
	mpz_clear(a_pol);
	mpz_clear(inv);
	mpz_clear(gamma);
	free(p_interval);
	free(p_pol);
	free(B_si);
	free(B_a_inv);
	free(sol1);
	free(sol2);
	
	printf("thread %lu exit\n", td.val);
	pthread_exit(NULL);
}

int main(int argc, char *argv[])
{ 
	
	if (argc!=2)
	{
		fprintf(stderr, "Usage: %s <num>\n", argv[0]);
		return EXIT_FAILURE;
	}
	
	mpz_init_set_str(n, argv[1], 10);
	
	n_digits=mpz_sizeinbase(n, 10);
	printf("# of digits: %ld\n", n_digits);
	
	if (n_digits>51)
		cap= (float) 8.5/10;
	else
		cap= (float) 9/10;
		
	if (n_digits>66)
		num_p=8;
	else if (n_digits>50)
		num_p=7;
	else if (n_digits>40)
		num_p=6;
	else if (n_digits>30)
		num_p=4;
	else
		num_p=3;
		
	if (n_digits<50)
		B=50000;
	else if (n_digits<61)
		B=50000+(n_digits-51)*5000;
	else if (n_digits<70)
		B=100000+(n_digits-61)*10000;
	else
		B=270000+(n_digits-70)*30000;
		
	interval=2*num_p;
	num_pol=B/3;
	
	printf("Parameters: B=%lu,   num_pol=%lu,   num_p=%u,   interval=%u,   cap=%.f%%\n", B, num_pol, num_p, interval, cap*100);
	printf("Sieving primes\n");
	
	struct timespec start_time, mid_time, end_time;
	unsigned int *dep;
	unsigned long i=0, p_size, dep_size, start;
	unsigned long *p=find_primes(B, &p_size);
	unsigned long *a=malloc(p_size*sizeof(unsigned long));
	float *log_p=malloc(p_size*sizeof(float));
	struct thread_data *td=malloc(md*sizeof(struct thread_data));
	mpz_t sr, rem;
	mpz_t ideal_a;
	fact=malloc(0);
	total_pol=malloc(0);
	
	/*for(i=0; i<p_size; i++)
		printf("%lu\n", p[i]);*/
	
	mpz_init(sr);
	mpz_init(rem);
	mpz_sqrtrem(sr, rem, n);
	
	if (!mpz_sgn(rem))
	{
		gmp_printf("Perfect square of %Zd\n\n", sr);
		return EXIT_SUCCESS;
	}
	
	mpz_mul_ui(rem, sr, num_pol);
	cap*=mpz_sizeinbase(rem, 10);
	mpz_add_ui(sr, sr, 1);			// square root ceiling
	
	init();
	
	if (clock_gettime(CLOCK_REALTIME, &start_time)==-1)
		error("error in gettime");
	
	for(i=0; i<p_size; i++)
		log_p[i]=log10(p[i]);
	
	printf("Factor base size: %lu\n", p_size);
	printf("Finding roots\n");
	
	a[0]=1;
	for(i=1; i<p_size; i++)
		find_square(&a[i], n, p[i]);
		
	printf("Sieving smooths\n");
	
	smooth=malloc(0);
	
	mpz_init_set_ui(ideal_a, 2);
	mpz_mul(ideal_a, ideal_a, n);
	mpz_sqrt(ideal_a, ideal_a);
	mpz_tdiv_q_ui(ideal_a, ideal_a, num_pol);
	
	/*mpz_init(ideal_a);
	mpz_ui_pow_ui(ideal_a, num_p, 2);
	mpz_mul_ui(ideal_a, ideal_a, 2);
	mpz_tdiv_q(ideal_a, n, ideal_a);
	mpz_sqrt(ideal_a, ideal_a);*/
	
	mpz_root(rem, ideal_a, num_p);
	i=0;
	while(mpz_cmp_ui(rem, p[i])>0)
		i++;
	start=i-md;
	
	for(i=0; i<md; i++)
	{
		td[i].val=i;
		td[i].a=a;
		td[i].p=p;
		td[i].log_p=log_p;
		td[i].p_size=p_size;
		td[i].start=start;
		if (pthread_create(&(td[i].tid), NULL, log_sieve_smooth, (void *) &td[i]))
			error("error in thread creation");
	}
	for(i=0; i<md; i++)
		pthread_join(td[i].tid, NULL);
	
	if (clock_gettime(CLOCK_REALTIME, &mid_time)==-1)
		error("error in gettime");
		
	printf("Sieve achieved in %lu seconds\n", mid_time.tv_sec-start_time.tv_sec);
	printf("Smooths found %lu\n", s_size);
	printf("solving matrix\n");
	
	dep=complete_bit_gauss(p_size+1, fact, &dep_size);
	//dep=bit_gauss(p_size+1, bool_fact, &dep_size);
	/*if (p_size<10000)
		dep=new_gauss_reduction(p_size+1, bool_fact, &dep_size);
	else
		dep=new_gauss_reduction_sorting(p_size+1, bool_fact, &dep_size);
	
	printf("matrix solutions\n");
	for(i=0; i<dep_size; i++)
	{
		for(j=0; j<s_size; j++)
			printf("%u ", dep[i*s_size+j]);
		printf("\n");
	}*/
	
	printf("Testing solutions\n");
		
	if (!try_solutions(p_size, s_size, dep_size, p, dep))
		error("Divisor not found");
	
	if (clock_gettime(CLOCK_REALTIME, &end_time)==-1)
		error("error in gettime");
	
	printf("Matrix solved and solution found in %lu seconds\n", end_time.tv_sec-mid_time.tv_sec);
	
	printf("Total time: divisor found in %lu seconds\n", end_time.tv_sec-start_time.tv_sec);
	mpz_clear(n);
	mpz_clear(sr);
	mpz_clear(rem);
	mpz_clear(ideal_a);
	for(i=0; i<s_size; i++)
		mpz_clear(smooth[i]);
	free(td);

	return EXIT_SUCCESS;
}
