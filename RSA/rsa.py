############################## RSA ###################################
#                       
# Author: CodeBreakers Union --- Andrea Castronovo, Stefano Maggioreni
#
# Description: Python module to collect all functions, classes and object
#              to implement the requested structure
#
######################################################################

## --- Import
# import random function
from random import randint, randrange
# import time to compute execution time
from time import time
# sqrt function
from math import sqrt
    
## --- Function

def EEA(a,m):
    ''' Function which represent Extended Euclidean Algorithm that compute
        the Greatest Common Divisor of two number and also finds
        the coefficients of Bézout’s identity.
        - `a`, `m` (int): input integers
           -------------------------------------------------------------
        - return (int): gcd(a,m)
        - return (int): `s` the Bézout coefficient for a
        - return (int): `t` the Bézout coefficient for m
        
        Note: If gcd(𝑎, 𝑚) = 1 then 𝑠 ≡ 𝑎^(−1) mod m'''

    # init
    r_old, r = int(m), int(a)
    s_old, s = [0, 1]
    t_old, t = [1, 0]

    # algorithm
    while r != 0:
        r_new = r_old % r
        q = (r_old - r_new) // r
        s_new = s_old - q * s
        t_new = t_old - q * t
        # update
        r_old,r = r,r_new
        s_old,s = s,s_new
        t_old,t = t,t_new

    return r_old, s_old, t_old

def SaM(x,e,n):
    ''' Function which represent Square and Multiply Algorithm that compute
        the exponentiation 𝑥^𝑒 mod 𝑛 by means of squaring and multiplication.
        - `x` (int): base
        - `e` (int): exponent
        - `n` (int): modulo
           -------------------------------------------
        - return (int): x^e mod n'''

    # int2bin2list
    e_bin = list(map(int, bin(e)[2:]))[::-1]
    
    # find the maximum index where ei = 1
    L_max = max(i for i, bit in enumerate(e_bin) if bit == 1)

    # algorithm
    y = x
    for i in range(L_max-1,-1,-1):
        y = (y ** 2) % n
        if e_bin[i] == 1:
            y = (y * x) % n

    return y % n # '\n' to add no for loop case

def execution_time(is_SaM, N_test, n_range):
    ''' Function to compute execution time of SaM or basic 
        exponential operation.
        - `is_SaM` (bool): True if SaM algorithm
        - `N_test` (int): number of trials
        - `n_range` (int): max range for operands
           ---------------------------------------------
        - return (float): execution time'''
    # get time
    start_time = time()

    for _ in range(N_test):
        # random
        x = randint(0,n_range) 
        e = randint(1,n_range)
        n = randint(1,n_range)
        if is_SaM:
            # sam
            SaM(x, e, n)
        else:
            # basic
            (x**e)%n
            
    return time() - start_time

def MR(p,N):
    ''' Function which represent Miller-Rabin Primality test.
        - `p` (int): candidate odd prime number greater than 2
        - `N` (int): number of trials
           -------------------------------------------------------------
        - return (bool): probably prime (True) or surely composite (False)'''
    # Ensure p is an odd number greater than 2
    if p % 2 == 0 or p < 3:
        return False
    elif p == 3:
        return True

    # Write p-1 as 2^r * q
    r, q = 0, p - 1
    while q % 2 == 0:
        r += 1
        q //= 2

    step = False
    for _ in range(N):
        x = randint(2, p - 2)
        y = SaM(x, q, p)

        if y != 1 and y != p - 1:
            for _ in range(r):
                y = SaM(y,2,p)
                if y == p - 1:
                    step = True
                    break
            if not step:
                return False
    return True

def is_prime(n):
    ''' Simple primality test.
        - `n` (int): candidate odd prime number greater than 2
           -------------------------------------------------------------
        - return (bool): prime (True) or not (False)'''
    if n < 3 or n % 2 == 0:
        return False
        
    return all(n % i for i in range(3, int(sqrt(n)) + 1, 2))


def prime_probability(L, N, n_MR, n_steps=None):
    ''' Given a length `𝐿` estimate the likelihood for a number to be prime 
       when it is uniformly drawn from the set of odd numbers.
        - `L` (int): length, that must be divisible by 2
        - `N` (int): max numbers of test
        - `n_MR` (int): numbers of trials for MR test
        - optional `n_steps` (int): to estimate prob. at each step within `N`
           -------------------------------------------------------------
        - return (float or [float]): probability, if n_steps present list '''
    
    # check length divisible by 2
    if L%2 != 0: L+=1

    # set n_steps
    if n_steps is None: n_steps = N 

    # bound for group
    lower_bound = int(2**(L//2) + 1)
    upper_bound = int(2**(L//2+1) - 1)

    # compute
    n_prime, prob = 0, []
    for i in range(1,N+1):
        # is drawed p prime?
        if MR(randrange(lower_bound, upper_bound+1, 2),n_MR): n_prime += 1
        # save probability for each steps
        if i%n_steps == 0: prob.append(n_prime/i)

    # return single value or list
    if n_steps == N: return prob[0]
    else: return prob

    

## --- Classes

class RSA:
    ''' A class representing the Rivest-Shamir-Adleman asymmetric
    algorithm for secure communication'''
    
    def __init__(self, length=None, n=None, e=None):
        ''' Constructor to initialize an instance of the RSA class.
            - `length` (int): length of `n` to generate keys 
            - `n`,`e` (int): kpub '''

        if n is not None and e is not None:
            # encryptor
            self.n = n
            self.e = e
            self.__d, self.length = None, None
        elif length is not None:
            # decryptor
            if length%2 != 0:
                # check if length is divisible by 2
                length += 1
            self.length = length
            self.n, self.e, self.__d = self.__keyGenerator()
        else:
            # no input
            raise ValueError('length or kpub arguments must be provided.')

    
    def __keyGenerator(self):
        ''' key public generator for RSA
             ---------------------------------------------
            - return (int, int, int): n,e and d as key'''
        
        # choose two prime numbers (𝑝, 𝑞)
        p, q = self.__find_two_prime_numbers()
        # compute n, m
        n, m = p*q, (p-1)*(q-1)
        # draw e and compute d
        e = randint(2,n-1)
        gcd, d, _ = EEA(e, m)
        i = 0
        while gcd != 1:
            # maintain length
            if e < n-2:
                e += 1
            else:
                e = randint(2,n-1)
            gcd, d, _ = EEA(e, m)
            # no infinite loop
            i += 1
            if i > 100_000_000:
                raise RuntimeError("No end after 100,000,000 iterations for e")
        return n, e, d%m

    def __find_two_prime_numbers(self):
        ''' prime random numbers generator.
               ---------------------------------------------
            - return (int, int): prime numbers'''
        # number of trials for Miller-Rabin test
        N = 100
        length = self.length//2
        # random numbers
        p = randint(2**(length-1), 2**length-1)
        if p%2 == 0: p+= 1
        q = randint(2**(length-1), 2**length-1)
        if q%2 == 0: q+= 1
        # check p-primality
        i = 0
        while MR(p, N) == False:
            # maintain length
            if p < 2**length-2:
                p += 2
            else:
                p = randint(2**(length-1), 2**length-1)
                if p%2 == 0: p+= 1
            # no infinite loop
            i += 1
            if i > 100_000_000:
                raise RuntimeError("No prime number found after 100,000,000 iterations for p")
        # check q-primality
        i = 0
        while MR(q, N) == False:
            # maintain length
            if q < 2**length-2:
                q += 2
            else:
                q = randint(2**(length-1), 2**length-1)
                if p%2 == 0: p+= 1
            # no infinite loop
            i += 1
            if i > 100_000_000:
                raise RuntimeError("No prime number found after 100,000,000 iterations for q")
                
        return p, q
        
    def encrypt(self, plaintext):
        ''' Encrypt method for RSA instance.
        - `plaintext` (bytes): plaintext to encrypt 
           -------------------------------------------------------------
        - return (bytes): ciphertext'''
        int_ciphertext = SaM(int.from_bytes(plaintext,'big'), self.e, self.n)
        return int_ciphertext.to_bytes((int_ciphertext.bit_length() + 7) // 8, 'big')
 
    def decrypt(self , ciphertext):
        ''' Decrypt method for RSA instance.
        - `ciphertext` (bytes): ciphertext to decrypt
           -------------------------------------------------------------
        - return (bytes): plaintext'''
        if self.__d == None:
            raise ValueError('You must initialize key!')

        int_plaintext = SaM(int.from_bytes(ciphertext,'big'), self.__d, self.n)
        return int_plaintext.to_bytes((int_plaintext.bit_length() + 7) // 8, 'big')

    