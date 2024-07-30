###################### STREAM CIPHERS ################################
#                       
# Author: CodeBreakers Union --- Andrea Castronovo, Stefano Maggioreni
#
# Description: Python module to collect all functions, classes and object
#              to implement the requested structure
#
######################################################################

## --- Import

from functools import reduce
from operator import xor
from math import sqrt
from scipy.special import erfc
from scipy.special import gammaincc as Q

## --- Function

def poly_int2str(poly):
    ''' Function to express polynomial as string of variables. 
        - `poly` ([int]): polynomial coeff, from Pm to P0
           -------------------------------------------------
        - return (str): string of polynomial expression '''
    # init
    Px = ''
    # max degree of poly
    m = 0
    # length of LFSR with that poly
    length = len(poly)-1
    # compute string
    for i,p in enumerate(poly):
        if i<length:
            # from Pm to P1
            if p == 1:
                # Pi == 1
                power = length - i
                if m<power: 
                    # max degree
                    m = power
                Px += f'x^{power} + '
        else:
            # + P0, must be 1
            Px += f'{p}'

    return Px
    

def Bytes2Bool(Byt, length=-1):
    ''' Function to transform bytes into boolean. 
        - `Byt` (bytes): bytes sequence to transform
        - optional `length` (int): length of MSBs to keep ---> default all
           -------------------------------------------------
        - return ([bool]): bool of bit's bytes of length "length" '''

    # boolean bits
    bools = []
    for byte in Byt:
        bools += [bool(int(bit)) for bit in f'{byte:08b}']

    if length > 0:
        # check if MSBs of length is all 0
        if not any(bools[:length]):
            raise ValueError(f'Invalid `state`: MSB all 0 for length {length}')
        # keep only 0:length bits
        bools = bools[:length]
        
    return bools

def Bool2Bytes(bools):
    ''' Function to transform boolean of any length into bytes
        reaching out the nearest upper bytes. 
        - `bools` ([bool]): bool of bit's bytes
           -------------------------------------------------
        - return (bytes): bytes sequence '''
    # filling with 0s to reach out the nearest byte
    extended_bools = bools + [False for i in range((8 - (len(bools)%8))%8)]
    # bool2str
    bools_str = ''.join(['1' if i else '0' for i in extended_bools])
    # str2int2bytes
    byt = int(bools_str,2).to_bytes(len(bools_str)//8, byteorder='big')

    return byt

def compute_poly(poly, quotient, r):
    ''' Function to compute {P(x) = P(x) + Q(x)*x^r} for Berlekamp
        Massey algorithm
        - `poly` ([int]): P(x) ascending order
        - `quotient` ([int]): Q(x) ascending order
        - `r` (int): number of time-steps
           -------------------------------------------------
        - return ([int]): new feedback polynomial P(x) in ascending order '''
    # compute Q(x) * x^r
    quotient_times_xr = [0]*r + quotient
    # same length for Q(x) and P(x)
    gap = len(quotient_times_xr) - len(poly)
    if gap>0:
        poly += [0]*gap
    elif gap<0:
        quotient_times_xr += [0]*(-gap)
    # compute P(x) + Q(x)*x^r
    poly = [p^qx for p,qx in zip(poly, quotient_times_xr)]

    return poly

def berlekamp_massey(b):
    ''' Berlekamp-Massey algorithm to find the shortest LFSR for
        a given binary sequence.
        - `b` ([bool]): sequence of bit
           -------------------------------------------------
        - return ([int]): shortest feedback polynomial P(x) 
                                coefficients from Pm to P0
        - return (int): linear complexity '''

    # init
    poly = [1]     # poly explaining the bit sequence up to the last bit
    quotient = [1] # last poly of the explored P(x)
    R = []         # temporary variable
    m = 0          # max degree of the explored P(x)
    r = 1          # num of time steps with Q(x) that has discrepancy equal to 1
    discr = 0      # discrepancy

    # # debug printing
    # branch = ' '
    # spacing = '{:1} {:1} {:1} {:1} {:^20} {:1} {:^20} {:1}'
    # print(spacing.format('t', 'b', 'd', ' ', 'P(x)', 'm', 'Q(x)', 'r'))
    # print('------------------------------------------------------')
    # print(spacing.format('-', '-', '-', branch, str(poly), str(m), str(quotient), str(r)))
    
    for t in range(len(b)):
        # compute discrepancy
        discr = reduce(xor,[poly[j]&b[t-j] for j in range(m+1)])

        if discr == 1:
            if 2*m <= t:
                # # debug printing
                # branch = 'A'
                R = poly.copy()
                poly = compute_poly(poly, quotient, r)
                quotient = R.copy()
                m = t - m + 1
                r = 0
            else:
                # # debug printing
                # branch = 'B'
                poly = compute_poly(poly, quotient, r)
        r += 1
        
        # # debug printing
        # print(spacing.format(str(t), str(b[t]), str(discr), branch, str(poly),\
        #                      str(m), str(quotient), str(r)))
        # branch = ' '

    return poly[::-1],m

def frequency_test(b):
    ''' Frequency (Monobit) statistical test to determine whether 
    the number of ones and zeros in a sequence are approximately the same 
    as would be expected for a truly random sequence. 
    
    Reccomendation: n=sequence length > 100
    
        - `b` ([bool]): sequence of bit to test
           -------------------------------------------------
        - return (bool): test Pass (True) or Fail (False) '''

    # verify recomemndation
    n = len(b)
    if n < 101:
        print('Warning: length', n, 'of bits sequence ' \
        'less than recommendation (100)')

    # compute statistic
    pi = sum([bit for bit in b])/n
    s = 2*sqrt(n)*abs(pi-0.5)

    # compute p-value
    p = erfc(s/sqrt(2))

    # compare
    alpha = 0.01

    if p > alpha:
        return True
    else:
        return False
        
def block_frequency_test(b,M):
    ''' Frequency statistical test within a Block to determine whether 
    the frequency of ones in an 𝑀-bit block of a sequence is approximately M/2. 

    With n = sequence length and N = n/M
    𝑛 > 100, 𝑀 ≥ 20, 𝑀 < 𝑛/100, N < 100 are recommended.
    
        - `b` ([bool]): sequence of bit to test
        - `M` (int): number of bits per blocks
           -------------------------------------------------
        - return (bool): test Pass (True) or Fail (False) '''

    # verify block size
    n = len(b)
    if M == 1:
        print('With 1-bit block you mean Monobit test!')
        return frequency_test(b)
    n = len(b)
    try:
        N = n//M # seq partion of non-overlapping blocks, discard unused bit
    except ZeroDivisionError:
        raise ZeroDivionError('M must be greater than 0!')
        
    # verify recommendation
    if n<101 or M<20 or M<n/100 or N<100:
        print('Warning: take care recommendations!')

    # compute statistic
    qi2 = 0
    for i in range(N):
        summ = 0
        for j in range(M):
            summ += int(b[i*M+j])

        pi = summ/M
        qi2 += (pi-0.5)**2
    qi2 = 4*M*qi2

    # compute p-value
    p = Q(N/2,qi2/2)

    # compare
    alpha = 0.01

    if p > alpha:
        return True
    else:
        return False

def runs_test(b):
    ''' Runs statistical test to determine whether the number of runs of 
    ones and zeros in a sequence is as expected. A run of length 𝑘 is a sequence of 𝑘
    identical bits bounded before and after with a bit of the opposite value.

    Reccomendation: n=sequence length > 100
    
        - `b` ([bool]): sequence of bit to test
           -------------------------------------------------
        - return (bool): test Pass (True) or Fail (False) '''

    n = len(b)

    # frequency (monobit) test
    if not frequency_test(b):
        return False

    # compute statistic
    rt = [not(b[t]^b[t+1]) for t in range(n-1)]
    v = (1+sum(rt))/(2*n)

    # compute p-value
    pi = sum([bit for bit in b])/n
    numer = abs(v-pi*(1-pi))
    denom = (pi*(1-pi))*sqrt(2)
    p = erfc(numer/denom)
    
    # compare
    alpha = 0.01

    if p > alpha:
        return True
    else:
        return False
    


## --- Classes

class LFSR:
    ''' A class representing a Linear Feedback Shift Register '''

    def __init__(self, poly, state=None):
        ''' Constructor to initialize an instance of the LFSR class.
            - `poly` ([int])  degrees of the non-zero coefficients 
            - optional `state` (bytes) initial state of the LFSR ---> default all bits 1 '''
        # polynomial's degree
        self.__length = max(poly)
        # create polynomial's P(x) coefficients list, from P0 to Pm
        self.__poly = [int(i in sorted(poly)) for i in range(0,self.length+1)]
        # set state
        if state == None:
            # set default
            state = [True if i<self.__length else False \
                            for i in range(((self.__length+7)//8)*8)]
        else:
            state = Bytes2Bool(state, self.__length)
        self.__state = state[:self.__length]
        # update LFSR
        self.__update()

    ### --- public attributes
    @property
    def length(self):
        ''' Getter for public length. 
               -----------------------
            - return (int): LFSR's length or polynomial degree '''
        return self.__length
        
    @property
    def poly(self):
        ''' Getter for public poly.
               -----------------------
            - return ([int]): LFSR's polynomial coeff, from Pm to P0'''
        return self.__poly[::-1]
        
    @property
    def output(self):
        ''' Getter for public output.
               -----------------------
            - return (bool): LFSR's output bit '''
        return self.__output

    @property
    def feedback(self):
        ''' Getter for public feedback. 
               -----------------------
            - return (bool): LFSR's last feedback bit '''
        return self.__feedback
        
    @property
    def state(self):
        ''' Getter for public state.
               -----------------------
            - return (bytes): LFSR's state '''
        return Bool2Bytes(self.__state)

    @state.setter
    def state(self, state):
        ''' Setter for public state.
            - `state` (bytes): LFSR's state '''
        self.__state = Bytes2Bool(state, self.__length)
        self.__update()
    
    ### ------
                
    def __iter__(self): 
        return self
        
    def __next__(self): 
        ''' Shift the registers updating LFSR state
               --------------------------------
            - returns (bool): output bit '''
        # shift value of registers
        self.__state.insert(0, self.__feedback)
        self.__state.pop()
        # update LFRS
        self.__update()
        
        return self.__output
 
    def run_steps(self, N=1): 
        ''' Execute `N` LFSR steps.
            - optional `N` (int): number of steps to execute ---> default at 1
                -----------------------
            - return ([bool]): list of output bit of each steps'''
        return [next(self) for _ in range(N)]

    def cycle(self, state=None): 
        ''' Compute a complete cycle of LFSR.
            - optional `state` (bytes) initial state 
                        of the LFSR ---> actual state as default
                -----------------------
            - return ([bool]): representing the output bits in 
                        the LFSR cycle, from actual to same again ''' 
        if state != None:
            # set state
            state = Bytes2Bool(state, self.__length)
            self.__state = state.copy()
            # update LFSR
            self.__update()
        else:
            # use actual state
            state = self.__state.copy()
        # initialize list of bool
        list_of_bool = [self.__output]
        # call of __next__ and save each output bit
        for i,b in enumerate(self):
            list_of_bool += [b]
            # Max iteration or cycle
            if self.__state == state: 
                break
            elif (i+1)==2**self.__length:
                print('Pay attention: maximum iteration reached without cycle!')
                break
                
        return list_of_bool

    
    def __update(self):
        ''' Update LFSR computing output and last feedback bit '''
        # output bit
        self.__output = self.__state[self.__length-1]
        # last feedback bit
        self.__feedback = reduce(xor, [bool(p*s) for p,s in \
                                       zip(self.__poly[1:], self.__state)])

    def __str__(self):
        ''' String method to describe the LFSR class instance '''

        # str to print
        spacing = '{:^8} {:^20} {:^20} {:^3} {:^3}'
        str_to_print = spacing.format('degree', 'P(x)', 'state', 'b', 'fd')
        str_to_print += '\n----------------------------------------------------------\n'

        # compute expression
        str_poly = poly_int2str(self.poly)
        int_state = ''.join([str(int(B)) for B in \
                     Bytes2Bool(self.state,self.length)])
        str_state = f'{self.state} -> 0b{int_state}'

        # str to print
        str_to_print += spacing.format(self.length, str_poly, \
                     str_state, self.output, self.feedback)

                
        return str_to_print

class ShrinkingGenerator:
    ''' A class representing a Shrinking generator '''
    # algorithm implementation
    def __init__(self, polyA=None, polyS=None, stateA=None, stateS=None):
        ''' Constructor to initialize an instance of the Shrinking generator class.
            - optional `polyA` ([int])  degrees of the non-zero 
                        coefficients of lfsrA ---> default [5, 2, 0]
            - optional `polyA` ([int])  degrees of the non-zero 
                        coefficients of lfsrS ---> default [3, 1, 0]
            - optional `stateA` (bytes) initial state 
                        of the lfsrA ---> default all bits 1
            - optional `stateS` (bytes) initial state 
                        of the lfsrS ---> default all bits 1 '''

        # default polynomials
        if polyA == None:
            polyA = [5,2,0]
        if polyS == None:
            polyS = [3,1,0]

        # lfsrs attributes
        self.__lfsrA = LFSR(polyA, stateA)
        self.__lfsrS = LFSR(polyS, stateS)
        # find a producible output bit
        while not self.lfsrS.output:
            # lfsrs step
            next(self.__lfsrA)
            next(self.__lfsrS)

        # output attributes
        self.__output = self.lfsrA.output

    ### --- public attributes
    @property
    def lfsrA(self):
        ''' Getter for public lfsrA. 
               -----------------------
            - return (LFSR): LFSR A '''
        return self.__lfsrA

    @property
    def lfsrS(self):
        ''' Getter for public lfsrS. 
               -----------------------
            - return (LFSR): LFSR S '''
        return self.__lfsrS

    @property
    def output(self):
        ''' Getter for public output. 
               -----------------------
            - return (bool): output '''
        return self.__output

    ### ---

    def __iter__(self):
        return self

    def __next__(self):
        ''' Find a new producible output bit
               --------------------------------
            - returns (bool): output bit '''
        # lfsrs step
        next(self.__lfsrA)
        next(self.__lfsrS)

        # find output
        while not self.lfsrS.output:
            next(self.__lfsrA)
            next(self.__lfsrS)

        # output attributes
        self.__output = self.lfsrA.output
        
        return self.__output


class SelfShrinkingGenerator:
    ''' class docstring '''
    # algorithm implementation
    def __init__(self, poly=None, selection_bit=None, state=None):
        ''' init docstring '''
        self.lfsr = ...
        sefl.sbit = ...
        self.output = ...

    def __iter__(self):
        return self

    def __next__(self):
        ''' next docstring '''
        ...
        return self.output
        