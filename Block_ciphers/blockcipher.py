###################### BLOCK CIPHERS ################################
#                       
# Author: CodeBreakers Union --- Andrea Castronovo, Stefano Maggioreni
#
# Description: Python module to collect all functions, classes and object
#              to implement the requested structure
#
######################################################################

## --- Import

# pycryptodome functions import
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util import Counter
# math function import
from math import sqrt

# import modules
import matplotlib.pyplot as plt
import numpy as np
import random

## --- Function
def AES_encrypt(aes_mode, img):
    ''' Function to encrypt a image with `aes_mode` operation. 
        - `aes_mode` (Crypto.Cipher._mode_): instance of AES mode operation
        - `img` (numpy.ndarray): image to encrypt
           -------------------------------------------------
        - return (numpy.ndarray): encrypted image '''
    # encryption of img2bytes
    bytes_mode = aes_mode.encrypt(img.tobytes())
    # bytes2img
    img_mode = np.frombuffer(bytes_mode, dtype=np.uint8)
    
    return img_mode.reshape(img.shape)

def AES_decrypt(aes_mode, img):
    ''' Function to decrypt a image with `aes_mode` operation. 
        - `aes_mode` (Crypto.Cipher._mode_): instance of AES mode operation
        - `img` (numpy.ndarray): image to decrypt
           -------------------------------------------------
        - return (numpy.ndarray): decrypted image '''
    # decryption of img2bytes
    bytes_mode = aes_mode.decrypt(img.tobytes())
    # bytes2img
    img_mode = np.frombuffer(bytes_mode, dtype=np.uint8)
    
    return img_mode.reshape(img.shape)

def grid_plot(imgs,names,gen_title=''):
    ''' Function to plot a images as a grid. 
        - `imgs` ([numpy.ndarray]): list of image to plottable as grid
        - `names` ([str]): list of title for each image
        - optional `gen_title` (str): general title for subplot'''

    # check of grid
    sqrt_len = sqrt(len(imgs))
    if sqrt_len != int(sqrt_len):
        raise ValueError('Number of length is not printable as grid.')
    elif len(names) != len(imgs):
        raise ValueError('Too few names compared to the images ('+ len(imgs) +').')

    # figure
    sqrt_len = int(sqrt_len)
    fig, ax = plt.subplots(sqrt_len, sqrt_len)
    fig.suptitle(gen_title)

    # plot
    index = 0
    for i in range(sqrt_len):
        for j in range(sqrt_len):
            ax[i,j].imshow(imgs[index])
            ax[i,j].set(title=names[index])
            index += 1

    plt.show()

def estimate_pi(tot_points):
    ''' Function to estimates the value of pi-greco using a MonteCarlo simulations,
        by means of drawing of N uniform random coordinates and counting how many of them
        fall into a quarter of circle with uniform radius respect to the total.
        - `tot_points` (int): number of random points
           -------------------------------------------------
        - return (float): pi estimation
        - return (numpy.ndarray): x coordinates of random points
        - return (numpy.ndarray): y coordinates of random points
        - return ([bool]): list of True/False, where True represent the index of 
            points inside circle, False outside points '''
    # x,y points
    x_points = np.random.uniform(0,1,tot_points)
    y_points = np.random.uniform(0,1,tot_points)
    # distance of points
    distance = [sqrt(x**2+y**2) for x,y in zip(x_points, y_points)]
    # pi estimation
    points_inside = [True if i<=1.0 else False for i in distance]
    pi_est = 4*(sum(points_inside)/tot_points)

    return pi_est, x_points, y_points, points_inside

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

def aes_mode(key, mode_str, iv=None):
    ''' Function to instantiate an aes mode operation from string. 
        - `key` (bytes): key for aes
        - `mode_str` ([str]): mode of operation as initials (ECB,CBC,CFB,CTR)
        - `iv` (bytes): initialization vector
           -------------------------------------------------
        - return (Crypto.Cipher._mode): aes_mode instance '''

    # check key
    byt = len(key)
    if byt not in [16,24,32]:
        raise ValueError('\nKey size must be 16, 24 or 32 bytes.')

    # create a dictionary to map the string to the corresponding AES mode
    mode_dict = {
        'ECB': AES.MODE_ECB,
        'CBC': AES.MODE_CBC,
        'CFB': AES.MODE_CFB,
        'CTR': AES.MODE_CTR
    }

    # check iv
    if mode_str.upper() != 'ECB' and len(iv) != 16:
            raise ValueError('\nIV size must be 16 bytes.')

    # use the dictionary to get the correct mode
    try:
        mode = mode_dict[mode_str.upper()]
    except KeyError:
        raise ValueError(f'\n{mode_str} is not valid.')

    if mode in [2,3]:
        # cbc or cfb
        cipher = AES.new(key, mode, IV=iv)
    elif mode == 6:
        # ctr
        # convert the IV to an integer to use as the initial counter value
        ctr_value = int.from_bytes(iv, byteorder='big')
        # Create the counter
        ctr = Counter.new(128, initial_value=ctr_value)
        cipher = AES.new(key, mode, counter=ctr)
    else:
        # ecb
        cipher = AES.new(key, mode)

    return cipher

def compute_HammingDistance(p_bits=128, k_bits=[128], N=1000,\
                            is_conf=True, n=-1, mode='ECB'):
    ''' Function to compute Hamming-Distance for DIFFUSION or
        CONFUSION of AES.MODE_ECB as default or RC4-drop[n] if n>=0. 
        - `p_bits` (int): number of bits for plaintext
        - `k_bits` ([int]): list of numbers of key's bits
        - `N` (int): number of trials
        - `is_diff` (bool): True to compute DIFFUSION
        - `n` (int): number of discarding first bits for RC4
        - `mode` (str): mode of operation as initials (CBC,CFB,CTR)
           -------------------------------------------------
        - return ([][int]): Hamming-Distance for each k_bits and each trials '''

    if n<0:
        # initialization vector
        iv = get_random_bytes(16)
    
    dist = []
    if is_conf:
        # plaintext
        plaintext = get_random_bytes(int(p_bits/8)) 
        
    # MC simulations
    for k in k_bits:
        if not is_conf:
            # generate key
            key = get_random_bytes(int(k/8))
            
        # inner list for each row of distance
        inner_list = []
        # computation
        for _ in range(N):
            # random index and plaintext or key
            if is_conf:
                # key random index
                index = random.randint(0,k-1)
                # normal and modify
                normal = [random.randint(0,1) for _ in range(k)]
                modify = normal[:index] + [1 if normal[index]==0 else 0] + normal[index+1:]
            else:
                # plaintext random index
                index = random.randint(0,p_bits-1)
                # normal and modify
                normal = [random.randint(0,1) for _ in range(p_bits)]
                modify = normal[:index] + [1 if normal[index]==0 else 0] + normal[index+1:]
            # Bool2Bytes
            b_normal = Bool2Bytes(normal)
            b_modify = Bool2Bytes(modify)
            
            # AES or RC4 init and encryptio
            if is_conf:
                if n<0:
                    # AES
                    aes_en = aes_mode(b_normal, mode, iv)
                    m_aes_en = aes_mode(b_modify, mode, iv)
                    # encryption
                    b_ciphertext = aes_en.encrypt(plaintext)
                    b_m_ciphertext = m_aes_en.encrypt(plaintext)
                else:
                    # RC4
                    rc4_drop = RC4(b_normal, drop=n)
                    m_rc4_drop = RC4(b_modify, drop=n)
                    # encryption
                    b_ciphertext = rc4_drop.encrypt(plaintext)
                    b_m_ciphertext = m_rc4_drop.encrypt(plaintext)
            else:
                if n<0:
                    # AES
                    aes_en = aes_mode(key, mode, iv)
                    m_aes_en = aes_mode(key, mode, iv)
                    # encryption
                    b_ciphertext = aes_en.encrypt(b_normal)
                    b_m_ciphertext = m_aes_en.encrypt(b_modify)
                else:
                    # RC4
                    rc4_drop = RC4(key, drop=n)
                    m_rc4_drop = RC4(key, drop=n)
                    # encryption
                    b_ciphertext = rc4_drop.encrypt(b_normal)
                    b_m_ciphertext = m_rc4_drop.encrypt(b_modify)
            # Bytes2Bool
            ciphertext = Bytes2Bool(b_ciphertext)
            m_ciphertext = Bytes2Bool(b_m_ciphertext)
            
            # Hamming distance
            inner_list.append(sum([1 if (p!=np) else 0 for p,np in zip(ciphertext, m_ciphertext)]))
        dist.append(inner_list)
        
    return dist

def plot_histograms(dist, p_bits, k_bits, title):
    ''' Function to plot three histogram. 
        - `dist` ([][int]): Hamming-Distance for each k_bits and each trials
        - `p_bits` (int): number of bits for plaintext
        - `k_bits` ([int]): list of numbers of key's bits
        - `title` (str): Diffusion or Confusion '''

    # subplots
    fig, ax = plt.subplots(1,3,figsize=(11,4))
    # Set common labels
    fig.text(0.075, 0.5, 'Prob. density', ha='center', va='center', rotation='vertical')
    fig.text(0.495, 1.07, f'{title} with {p_bits} plaintext bits', ha='center', va='center', fontsize=14)

    for i,k in enumerate(k_bits):
        # compute mean and standard deviation
        mean = np.mean(dist[i])
        std = np.std(dist[i])
        # plot
        if mean == 1:
            ax[i].hist(dist[i],bins=20, density=True, range=(0.8,1.2))[-1]
        else:
            ax[i].hist(dist[i],bins=80, density=True)[-1]
            ax[i].axvline(p_bits//2, c = 'k', linestyle='dashed', label='p_bits/2')
            ax[i].axvline(mean, c = 'r', linestyle='dashed', label=f'$\mu$ = {np.round(mean,2)}')
            ax[i].axvline(mean - std, c = 'y', linestyle='dashed', label=f'$\sigma$ = {np.round(std,2)}')
            ax[i].axvline(mean + std, c = 'y', linestyle='dashed')
            ax[i].legend()
        
        ax[i].set_title(f'Key length := {k_bits[i]} bits')
        ax[i].set_xlabel('d(y,y\')')
        ax[i].grid()

    plt.show()
    

## --- Classes

class RC4:
    ''' A class representing a Rivest Cipher 4 (or - drop[n]) stream cipher'''

    def __init__(self, key, drop=-1):
        ''' Constructor to initialize an instance of the RC4 class using
            the Key Scheduling Algorithm (KSA) to init P-stream bytes.
            - `key` (bytes): key of stream cipher 
            - optional `drop` (int): number of discarding first bits'''
        
        # check of key
        if not isinstance(key, bytes):
            raise ValueError('key must be Bytes')

        self.__ksa(key)
        self.__i = 0
        self.__j = 0
        if drop > 0:
            for i,_ in enumerate(self):
                if i==drop-1: break

    ### --- public attributes
    @property
    def P(self):
        ''' Getter for public P. 
               -----------------------
            - return (bytes): stream bytes '''
        return bytes(self.__P)
        
    @property
    def i(self):
        ''' Getter for public i.
               -----------------------
            - return (int): 8-bit index pointers '''
        return self.__i
        
    @property
    def j(self):
        ''' Getter for public j.
               -----------------------
            - return (int): 8-bit index pointers '''
        return self.__j
    ### ------

    def __iter__(self): 
        return self

    def __ksa(self, key): 
        ''' Key Sheduling algorithm (KSA) to initialize the `P` stream of bytes
            - `key` (bytes): key of stream cipher '''

        # init
        self.__P = [i for i in range(256)]
        j = 0

        # alog
        for i,p in enumerate(self.__P):
            j = (j + p + key[i%len(key)]) % 256
            self.__P[i],self.__P[j] = self.__P[j],self.__P[i]

    def __prga(self):
        ''' Pseudo-Random Generator Algorithm (PRGA) to iterate state and
            update P stream output bytes
              -------------------------------------
            - return (int): output byte'''
        # algo
        self.__i = (self.i+1) % 256
        self.__j = (self.j + self.__P[self.i]) % 256
        self.__P[self.i],self.__P[self.j] = self.__P[self.j],self.__P[self.i]

        return self.__P[(self.__P[self.i]+self.__P[self.j]) % 256]

    def __next__(self): 
        ''' Iterate the RC4 updating the state
               --------------------------------
            - returns (byte): output byte '''
        
        return self.__prga()

    def encrypt(self, plaintext):
        ''' RC4 encryption
            - plaintext (bytes): sequence to encrypt
              -------------------------------------
            - return (bytes): encrypted sequence '''

        ciphertext = b''
        # encrypt
        for byt_pl, byt_P in zip(plaintext,self):
            # bits
            bits_pl = [bool(int(b)) for b in f'{byt_pl:08b}']
            bits_P = [bool(int(b)) for b in f'{byt_P:08b}']
            # bool2bytes of xor
            cipher = Bool2Bytes([b1 ^ b2 for b1, b2 in zip(bits_pl, bits_P)])
            # ciphertext
            ciphertext += cipher

        return ciphertext

    def decrypt(self, ciphertext):
        ''' RC4 decryption
            - ciphertext (bytes): sequence to decrypt
              -------------------------------------
            - return (bytes): decrypted sequence '''

        plaintext = b''
        # decrypt
        for byt_cl, byt_P in zip(ciphertext,self):
            # bits
            bits_cl = [bool(int(b)) for b in f'{byt_cl:08b}']
            bits_P = [bool(int(b)) for b in f'{byt_P:08b}']
            # bool2bytes of xor
            plain = Bool2Bytes([b1 ^ b2 for b1, b2 in zip(bits_cl, bits_P)])
            # ciphertext
            plaintext += plain

        return plaintext
        