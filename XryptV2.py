#!/usr/bin/env python3
import os
import sys
import math
import re
import hashlib
import random
import base64
import string
import getpass
import multiprocessing as mp
import csv
import gmpy2
from random import randint
from Crypto.Cipher import AES
from Crypto import Random
from Crypto.Protocol.KDF import PBKDF2
from gmpy2 import mpz, mpfr
from gmpy2 import is_prime as is_prp
from gmpy2 import is_extra_strong_lucas_prp as is_eslprp

def get1prime(keysize):
    while True:
        p = random.randrange(1<<(keysize-(keysize//256)), 1<<((keysize+(keysize//256)+1)))
        if is_prp(p):
            if isprime(p):
                return p

def isprime(n):
    n = mpz(n)
    if not n & 1:  #check if first bit is 1
        return False
    for i in (3,5,7,11):
        if divmod(n, i)[1] == 0:
            return False
   #Fermat
    if (pow(2, n-1, n)) != 1:
       return False
   #MilRab, x**2 = 1 mod P - ERH
    s = 0
    d = n-1
    while not d & 1:
        d>>=1 #dividing by 2^d
        s+=1
    assert(2**s * d == n-1) #Process to find s and d
    def trial_composite(a):
        if pow(a, d, n) == 1:
            return False
        for i in range(s):
            if pow(a, 2**i * d, n) == n-1:
                return False
        return True
    for i in range(10):
        a = random.randrange(2, n-1)
        if trial_composite(a):
            return False
    if is_eslprp(n,1):
        return True
    else:
        return False

def modInverse(a, m) : #Euclid's Extended Algorithm
    m0 = m
    y = 0
    x = 1
    while (a > 1) :
        q = a // m
        t = m
        m = divmod(a,m)[1]
        a = t
        t = y
        y = x - q * y
        x = t
    if (x < 0) :
        x = x + m0
    return x

def divmodp(num, den, p):
    inv = modInverse(den,p)
    return num*inv

def lcm(x, y):
   return (x*y)//math.gcd(x,y)

##AES256CHUNK
def get_private_key(password):
    salt = b"We will know, we must know" #Sort your salts sir
    kdf = PBKDF2(password, salt, 64, 1000)
    key = kdf[:32]
    return key

def encryptaes(raw, password):
    private_key = password
    raw = pad(raw)
    iv = Random.new().read(AES.block_size)
    cipher = AES.new(private_key, AES.MODE_CBC, iv)
    if isinstance(raw, str):  # This checks if 'raw' is a string
        raw = raw.encode('utf-8')
    return base64.b64encode(iv + cipher.encrypt(raw))

def decryptaes(enc, password):
    private_key = password
    enc = base64.b64decode(enc)
    iv = enc[:16]
    cipher = AES.new(private_key, AES.MODE_CBC, iv)
    if isinstance(iv, str):  # This checks if 'iv' is a string
        iv = iv.encode('utf-8')
    return unpad(cipher.decrypt(enc[16:]))


#Padding
BLOCK_SIZE = 64 #Block is 128 no matter what,this is multiple of 16
pad = lambda s: s + (BLOCK_SIZE - len(s) % BLOCK_SIZE) * chr(BLOCK_SIZE - len(s) % BLOCK_SIZE)
unpad = lambda s: s[:-ord(s[len(s) - 1:])]

#RSA
#Unique and Arbitrary Pub E, a prime.
#e = 66047 # because I can
e = 65537

def encryptit(e, n, thestring):#for sigining pass d as e
    thestring = pad(str(thestring)).encode()
    rbinlist = ['{0:08b}'.format(x) for x in thestring]
    catstring = ''
    catstring += rbinlist[0].lstrip('0')
    del rbinlist[0]
    for i in rbinlist:
        catstring += str(i)
    puttynumber = int(catstring,2)
    cypherstring = str(pow(mpz(puttynumber), mpz(e), mpz(n)))
    return cypherstring

def decryptit(d, n, cynum):#for signing pass e as d
    decryptmsg = ''
    n = int(n)
    d = int(d)
    puttynum = pow(mpz(int(cynum)), mpz(d), mpz(n))
    puttynum = '{0:08b}'.format(puttynum)
    while True:
        if len(puttynum)%8 == 0:
            break
        puttynum = '0{0}'.format(puttynum)
    locs = re.findall('[01]{8}', puttynum)
    for x in locs:
        letter = chr(int(x,2))
        decryptmsg += letter
    return unpad(decryptmsg)[2:-1]

def primegenerator(keysize):
    while True:
        primes = []
        plist = []
        for i in range(mp.cpu_count()):
            plist.append(keysize)
        workpool = mp.Pool(processes=mp.cpu_count())
        reslist = workpool.imap_unordered(get1prime, plist)
        workpool.close()
        for res in reslist:
            if res:
                primes.append(res)
                workpool.terminate()
                break
        workpool.join()
        #
        workpool1 = mp.Pool(processes=mp.cpu_count())
        reslist = workpool1.imap_unordered(get1prime, plist)
        workpool1.close()
        for res in reslist:
            if res:
                primes.append(res)
                workpool1.terminate()
                break
        workpool1.join()
        return primes

def laGrange(pts):
    gmpy2.get_context().precision=1000
    evalpoint = mpz(''.join([str(ord(x)) for x in input('Input public passphrase: ')]))
    p = 2**521 - 1
    npts = [list(i) for i in pts]
    terms =[]
    for mx, y in zip(npts[0], npts[1]):
        num,den = mpz(y%p),mpz(1)
        for x in pts[0]:
            if pts[0].index(x) != pts[1].index(y):
                num *= (evalpoint - x)
                den *= (mx - x)
        terms.append(divmodp(num,den,p))
    return (sum(terms)+p)%p

def genpoints():
    x,y,pts,collection = [],[],[],[]
    N = int(input('How many shares?: '))
    rng = 2**256
    for xy in range(N):
        x.append(randint(-rng, rng))
        y.append(randint(-rng, rng))
    pts.append(x)
    pts.append(y)
    for x,y in zip(pts[0],pts[1]):
        collection.append([x,y])
    with open(input('File to write shares: '), 'w+') as f1:
        for xy in collection:
            f1.write(str(xy[0])+',')
            f1.write(str(xy[1])+'\n')
    return pts

def collpoints():
    with open(input('Enter share file: '), 'r') as f1:
        pts = list(csv.reader(f1, delimiter=","))
    terms, x, y = [],[],[]
    for xy in pts:
        x.append(int(xy[0]))
        y.append(int(xy[1]))
    terms.append(x)
    terms.append(y)
    return terms

#Begin User Flow
while True:
    choice = input("""
    
    ▒██   ██▒██▀███▓██   ██▓██▓███ ▄▄▄█████▓
    ▒▒ █ █ ▒▓██ ▒ ██▒██  ██▓██░  ██▓  ██▒ ▓▒
    ░░  █   ▓██ ░▄█ ▒▒██ ██▓██░ ██▓▒ ▓██░ ▒░
     ░ █ █ ▒▒██▀▀█▄  ░ ▐██▓▒██▄█▓▒ ░ ▓██▓ ░
    ▒██▒ ▒██░██▓ ▒██▒░ ██▒▓▒██▒ ░  ░ ▒██▒ ░
    ▒▒ ░ ░▓ ░ ▒▓ ░▒▓░ ██▒▒▒▒▓▒░ ░  ░ ▒ ░░
    ░░   ░▒ ░ ░▒ ░ ▒▓██ ░▒░░▒ ░        ░
     ░    ░   ░░   ░▒ ▒ ░░ ░░        ░
     ░    ░    ░    ░ ░
                    ░ ░
    
    Dan's Cryptography Program.
    "For when you need to send stolen nuclear codes to warlords"
    Generate Public/Private RSA keys 
    Encrypt/Decrypt/Sign Data with RSA and AES
    Create and process distributed secret keys
    
    Choose:
    A: Generate New Public/Private Key Pair
    B: Encrypt a File RSA/AES/DSA
    C: Decrypt a File RSA/AES/DSA
    D: Generate Distributable Shares
    E: Generate Distributable Shares and Convert Phrase to a Secret
    F: Process Shares and Convert Phrase to a Secret
    G: Quit
    => """)
    
    if choice == 'A' or choice == 'a':
        try:
            keysize = (int(input("Desired Keysize:  "))>>1)
        except ValueError as a:
            print('Enter a number\n\n')
            sys.exit()
        pubkeyname = input('Input desired public key name: ')
        pkey = input('Input desired private key name: ')
        pwkey = get_private_key(getpass.getpass(prompt='Password to protect your private key: ', stream=None))
        print('Generating Keys...')
        primes = primegenerator(keysize)
        if primes[0] != primes[1]:
            p, q = primes[0], primes[1]
        else:
            print('God hates you')
            exit()
        n = p*q
        cm = lcm(p-1, q-1)
        print('Computing Private key ...')
        d = modInverse(e, cm)
        print('Private Key Size: {} bits'.format(keysize*2))
        print('Functional Length of: {}'.format(len(bin((d)))))
        keystring = encryptaes(str(d).encode('ascii', errors='ignore').decode('utf8'),pwkey)
        b64key = bytes.decode(base64.encodebytes(bytes(str(hex(n)).encode())))
        with open(pkey, 'w') as f1:
            f1.write(str(n)+'\n')
            f1.write(bytes.decode(keystring))
        with open(pubkeyname, 'w') as f2:
            f2.write(b64key)
        print('Complete - {} and {} generated'.format(pubkeyname,pkey))
        print('e exponent: {}'.format(str(e)))
        print("""
    -----BEGIN PUBLIC KEY-----
    {}-----END PUBLIC KEY-----
    """.format(b64key))
        b64privkey = b64key = bytes.decode(base64.encodebytes(bytes(str(hex(d)).encode())))
        print("""
    -----BEGIN PRIVATE KEY-----
    {}-----END PRIVATE KEY-----
    """.format(b64privkey))
    
    if choice == 'B' or choice == 'b':
        lineoutholder = []
        pubkeyname = input('Enter recipients public key: ')
        while not os.path.exists(pubkeyname):
            print('No such file')
            pubkeyname = input('Enter recipients public key: ')
        with open(pubkeyname, 'r') as f1:
            pubkey = f1.read()
        privkey = input('Enter your private key: ')
        while not os.path.exists(privkey):
            print('No such file')
            privkey = input('Enter your private key: ')
        pwkey = get_private_key(getpass.getpass(prompt='Password for your private key: ', stream=None))
        uhaeskey = ''.join([random.choice(string.ascii_letters + string.digits) for n in range(32)])
        n = int(bytes.decode(base64.decodebytes(bytes(pubkey.encode()))), 16)
        workfile = input('Enter the file to ENCRYPT: ')
        outfile = input('Enter filename to WRITE out: ')
        sha256_hash = hashlib.sha256()
        try:
            with open(workfile, 'rb') as f2:
                wholefile = f2.read()
            with open(workfile, 'rb') as f2:#open again to clear memory
                for byte_block in iter(lambda: f2.read(4096),b""):
                    sha256_hash.update(byte_block)
            HASH = sha256_hash.hexdigest()
            with open(privkey) as f3:
                priv = f3.readlines()
        except Exception as x:
            print(x)
            exit()
        try:
            d = int(bytes.decode(decryptaes(priv[1], pwkey)))
        except:
            print('Bad PassWord!')
            exit()
        HASH = [ord(i) for i in HASH]
        numhash = ''
        for i in HASH:
            numhash +=str(i)
        signature = pow(int(numhash), d, int(priv[0]))
        aeskey = get_private_key(uhaeskey)
        plaintext = base64.encodebytes(wholefile)
        cyphertext = bytes.decode(encryptaes(plaintext.decode('ascii'), aeskey))
        shippedpw = encryptit(e, n, uhaeskey.encode())
        concat = str(str(signature)+'CUTcutCUTcutCUT'+shippedpw+'CUTcutCUTcutCUT'+cyphertext)
        with open(outfile, 'w') as f3:
            f3.write(concat)
        print('Wrote to {} ...'.format(outfile))
    
    if choice == 'C' or choice == 'c':
        dspubkeyname = input('Enter senders public key: ')
        while not os.path.exists(dspubkeyname):
            print('No such file')
            dspubkeyname = input('Enter senders public key: ')
        with open(dspubkeyname, 'r') as f1:
            pubkey = f1.read()
        nsig = int(bytes.decode(base64.decodebytes(bytes(pubkey.encode()))), 16)
        privkey = input('Enter your private key: ')
        while not os.path.exists(privkey):
            print('No such file')
            privkey = input('Enter your private key: ')
        pwkey = get_private_key(getpass.getpass(prompt='Password for your private key: ', stream=None))
        workfile = input('Enter the file to decrypt: ')
        outfile = input('Enter the filename to write out: ')
        print('DECRYPTING')
        sha256_hash = hashlib.sha256()
        try:
            with open(workfile) as f1:
                lineholder = f1.read().split('CUTcutCUTcutCUT')
            signature, codedkey, cyphertext =lineholder[0], lineholder[1], lineholder[2]
        except:
            print('Bad file name or path')
            exit()
        with open(privkey) as f2:
            priv = f2.readlines()
        n = priv[0]
        try:
            d = int(bytes.decode(decryptaes(priv[1], pwkey)))
        except:
            print('Bad Password!')
            exit()
        sigdec = pow(int(signature), e, nsig)
        aeskey = decryptit(d, n, codedkey)
        aeskey = get_private_key(aeskey)
        decstr = bytes.decode(decryptaes(cyphertext, aeskey))
        cleartext = base64.decodebytes(bytes(decstr, 'ascii'))
        with open(outfile, 'wb') as f1:
            f1.write(cleartext)
        with open(outfile, 'rb') as f2:
            for byte_block in iter(lambda: f2.read(4096),b""):
                sha256_hash.update(byte_block)
            HASH = sha256_hash.hexdigest()
        HASH = [ord(i) for i in HASH]
        numhash = ''
        for i in HASH:
            numhash +=str(i)
        if int(numhash) == int(sigdec):
            print('Signature Verified')
        else:
            print('FAILURE, bad hash...')
        print('Wrote out to {} '.format(outfile))
    
    if choice == 'D' or choice == 'd':
        genpoints()
    
    if choice == 'E' or choice == 'e':
        genpoints()
        print('Secret Key: ' , ''.join(x for x in str(laGrange(collpoints())) if x!='.' and x!='-'))
        
    if choice == 'F' or choice == 'f':
        print('Secret Key: ' , ''.join(x for x in str(laGrange(collpoints())) if x!='.' and x!='-'))
    
    if choice == 'G' or choice == 'g':
        print("Exiting the program. Bye!")
        break
