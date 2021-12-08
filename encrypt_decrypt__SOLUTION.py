#!/usr/bin/env python3

##### IMPORTS

import argparse

from collections.abc import Callable

from multiprocessing import Pool
from os import cpu_count

from sys import exit, stdout

from time import time_ns
from typing import Iterator, Mapping, Optional, Union

# add any additional modules you need here
### BEGIN
import hashlib
import numpy as np
from secrets import randbelow, randbits, token_bytes
### END

##### METHODS

def block_idx( block_size:int, offset:int = 0 ) -> Iterator[bytes]:
    """A generator for creating an arbitrary number of block indicies.

       PARAMETERS
       ==========
       block_size: The size of block to use, in bytes. Determines the maximum number 
         of blocks returned, as well.
       offset: The number this generator will start counting from. Defaults to zero.

       YIELDS
       ======
       Successive block indicies.
       """

    mask = (1 << (block_size*8)) - 1 # set an upper limit AND bitmask
    idx  = 0
    while idx <= mask:

        # adding the offset is slower, but the bookkeeping is easier
        yield ( (idx + offset) & mask ).to_bytes( block_size, 'big' )
        idx += 1


def generate_iv( length:int ) -> bytes:
    """Generate an initialization vector for encryption. Must be drawn from a
       cryptographically-secure pseudo-random number generator.

       PARAMETERS
       ==========
       length: The length of the IV desired, in bytes.

       RETURNS
       =======
       A bytes object containing the IV.
       """
    assert type(length) is int

# delete this comment and insert your code here
### BEGIN

    return token_bytes( length )

### END

class Hasher:
    """Encapsulates the hash function used for encryption. This is written as a
       class so that we have easy access to both the hash and hash's block size.

       EXAMPLES:

       > h = Hasher()
       > print( h.digest_size )
       32
       > h.hash( b'test value' )
       b'a byte object 32 characters long'

       """

    def __init__( self ):
        """Create a Hasher. This mostly exists to put the block size in place."""

        # the size of the output of the hash function
        self.digest_size = 32

# Uncomment the following line of code and substitute the hash's ideal input 
#  block size. IMPORTANT: this is almost never the same size as the digest size!

#        self.block_size = ...
### BEGIN
        self.block_size = 64
### END

    def hash( self, data:bytes ) -> bytes:
        """Hash an arbitrary number of bytes into a 32-byte output. Hopefully this is
           done in a cryptographically-secure way.

           PARAMETERS
           ==========
           data: The bytes object to be hashed.

           RETURNS
           =======
           A bytes object containing 32 bytes of hash value.
           """
        assert type(data) is bytes

# delete this comment and insert your code here
### BEGIN

# the easy solution:
#        return hashlib.sha256( data ).digest()

# one hard solution:
# BASE ALGORITHM: ChaCha
# CHANGES: three non-trivial, two trivial.
#  * Most of the original shift constants were divisible by two. I switched to
#     prime values or squares of primes, so there's no common multiples.
#  * The original round consisted of a series of additions, XORs, and shifts
#     that occurred across rows, then down all diagonals. My round ditches
#     the diagonal portion, but compensates by shifting rows diagonally and
#     doing more rounds.
#  * The order of adds/xors has been switched, which might make it easier to pipeline.
#  * The initial state is quite different, it's now all a nothing-up-my-sleeve
#     number instead of a mix of parameters and a NUMS number.
#  * The number of rounds were decreased, partly because there seems to be sufficient
#     security overhead to permit it, but mainly because it speeds up execution.

        # NOTE: the algorithm could be sped-up by pre-mixing this portion
        state = [np.array([0x74686973, 0x20697320, 0x61206e6f, 0x7468696e], dtype=np.uint32),
                 np.array([0x672d7570, 0x2d6d792d, 0x736c6565, 0x7665206e], dtype=np.uint32),
                 np.array([0x756d6265, 0x7220666f, 0x7220696e, 0x69746961], dtype=np.uint32),
                 np.array([0x6c697a69, 0x6e672074, 0x68652073, 0x74617465], dtype=np.uint32) ]

        # extend the data, so we're guaranteed to be block-aligned
        if (len(data) & 0x3f) == 0:
            extended = data
        else:
            extended = data + ( b'\x00' * ( 64 - (len(data) & 0x3f) ) )
        
        # for each 64-byte block of the data
        blocks = len(extended) >> 6
        for idx in range( blocks + 1 ):

            # perform some rounds of state mixing
            for round in range(15):

                state[0] += state[1]
                state[2] += state[3]
                state[1] ^= state[2]
                state[3] ^= state[0]
                state[1] = (state[1] << 25) | (state[1] >> 7)
                state[3] = (state[3] << 13) | (state[3] >> 19)

                state[0] += state[1]
                state[2] += state[3]
                state[1] ^= state[2]
                state[3] ^= state[0]
                state[1] = (state[1] << 16) | (state[1] >> 16)
                state[3] = (state[3] << 9) | (state[3] >> 23)

                # shift values around to increase mixing
                for i in range(1,4):
                    temp = list(state[i][0:-i])
                    state[i][0:i] = state[i][-i:]
                    state[i][i:] = temp

            # ensure we don't merge non-existent data
            if idx == blocks:
                break

            # merge the data with the state
            for i in range(16):
                state[i >> 2][i & 0x3] += (extended[idx*64 + i*4 + 0] << 24) | \
                                          (extended[idx*64 + i*4 + 1] << 16) | \
                                          (extended[idx*64 + i*4 + 2] << 8) | \
                                          (extended[idx*64 + i*4 + 3])

        # consolidate the state down to 32 bytes
        output = [state[0]+state[2], state[1]+state[3]]
        return b''.join( b''.join( int.to_bytes( int(x), 4, 'little' ) for x in output[i] ) for i in [0,1] )


### END

def xor( a:bytes, b:bytes ) -> bytes:
    """Bit-wise exclusive-or two byte sequences. If the two bytes objects differ in
       length, pad with zeros.

       PARAMETERS
       ==========
       a, b: bytes objects to be XORed together.

       RETURNS
       =======
       A bytes object containing the results.
       """
    assert type(a) is bytes
    assert type(b) is bytes

# delete this comment and insert your code here
### BEGIN

    # ensure a is shorter than b
    if len(a) > len(b):
        temp = a
        a = b
        b = temp

    result = bytearray(b)       # take advantage of implicit zero padding
    for i, x in enumerate(a):
        result[i] ^= x          # XOR the matching bytes, ignore the rest
    return bytes(result)        # convert back to an immutable bytes object

    # exercise: can you accomplish this in three lines?

### END

def HMAC( data:bytes, key:bytes, hasher:Hasher ) -> bytes:
    """Perform HMAC with the given hash function. Be sure to read the HMAC spec carefully!

       PARAMETERS
       ==========
       data:   The bytes object to be hashed.
       key:    A bytes object to be used as a key.
       hasher: A Hasher instance.

       RETURNS
       =======
       A bytes object containing the digest.
       """
    assert type(data) is bytes
    assert type(key) is bytes

# delete this comment and insert your code here
### BEGIN

    # if the key is larger than the block size, hash it down
    if len(key) > hasher.block_size:
        key_p = hasher.hash(key)
    else:
        key_p = key

    # set up the padding values (note we're padding to block size, not digest size!)
    ipad = b'\x36' * hasher.block_size
    opad = b'\x5c' * hasher.block_size

    # perform the HMAC hash algorithm with the padded keys
    return hasher.hash( xor(opad,key_p) + hasher.hash( xor(ipad,key_p) + data ) )

### END

def pad( data:bytes, digest_size:int ) -> bytes:
    """Pad out the given bytes object with PKCS7 so it fits within the given 
       digest size. That size is guaranteed to be 255 bytes or less.

       PARAMETERS
       ==========
       data:        The bytes object to be padded.
       digest_size: The output length in bytes is 0 mod digest_size.

       RETURNS
       =======
       A bytes object containing the padded value.
       """
    assert type(data) is bytes
    assert type(digest_size) is int
    assert (digest_size > 1) and (digest_size < 256)

# delete this comment and insert your code here
### BEGIN

    # figure out the value to pad with
    padding = digest_size - (len(data) % digest_size)
    return data + (padding.to_bytes( 1, 'big' ) * padding)

### END

def unpad( data:bytes ) -> Optional[bytes]:
    """Remove PKCS7 from the given bytes object.

       PARAMETERS
       ==========
       data:       The bytes object to have any padding removed.

       RETURNS
       =======
       Either a bytes object containing the original value, or None if 
         no valid padding was found.
       """
    assert type(data) is bytes

# delete this comment and insert your code here
### BEGIN

    padding = data[-1]          # assume the last byte is canonical
    if padding == 0:            # catch the zero case
        return None

    for x in range(padding):    # test the remaining padding bytes agree
        if data[-x-1] != padding:
            return None

    return data[:-padding]      # all good? strip off the padding

### END

def encrypt( iv:bytes, data:bytes, key:bytes, hasher:Hasher, \
        block_ids:Callable[[int], Iterator[bytes]] ) -> bytes:
    """Encrypt the given data, with the given IV and key, using the given hash function.
       Assumes the data has already been padded to align with the digest size. Do not
       prepend the IV. The IV must have the same length as the hash function's block size.

       PARAMETERS
       ==========
       iv:        The initialization vector used to boost semantic security
       data:      The padded data to be encrypted.
       key:       A bytes object to be used as a key.
       hasher:    A Hasher instance.
       block_ids: A generator that generates block indexes of a specific size.
            (see block_idx())

       RETURNS
       =======
       A bytes object containing the encrypted value. Note that the return is not a list or
         generator.
       """
    assert type(iv) is bytes
    assert type(key) is bytes
    assert type(data) is bytes
    assert (len(data) % hasher.digest_size) == 0
    assert len(iv) == hasher.block_size

# delete this comment and insert your code here
### BEGIN

    # set up our generator and output
    generator = block_ids( hasher.block_size )
    output = list()

    # for each block of input
    for i in range( len(data) // hasher.digest_size ):

        randomness = HMAC( xor( next(generator), iv ), key, hasher )
        idx        = i*hasher.digest_size
        plaintext  = data[idx:idx + hasher.digest_size]
        output.append( xor( plaintext, randomness ) )

    return b''.join( output )

    # exercise: compress everything after "generator = ..." into a single line
### END


def pad_encrypt_then_HMAC( plaintext:bytes, key_cypher:bytes, key_HMAC:bytes, hasher:Hasher, \
        block_ids:Callable[[int], Iterator[bytes]] ) -> bytes:
    """Encrypt a plaintext with your encryption function. Note the order of operations!
    
       PARAMETERS
       ==========
       plaintext: The bytes object to be encrypted. Not necessarily padded!
       key_cypher: The bytes object used as a key to encrypt the plaintext.
       key_HMAC: The bytes object used as a key for the keyed-hash MAC.
       hasher: A Hasher instance.
       block_ids: A generator that generates block indexes of a specific size.
            (see block_idx())

       RETURNS
       =======
       The cyphertext, as a bytes object. Note that the return is not a list or
         generator.
       """

    assert type(plaintext) is bytes
    assert type(key_cypher) is bytes
    assert type(key_HMAC) is bytes

# delete this comment and insert your code here
### BEGIN

    # this code's pretty boring and obvious, alas
    iv        = generate_iv( hasher.block_size )
    padded    = pad( plaintext, hasher.digest_size )

    encrypted = encrypt( iv, padded, key_cypher, hasher, block_ids )
    iv_enc    = iv + encrypted
    mac       = HMAC( iv_enc, key_HMAC, hasher )

    return iv_enc + mac

### END

def decrypt_and_verify( cyphertext: bytes, key_cypher: bytes, key_HMAC:bytes, hasher:Hasher, \
        block_ids:Callable[[int], Iterator[bytes]] ) -> Optional[bytes]:
    """Decrypt a plaintext that had been encrypted with the prior function.
       Also performs integrity checking to help ensure the original wasn't
       corrupted.
    
       PARAMETERS
       ==========
       cyphertext: The bytes object to be decrypted
       key_cypher: The bytes object used as a key to decrypt the plaintext.
       key_HMAC: The bytes object used as a key for the keyed-hash MAC.
       hasher: A Hasher instance.
       block_ids: A generator that generates block indexes of a specific size.
            (see block_idx())

       RETURNS
       =======
       If the cyphertext could be decrypted and validates, this returns a bytes 
         object containing the plaintext. Otherwise, it returns None.
       """

    assert type(cyphertext) is bytes
    assert type(key_cypher) is bytes
    assert type(key_HMAC) is bytes

# delete this comment and insert your code here
### BEGIN

    # do a quick sanity check of the length
    if len(cyphertext) < (hasher.block_size + 2*hasher.digest_size):
        return None

    # strip out the MAC and verify it matches
    mac  = cyphertext[-hasher.digest_size:]
    test = HMAC( cyphertext[:-hasher.digest_size], key_HMAC, hasher )

    if test != mac:
        return None

    # next, decrypt the cyphertext
    iv        = cyphertext[:hasher.block_size]
    encrypted = cyphertext[hasher.block_size:-hasher.digest_size]
    padded    = encrypt( iv, encrypted, key_cypher, hasher, block_ids )

    # the return of unpad() matches our return, so just passthrough
    return unpad( padded )

### END


##### MAIN

if __name__ == '__main__':

    # parse the command line args
    cmdline = argparse.ArgumentParser( description="Encrypt or decrypt a file." )

    methods = cmdline.add_argument_group( 'ACTIONS', "The three actions this program can do." )

    methods.add_argument( '--decrypt', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='A file to be decrypted.' )
    methods.add_argument( '--encrypt', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='A file to be encrypted.' )
    methods.add_argument( '--dump', action='store_true', \
        help='Dump a binary stream generated by the hash function to stdout. Handy for testing its quality.' )

    methods = cmdline.add_argument_group( 'OPTIONS', "Modify the defaults used for the above actions." )

    methods.add_argument( '--output', metavar='OUTPUT', type=argparse.FileType('wb', 0), \
        help='The output file. If omitted, print the decrypted plaintext or dump to stdout. The destination\'s contents are wiped, even on error.' )
    methods.add_argument( '--password', metavar='PASSWORD', type=str, default="swordfish", \
        help='The password to use as a key.' )
    methods.add_argument( '--reference', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='If provided, check the output matches what is in this file.' )
    methods.add_argument( '--threads', type=int, default=0, \
        help='Number of threads to use with dump. Numbers < 1 implies all available.' )

    methods.add_argument( '--offset', type=int, default=0, \
        help='An offset into the sequence used during dump.' )

    args = cmdline.parse_args()

    if args.threads < 1:
        args.threads = cpu_count()

    if args.offset < 0:
        args.offset *= -1;

    h = Hasher()

    # which mode are we in?
    if args.decrypt:

        # hash the key to obscure it, then split that into two derived keys
        key       = h.hash( args.password.encode('utf-8') )
        key_enc   = key[:len(key)>>1]
        key_HMAC  = key[len(key)>>1:]

        plaintext = decrypt_and_verify( args.decrypt.read(), key_enc, key_HMAC, h, \
                block_idx )
        args.decrypt.close()

        if plaintext is None:
            print( "ERROR: Could not decrypt the file!" )
            exit( 1 )

        if args.reference:
            ref = args.reference.read()
            if ref != plaintext:
                print( "ERROR: The output and reference did not match!" )
                exit( 2 )

        if args.output:
            args.output.write( plaintext )
            args.output.close()

        else:
            try:
                print( plaintext.decode('utf-8') )
            except UnicodeError as e:
                print( "WARNING: Could not print out the encrypted contents. Was it UTF-8 encoded?" )
                exit( 3 )

    elif args.encrypt:

        key       = h.hash( args.password.encode('utf-8') )
        key_enc   = key[:len(key)>>1]
        key_HMAC  = key[len(key)>>1:]

        cyphertext = pad_encrypt_then_HMAC( args.encrypt.read(), key_enc, key_HMAC, h, \
                block_idx )

        if args.reference:
            ref = args.reference.read()
            if ref != cyphertext:
                print( "ERROR: The output and reference did not match!" )
                exit( 4 )

        if args.output:
            args.output.write( cyphertext )
            args.output.close()

        else:
            print( "As the cyphertext is binary, it will not be printed to stdout." )

    elif args.dump:

        generator = block_idx( h.block_size, args.offset )
        if args.threads > 1:
            with Pool(args.threads) as p:
                for output in p.imap( h.hash, generator, 64 ):
                    if args.output:
                        args.output.write( output )
                    else:
                        stdout.buffer.write( output )
        else:
            for output in map( h.hash, generator ):
                if args.output:
                    args.output.write( output )
                else:
                    stdout.buffer.write( output )

# another approach to do the same:
#        for input in generator:
#                stdout.buffer.write( h.hash(input) )

    else:

        print( "Please select one of encryption, decryption, or dumping." )
