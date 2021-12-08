#!/usr/bin/env python3

##### IMPORTS

import argparse
from sys import exit
from threading import Thread
from time import sleep
from typing import Any, Callable, Iterator, Mapping, Optional, Union # Callable works from here?

# Insert your imports here
### BEGIN

# allow for future_expansion
base_bytes = 64
base_bits  = base_bytes << 3 # same as multiplying by 8
hash_bytes = 32
hash_bits  = hash_bytes << 3
salt_bytes = 16
salt_bits  = salt_bytes << 3

from hashlib import blake2b
def blake2b_256( data ):
    """A helper to make invoking BLAKE2b-256 easier"""
    return blake2b( data, digest_size=hash_bytes ).digest()

from secrets import randbits, token_bytes
import socket
from sympy import gcd, isprime, primefactors, sieve

# sieve speed-up courtesy: Wiener, Michael J. "Safe Prime Generation with a Combined Sieve." IACR Cryptol. ePrint Arch. 2003 (2003): 186.
# create a sieve of values to avoid
sieve.extend_to_no(150)                     # somewhere around here is best for my workstation
prime_list  = list( sieve._list )[2:]
prime_avoid = [(r-1)>>1 for r in prime_list]

### END

##### METHODS

def split_ip_port( string:str ) -> Optional[tuple[str,int]]:
    """Split the given string into an IP address and port number.
    
    PARAMETERS
    ==========
    string: A string of the form IP:PORT.

    RETURNS
    =======
    If successful, a tuple of the form (IP,PORT), where IP is a 
      string and PORT is a number. Otherwise, returns None.
    """

    assert type(string) == str

    try:
        idx = string.index(':')
        return (string[:idx], int(string[idx+1:]))
    except:
        return None

def int_to_bytes( value:int, length:int ) -> bytes:
    """Convert the given integer into a bytes object with the specified
       number of bits. Uses network byte order.

    PARAMETERS
    ==========
    value: An int to be converted.
    length: The number of bytes this number occupies.

    RETURNS
    =======
    A bytes object representing the integer.
    """
    
    assert type(value) == int
    assert length > 0   # not necessary, but we're working with positive numbers only

    return value.to_bytes( length, 'big' )

### BEGIN
def i2b( x, l ):    # reminder: type hints are optional!
    """The above, but it passes through bytes objects."""
    if type(x) == int:
        return x.to_bytes( l, 'big' )
    elif type(x) == bytes:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')
### END

def bytes_to_int( value:bytes ) -> int:
    """Convert the given bytes object into an integer. Uses network
       byte order.

    PARAMETERS
    ==========
    value: An bytes object to be converted.

    RETURNS
    =======
    An integer representing the bytes object.
    """
    
    assert type(value) == bytes
    return int.from_bytes( value, 'big' )

### BEGIN
def b2i( x ):
    """The above, but it passes through int objects."""
    if type(x) == bytes:
        return int.from_bytes( x, 'big' )
    elif type(x) == int:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')
### END

def create_socket( ip:str, port:int, listen:bool=False ) -> Optional[socket.socket]:
    """Create a TCP/IP socket at the specified port, and do the setup
       necessary to turn it into a connecting or receiving socket. Do
       not actually send or receive data here, and do not accept any
       incoming connections!

    PARAMETERS
    ==========
    ip: A string representing the IP address to connect/bind to.
    port: An integer representing the port to connect/bind to.
    listen: A boolean that flags whether or not to set the socket up
       for connecting or receiving.

    RETURNS
    =======
    If successful, a socket object that's been prepared according to 
       the instructions. Otherwise, return None.
    """
    
    assert type(ip) == str
    assert type(port) == int

    # delete this comment and insert your code here
    ### BEGIN
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

    try:
        if listen:
            sock.bind( (ip, port) )
            sock.listen(salt_bytes)
        else:
            sock.connect( (ip, port) )

        return sock
    except:
        return None
    ### END

def send( sock:socket.socket, data:bytes ) -> int:
    """Send the provided data across the given socket. This is a
       'reliable' send, in the sense that the function retries sending
       until either a) all data has been sent, or b) the socket 
       closes.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    data: A bytes object containing the data to send.

    RETURNS
    =======
    The number of bytes sent. If this value is less than len(data),
       the socket is dead plus an unknown amount of the data was transmitted.
    """
    
    assert type(sock) == socket.socket
    assert type(data) == bytes

    # delete this comment and insert your code here
    ### BEGIN
    sent = 0
    while sent < len(data):
        try:
            out = sock.send( data[sent:] )
        except:
            return sent

        if out <= 0:
            return sent
        sent += out

    return sent
    ### END

def receive( sock:socket.socket, length:int ) -> bytes:
    """Receive the provided data across the given socket. This is a
       'reliable' receive, in the sense that the function never returns
       until either a) the specified number of bytes was received, or b) 
       the socket closes. Never returning is an option.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    length: A positive integer representing the number of bytes to receive.

    RETURNS
    =======
    A bytes object containing the received data. If this value is less than 
       length, the socket is dead.
    """
    
    assert type(sock) == socket.socket
    assert length > 0

    # delete this comment and insert your code here
    ### BEGIN
    intake = b''
    while len(intake) < length:

        rem = length - len(intake)
        try:
            input = sock.recv( min(rem,4096) )
        except:
            return intake

        if input == b'':
            return intake
        intake = intake + input

    return intake
    ### END

def safe_prime( bits:int=512 ) -> int:
    """Generate a safe prime that is exactly 'bits' bits long. The result
       should be greater than 1 << (bits-1).

    PARAMETERS
    ==========
    bits: An integer representing the number of bits in the safe prime.
       Must be greater than 1.

    RETURNS
    =======
    An interger matching the spec.
    """

    assert bits > 1

    # delete this comment and insert your code here
    ### BEGIN

    # do a linear search
    maximum = 1 << (bits-1)
    q       = randbits(bits-1) | (1 << (bits-2))      # guarantee the high bit is set
    q      += 5 - (q % 6)                             # make it 5 (mod 6)

    while True:

        # sieve out some known-bad values
        for i,r in enumerate(prime_list):
            if (q % r) == prime_avoid[i]:
                break
        else:
            if isprime( q ):
                cand = (q<<1) + 1
                if isprime( cand ):
                    return cand

        q += 6          # ensure it's always 5 (mod 6)

        if q >= maximum:                # protect against overflow
            q    = (1 << (bits-2)) + 1
            q   += 5 - (q % 6)          # reset this back to where we expect

    ### END

def prim_root( N:Union[int,bytes] ) -> int:
    """Find a primitive root for N, a large safe prime. Hint: it isn't
       always 2.

    PARAMETERS
    ==========
    N: The prime in question. May be an integer or bytes object.

    RETURNS
    =======
    An integer representing the primitive root. Must be a positive
       number greater than 1.
    """

    # delete this comment and insert your code here
    ### BEGIN

    N = b2i(N)

    # IMPORTANT: This assumes N is a safe prime. Will fail for other cases!
    group   = N-1
    fact    = N>>1      # there's only two prime factors of the group, one of which is 2!

    # do a linear search
    c = 1
    while c < group:
        c += 1          # offset this to guarantee incrementing before the "continue"s
        if gcd(N,c) != 1:
            continue
        elif pow( c, fact, N ) == 1:
            continue
#        elif pow( c, 2, N ) == 1:       # no need, because only 1 and N-1 could satisfy this
#            continue                    #  and they're excluded from the search range
        else:
            return c

    ### END


def calc_x( s:bytes, pw:str ) -> int:
    """Calculate the value of x, according to the assignment.

    PARAMETERS
    ==========
    s: The salt to use. A bytes object consisting of 16 bytes.
    pw: The password to use, as a string.

    RETURNS
    =======
    An integer representing x.
    """

    assert type(pw) == str
    assert type(s) == bytes

    # delete this comment and insert your code here
    ### BEGIN

    return bytes_to_int(blake2b_256( s + pw.encode('utf-8') ))

    ### END

def calc_A( g:Union[int,bytes], N:Union[int,bytes], a:Union[int,bytes] ) -> int:
    """Calculate the value of A, according to the assignment.

    PARAMETERS
    ==========
    g: A primitive root of N. Could be an integer or bytes object.
    N: The safe prime. Could be an integer or bytes object.
    a: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing A.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # clean up any incoming values
    g, N, a = map( b2i, [g, N, a] )

    # this also works well:
#    g, N, a = [bytes_to_int(c) if type(c) == bytes else c \
#            for c in [g, N, a]]

    return pow(g, a, N)

    ### END

def calc_B( g:Union[int,bytes], N:Union[int,bytes], b:Union[int,bytes], \
        k:Union[int,bytes], v:Union[int,bytes] ) -> int:
    """Calculate the value of B, according to the assignment.

    PARAMETERS
    ==========
    g: A primitive root of N. Could be an integer or bytes object.
    N: The safe prime. Could be an integer or bytes object.
    b: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    k: The hash of N and g. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing B.
    """

    # delete this comment and insert your code here
    ### BEGIN

    g, N, b, k, v = map( b2i, [g, N, b, k, v] )

    return (k*v + pow(g,b,N)) % N

    ### END

def calc_u( A:Union[int,bytes], B:Union[int,bytes] ) -> int:
    """Calculate the value of u, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing u.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # ints to bytes takes more thought
    A, B = map( lambda x: i2b(x,base_bytes), [A, B] )

    # note that this is already mod N
    return bytes_to_int(blake2b_256( A + B ))

    ### END

def calc_K_client( N:Union[int,bytes], B:Union[int,bytes], \
        k:Union[int,bytes], v:Union[int,bytes], a:Union[int,bytes], \
        u:Union[int,bytes], x:Union[int,bytes] ) -> int:
    """Calculate the value of K_client, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.
    k: The hash of N and g. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.
    a: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    u: The hash of A and B. Could be an integer or bytes object.
    x: See calc_x(). Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing K_client.
    """

    # delete this comment and insert your code here
    ### BEGIN

    N, B, k, v, a, u, x = map( b2i, [N, B, k, v, a, u, x] )

    return pow(B - k*v, a + u*x, N)

    ### END

def calc_K_server( N:Union[int,bytes], A:Union[int,bytes], \
        b:Union[int,bytes], v:Union[int,bytes], u:Union[int,bytes] ) -> int:
    """Calculate the value of K_server, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    A: See calc_A(). Could be an integer or bytes object.
    b: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.
    u: The hash of A and B. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing K_server.
    """

    # delete this comment and insert your code here
    ### BEGIN

    N, A, b, v, u = map( b2i, [N, A, b, v, u] )

    return pow( A*pow(v,u,N), b, N )

    ### END

def find_Y( K_client:Union[int,bytes], bits:Union[int,bytes] ) -> bytes:
    """Find a bytes object Y such that H(K_client||Y) starts with "bits" zero bits.
       See the assignment handout for how those bits should be arranged.

    PARAMETERS
    ==========
    K_client: See calc_K_client(). Could be an integer or bytes object.
    bits: The number of bits that must be zero. Could be an integer or bytes object.

    RETURNS
    =======
    A bytes object representing Y.
    """

    # delete this comment and insert your code here
    ### BEGIN

    K_client = i2b(K_client, base_bytes)
    bits     = b2i( bits )

    # basic idea: we want speed, and incrementing a value is
    #  much quicker than calculating a random value. Byte concatenation
    #  seems slower than to_bytes() in the benchmarks.

    base = bits >> 3                        # how many leading bytes?
    comp = bytes(base)                      # stash this to speed comparisons
    mask = ~((1 << (8 - (bits&7))) - 1)     # mask off the lower endian bits

    idx = 0                                 # start from zero and count up

    while True:
        Y = idx.to_bytes( base_bytes, 'big' )
        hashVal = blake2b_256( K_client + Y )
        if (hashVal[:base] == comp) and ((hashVal[base] & mask) == 0):
            return Y
        idx += 1

    ### END

def calc_M1( A:Union[int,bytes], K_server:Union[int,bytes], Y:Union[int,bytes] ) -> bytes:
    """Calculate the value of M1, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    K_server: See calc_K_server(). Could be an integer or bytes object.
    Y: See find_Y(). Could be an integer or bytes object.

    RETURNS
    =======
    A bytes object representing M1.
    """

    # delete this comment and insert your code here
    ### BEGIN

    K_server, A, Y = map( lambda x: i2b(x,base_bytes), [K_server, A, Y] )

    return blake2b_256( K_server + A + Y )

    ### END

def client_prepare() -> bytes:
    """Do the preparations necessary to connect to the server. Basically,
       just generate a salt.

    RETURNS
    =======
    A bytes object containing a randomly-generated salt, 16 bytes long.
    """

    # delete this comment and insert your code here
    ### BEGIN
    return token_bytes( salt_bytes )

    ### END

def server_prepare() -> tuple[int,int,int]:
    """Do the preparations necessary to accept clients. Generate N and g,
       and compute k.

    RETURNS
    =======
    A tuple of the form (g, N, k), containing those values as integers.
    """

    # delete this comment and insert your code here
    ### BEGIN
    N = safe_prime()
    g = prim_root( N )
    k = calc_u( g, N )      # same thing!

    return (g, N, k)
    ### END

### BEGIN
def close_sock( sock ):
    """A helper to close sockets cleanly."""
    try:
        sock.shutdown(socket.SHUT_RDWR)
        sock.close()
    except:
        pass
    return None

def varprint( data, label, source="Client" ):
    """A helper for printing out data."""
    global args

    if not (('args' in globals()) and args.verbose):
        return

    if label is not None:
        middle = f"{label} = "
    else:
        middle = ""

    if type(data) == bytes:
        print( f"{source}: Received {middle}<{data.hex()}>" )
    else:
        print( f"{source}: {middle}{data}" )

### END
def client_register( ip:str, port:int, username:str, pw:str, s:bytes ) -> \
        Optional[tuple[int,int,int]]:
    """Register the given username with the server, from the client.
       IMPORTANT: don't forget to send 'r'!

    PARAMETERS
    ==========
    ip: The IP address to connect to, as a string.
    port: The port to connect to, as an int.
    username: The username to register, as a string.
    pw: The password, as a string.
    s: The salt, a bytes object 16 bytes long.

    RETURNS
    =======
    If successful, return a tuple of the form (g, N, v), all integers.
       On failure, return None.
    """

    # delete this comment and insert your code here
    ### BEGIN

    varprint( username, "username" )
    varprint( pw, "pw" )
    varprint( s, "salt" )

    # connect to the server
    sock = create_socket( ip, port )
    if sock is None:
        return None

    # send 'r'
    count = send( sock, b'r' )
    if count != 1:
        return close_sock( sock )

    # retrieve N and g
    expected = base_bytes * 2
    g_N = receive( sock, expected )
    if len(g_N) != expected:
        return close_sock( sock )

    g = g_N[:expected>>1]
    N = g_N[expected>>1:]

    varprint( g_N, None )
    varprint( bytes_to_int(N), "N" )
    varprint( bytes_to_int(g), "g" )

    # calculate x and v
    x = calc_x( s, pw ) 
    v = calc_A( g, N, x )

    varprint( x, "x" )
    varprint( v, "v" )

    # send (s, v, username)
    u_enc = username.encode('utf-8')
    assert len(u_enc) < 256

    data = s + int_to_bytes( v, base_bytes ) + int_to_bytes( len(u_enc), 1 ) + u_enc

    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # kill the connection
    close_sock( sock )

    print( "Client: Registration successful." )
    return tuple(map( b2i, [g, N, v] ))

    ### END

def server_register( sock:socket.socket, g:Union[int,bytes], N:Union[int,bytes], \
        database:dict ) -> Optional[dict]:
    """Handle the server's side of the registration. IMPORTANT: reading the
       initial 'r' has been handled for you.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    g: A primitive root of the safe prime. Could be an integer or bytes object.
    N: A safe prime. Could be an integer or bytes object.
    database: A dictionary of all registered users. The keys are usernames
       (as strings!), and the values are tuples of the form (s, v), where s
       is the salt (16 bytes) and v is as per the assignment (integer).

    RETURNS
    =======
    If the registration process was successful, return an updated version of the
       database. If it was not, return None. NOTE: a username that tries to
       re-register with a different salt and/or password is likely malicious,
       and should therefore count as an unsuccessful registration.
    """

    # delete this comment and insert your code here
    ### BEGIN

    varprint( g, 'g', "Server" )
    varprint( N, 'N', "Server" )

    g, N = map( lambda x: i2b(x,base_bytes), [g, N] )

    # send g and N
    data = g + N
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get s, v
    s = receive( sock, salt_bytes )
    if len(s) != salt_bytes:
        return close_sock( sock )
    varprint( s, 'salt', "Server" )
    
    v = receive( sock, base_bytes )
    if len(v) != base_bytes:
        return close_sock( sock )
    varprint( v, 'v', "Server" )
    
    v = bytes_to_int( v )
    varprint( v, 'v', "Server" )

    # get username
    count = receive( sock, 1 )
    if len(count) != 1:
        return close_sock( sock )
    count = bytes_to_int( count )

    varprint( count, 'username_length', "Server" )

    u_enc = receive( sock, count )
    if len(u_enc) != count:
        return close_sock( sock )

    varprint( u_enc, 'u_enc', "Server" )
    try:
        username = u_enc.decode('utf-8')
    except:
        return close_sock( sock )
    varprint( username, 'username', "Server" )

    # were we already registered?
    if username in database:
        temp = database[username]
        if (s != temp[0]) or (v != temp[1]):
            return close_sock( sock )
        else:
            print( "Server: Repeat registration attempted." )

    # all finished with the connection
    close_sock( sock )

    print( "Server: Registration successful." )

    # save them and return
    database[username] = (s, v)
    return database

    ### END

def client_protocol( ip:str, port:int, g:Union[int,bytes], N:Union[int,bytes], \
        username:str, pw:str, s:bytes ) -> Optional[tuple[int,int]]:
    """Register the given username with the server, from the client.
       IMPORTANT: don't forget to send 'p'!

    PARAMETERS
    ==========
    ip: The IP address to connect to, as a string.
    port: The port to connect to, as an int.
    g: A primitive root of the safe prime. Could be an integer or bytes object.
    N: A safe prime. Could be an integer or bytes object.
    username: The username to register, as a string.
    pw: The password, as a string.
    s: The salt, a bytes object 16 bytes long. Must match what the server 
       sends back.

    RETURNS
    =======
    If successful, return a tuple of the form (a, K_client), where both a and 
       K_client are integers. If not, return None.
    """

    # delete this comment and insert your code here
    ### BEGIN

    varprint( N, 'N' )
    varprint( g, 'g' )
    varprint( username, 'username' )
    varprint( pw, 'pw' )
    varprint( s, 's' )

    # conversions!
    g, N = map( b2i, [g, N] )

    # connect to the server
    sock = create_socket( ip, port )
    if sock is None:
        return None

    # send 'p'
    count = send( sock, b'p' )
    if count != 1:
        return close_sock( sock )

    # retrieve N and g
    expected = base_bytes * 2
    g_N = receive( sock, expected )
    if len(g_N) != expected:
        return close_sock( sock )

    # check they match
    if bytes_to_int(g_N[:expected>>1]) != g:
        return close_sock( sock )

    if bytes_to_int(g_N[expected>>1:]) != N:
        return close_sock( sock )

    varprint( g_N[:expected>>1], "g" )
    varprint( g_N[expected>>1:], "N" )

    # calculate k before conversions, as it might be more efficient
    k = calc_u( g, N )      # same action as u! 
    varprint( k, 'k' )

    # calculate x and v
    x = calc_x( s, pw ) 
    v = calc_A( g, N, x )   # same action as A!

    varprint( x, 'x' )
    varprint( v, 'v' )

    # generate a via rejection sampling
    a = randbits( base_bits )
    while a >= N:
        a = randbits( base_bits )
    varprint( a, 'a' )

    # calculate A
    A = calc_A( g, N, a )
    A_bytes = int_to_bytes( A, base_bytes )
    varprint( A, 'A' )

    # send A, username
    u_enc = username.encode('utf-8')
    u_len = int_to_bytes( len(u_enc), 1 )

    data = A_bytes + u_len + u_enc
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get s, B
    expected = salt_bytes + base_bytes
    s_B = receive( sock, expected )
    if len(s_B) != expected:
        return close_sock( sock )
    varprint( s_B, None )

    if s != s_B[:salt_bytes]:
        return close_sock( sock )

    B = bytes_to_int( s_B[salt_bytes:] )
    varprint( B, 'B' )

    # compute u
    u = calc_u( A_bytes, s_B[salt_bytes:] )
    varprint( u, 'u' )

    # compute K_client
    K_client = calc_K_client( N, B, k, v, a, u, x )
    varprint( K_client, 'K_client' )

    # get bits
    bits = receive( sock, 1 )
    if len(bits) != 1:
        return close_sock( sock )

    # find Y
    Y = find_Y( K_client, bits )
    varprint( bytes_to_int(Y), 'Y' )

    # send Y
    count = send( sock, Y )
    if count != len(Y):
        return close_sock( sock )

    # receive M1_server
    M1 = receive( sock, hash_bytes )
    if len(M1) != hash_bytes:
        return close_sock( sock )

    varprint( M1, 'M1' )

    # all done with the connection
    close_sock( sock )

    # doesn't match what we computed? FAILURE
    if M1 != calc_M1( A_bytes, K_client, Y ):
        return None
    else:
        print( "Client: Protocol successful." )
        return ( a, K_client )  # both are ints

    ### END

def server_protocol( sock:socket.socket, g:Union[int,bytes], N:Union[int,bytes], \
        bits:int, database:dict ) -> Optional[tuple[str,int,int]]:
    """Handle the server's side of the consensus protocal. 
       IMPORTANT: reading the initial 'p' has been handled for 
       you.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    g: A primitive root of the safe prime. Could be an integer or bytes object.
    N: A safe prime. Could be an integer or bytes object.
    bits: The number of bits in H(K_server||Y) that must be zero. See the assignment
       handout for details.
    database: A dictionary of all registered users. The keys are usernames
       (as strings!), and the values are tuples of the form (s, v), where s
       is the salt (16 bytes) and v is as per the assignment (integer).

    RETURNS
    =======
    If successful, return a tuple of the form (username, b, K_server), where both b and 
       K_server are integers while username is a string. If not, return None.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # calculate k before conversions, as it might be more efficient
    varprint( N, 'N', "Server" )
    varprint( g, 'g', "Server" )

    k = calc_u( g, N )      # same thing as u! 
    varprint( k, 'k', "Server" )

    # send g and N
    g, N = map( lambda x: i2b(x,base_bytes), [g, N] )
    data = g + N
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get A
    A_bytes = receive( sock, base_bytes )
    if len(A_bytes) != base_bytes:
        return close_sock( sock )
    A = bytes_to_int( A_bytes )
    varprint( A_bytes, None, "Server" )
    varprint( A, 'A', "Server" )

    # get username
    data = receive( sock, 1 )
    if len(data) != 1:
        return close_sock( sock )
    count = bytes_to_int( data )
    varprint( count, 'username_length', "Server" )

    u_enc = receive( sock, count )
    if len(u_enc) != count:
        return close_sock( sock )
    varprint( u_enc, 'u_enc', "Server" )

    try:
        username = u_enc.decode('utf-8')
    except:
        return close_sock( sock )

    varprint( username, 'username', "Server" )

    g, N = map( b2i, [g, N] )

    # retrieve s, v, if possible
    if username in database:
        s, v = database[username]
    else:
        return close_sock( sock )

    # generate b via rejection sampling
    b = randbits( base_bits )
    while b >= N:
        b = randbits( base_bits )
    varprint( b, 'b', "Server" )

    # calculate B
    B = calc_B( g, N, b, k, v )
    B_bytes = int_to_bytes( B, base_bytes )
    varprint( B, 'B', "Server" )

    # send s,B
    data = s + B_bytes
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # compute u
    u = calc_u( A_bytes, B_bytes )
    varprint( u, 'u', "Server" )

    # compute K_server
    K_server = calc_K_server( N, A_bytes, b, v, u )
    varprint( K_server, 'K_server', "Server" )

    # send bits
    count = send( sock, bits.to_bytes(1,'big') )
    if count != 1:
        return close_sock( sock )

    # receive Y
    Y = receive( sock, base_bytes )
    if len(Y) != base_bytes:
        return close_sock( sock )
    varprint( Y, 'Y', "Server" )

    # check Y
    base = bits >> 3        # copy-paste code is worth the increased risk of breakage
    mask = ~((1 << (8 - (bits&7))) - 1)

    hashVal = blake2b_256( i2b(K_server,base_bytes) + Y )
    if (hashVal[:base] != bytes(base)) or ((hashVal[base] & mask) != 0):
        return close_sock( sock )

    # compute M1
    M1 = calc_M1( A, K_server, Y )
    varprint( bytes_to_int(M1), 'M1', "Server" )

    # send M1. Defer error checking until after the socket's closed
    count = send( sock, M1 )
    close_sock( sock )
    if count != len(M1):
        return None
    else:
        print( "Server: Protocol successful." )
        return (username, b, K_server)
    ### END


##### MAIN

if __name__ == '__main__':

    # parse the command line args
    cmdline = argparse.ArgumentParser( description="Test out a secure key exchange algorithm." )

    methods = cmdline.add_argument_group( 'ACTIONS', "The three actions this program can do." )

    methods.add_argument( '--client', action='store_true', \
        help='Perform registration and the protocol on the given IP address and port.' )
    methods.add_argument( '--server', action='store_true', \
        help='Launch the server on the given IP address and port.' )
    methods.add_argument( '--quit', action='store_true', \
        help='Tell the server on the given IP address and port to quit.' )

    methods = cmdline.add_argument_group( 'OPTIONS', "Modify the defaults used for the above actions." )

    methods.add_argument( '--addr', metavar='IP:PORT', type=str, default="127.0.4.18:3180", \
        help='The IP address and port to connect to.' )
    methods.add_argument( '--username', metavar='NAME', type=str, default="admin", \
        help='The username the client sends to the server.' )
    methods.add_argument( '--password', metavar='PASSWORD', type=str, default="swordfish", \
        help='The password the client sends to the server.' )
    methods.add_argument( '--salt', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='A specific salt for the client to use, stored as a file. Randomly generated if not given.' )
    methods.add_argument( '--timeout', metavar='SECONDS', type=int, default=600, \
        help='How long until the program automatically quits. Negative or zero disables this.' )
    methods.add_argument( '--bits', type=int, default=20, \
        help='The number of zero bits to challenge the Client to generate.' )
    methods.add_argument( '-v', '--verbose', action='store_true', \
        help="Be more verbose about what is happening." )

    args = cmdline.parse_args()

    # ensure the number of bits is sane
    if (args.bits < 1) or (args.bits > 64):
        args.bits = 20

    # handle the salt
    if args.salt:
        salt = args.salt.read( 16 )
    else:
        salt = client_prepare()

    if args.verbose:
        print( f"Program: Using salt <{salt.hex()}>" )
    
    # first off, do we have a timeout?
    killer = None           # save this for later
    if args.timeout > 0:

        # define a handler
        def shutdown( time, verbose=False ):

            sleep( time )
            if verbose:
                print( "Program: exiting after timeout.", flush=True )

            return # optional, but I like having an explicit return

        # launch it
        if args.verbose:
            print( "Program: Launching background timeout.", flush=True )
        killer = Thread( target=shutdown, args=(args.timeout,args.verbose) )
        killer.daemon = True
        killer.start()

    # next off, are we launching the server?
    result      = None     # pre-declare this to allow for cascading

    server_proc = None
    if args.server:
        if args.verbose:
            print( "Program: Attempting to launch server.", flush=True )
        result = split_ip_port( args.addr )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Server: Asked to start on IP {IP} and port {port}.", flush=True )
            print( f"Server: Generating N and g, this will take some time.", flush=True )
        g, N, k = server_prepare() 
        if args.verbose:
            print( f"Server: Finished generating N and g.", flush=True )

        # use an inline routine as this doesn't have to be globally visible
        def server_loop( IP, port, g, N, k, bits, verbose=False ):
            
            database = dict()           # for tracking registered users

            sock = create_socket( IP, port, listen=True )
            if sock is None:
                if verbose:
                    print( f"Server: Could not create socket, exiting.", flush=True )
                return

            if verbose:
                print( f"Server: Beginning connection loop.", flush=True )
            while True:

                (client, client_address) = sock.accept()
                if verbose:
                    print( f"Server: Got connection from {client_address}.", flush=True )

                mode = receive( client, 1 )
                if len(mode) != 1:
                    if verbose:
                        print( f"Server: Socket error with client, closing it and waiting for another connection.", flush=True )
                    client.shutdown(socket.SHUT_RDWR)
                    client.close()
                    continue

                if mode == b'q':
                    if verbose:
                        print( f"Server: Asked to quit by client. Shutting down.", flush=True )
                    client.shutdown(socket.SHUT_RDWR)
                    client.close()
                    sock.shutdown(socket.SHUT_RDWR)
                    sock.close()
                    return

                elif mode == b'r':
                    if verbose:
                        print( f"Server: Asked to register by client.", flush=True )

                    temp = server_register( client, g, N, database )
                    if (temp is None) and verbose:
                            print( f"Server: Registration failed, closing socket and waiting for another connection.", flush=True )
                    elif temp is not None:
                        if verbose:
                            print( f"Server: Registration complete, current users: {[x for x in temp]}.", flush=True )
                        database = temp

                elif mode == b'p':
                    if verbose:
                        print( f"Server: Asked to generate shared secret by client.", flush=True )

                    temp = server_protocol( client, g, N, bits, database )
                    if (temp is None) and verbose:
                            print( f"Server: Protocol failed, closing socket and waiting for another connection.", flush=True )
                    elif type(temp) == tuple:
                        if verbose:
                            print( f"Server: Protocol complete, negotiated shared key for {temp[0]}.", flush=True )
                            print( f"Server:  Shared key is {temp[2]}.", flush=True )

                # clean up is done inside the functions
                # loop back

        # launch the server
        if args.verbose:
            print( "Program: Launching server.", flush=True )
        server_proc = Thread( target=server_loop, args=(IP, port, g, N, k, args.bits, args.verbose) )
        server_proc.daemon = True
        server_proc.start()

    # finally, check if we're launching the client
    result      = None     # clean this up

    client_proc = None
    if args.client:
        if args.verbose:
            print( "Program: Attempting to launch client.", flush=True )
        result = split_ip_port( args.addr )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Client: Asked to connect to IP {IP} and port {port}.", flush=True )
        # another inline routine
        def client_routine( IP, port, username, pw, s, verbose=False ):

            if verbose:
                print( f"Client: Beginning registration.", flush=True )

            results = client_register( IP, port, username, pw, s )
            if results is None:
                if verbose:
                    print( f"Client: Registration failed, not attempting the protocol.", flush=True )
                return
            else:
                g, N, v = results
                if verbose:
                    print( f"Client: Registration successful, g = {g}.", flush=True )

            if verbose:
                print( f"Client: Beginning the shared-key protocol.", flush=True )

            results = client_protocol( IP, port, g, N, username, pw, s )
            if results is None:
                if verbose:
                    print( f"Client: Protocol failed.", flush=True )
            else:
                a, K_client = results
                if verbose:
                    print( f"Client: Protocol successful.", flush=True )
                    print( f"Client:  K_client = {K_client}.", flush=True )

            return

        # launch the client
        if args.verbose:
            print( "Program: Launching client.", flush=True )
        client_proc = Thread( target=client_routine, args=(IP, port, args.username, args.password, salt, args.verbose) )
        client_proc.daemon = True
        client_proc.start()

    # finally, the quitting routine
    result      = None     # clean this up

    if args.quit:
        # defer on the killing portion, in case the client is active
        result = split_ip_port( args.addr )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Quit: Asked to connect to IP {IP} and port {port}.", flush=True )
        if client_proc is not None:
            if args.verbose:
                print( f"Quit: Waiting for the client to complete first.", flush=True )
            client_proc.join()

        if args.verbose:
            print( "Quit: Attempting to kill the server.", flush=True )

        # no need for threading here
        sock = create_socket( IP, port )
        if sock is None:
            if args.verbose:
                print( f"Quit: Could not connect to the server to send the kill signal.", flush=True )
        else:
            count = send( sock, b'q' )
            if count != 1:
                if args.verbose:
                    print( f"Quit: Socket error when sending the signal.", flush=True )
            elif args.verbose:
                    print( f"Quit: Signal sent successfully.", flush=True )

            sock.shutdown(socket.SHUT_RDWR)
            sock.close()

    # finally, we wait until we're told to kill ourselves off, or both the client and server are done
    while not ((server_proc is None) and (client_proc is None)):

        if not killer.is_alive():
            if args.verbose:
                print( f"Program: Timeout reached, so exiting.", flush=True )
            if client_proc is not None:
                client_proc.terminate()
            if server_proc is not None:
                server_proc.terminate()
            exit()

        if (client_proc is not None) and (not client_proc.is_alive()):
            if args.verbose:
                print( f"Program: Client terminated.", flush=True )
            client_proc = None
        
        if (server_proc is not None) and (not server_proc.is_alive()):
            if args.verbose:
                print( f"Program: Server terminated.", flush=True )
            server_proc = None
