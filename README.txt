CPSC 418 Assignment 3
Kell Larson 30056026
Alexandria Little (ID HERE)

Files Submitted:
- vaccine_passport.py

Implemented:
- RSA.modulus()
- RSA.keypair()
- RSA.sign()
- RSA.verify()
- RSA.encrypt()
- RSA.decrypt()
- encode_name()
- gen_plaintext()
- pseudoKMAC()
- interleave_data()
- encrypt_data()
- decrypt_data()
- create_passport()
- verify_passport()

Partially Implemented:
- request_passport()
	    - Cannot generate a valid Y, unsure why.
	    - Rest of the code should be OK, but cannot verify.
- retrieve_passport()
	    - Unable to check if Y is correct, keeps stating Y is not valid even though after computing M1
	        and the gradescope client declare it as valid.
	    - QR data generation not sending data, but appears to be generating the data correctly.

Known Bugs:
- See Partially Implemented

I worked with (Kell/Alexandria) on my answers.
