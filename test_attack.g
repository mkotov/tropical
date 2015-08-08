# Implementation of an attack on key exchange protocol using matrices over tropical algebra from 
# Grigoriev, Shpilrain, Tropical cryptography, http://arxiv.org/pdf/1301.1195.pdf.
# 
# Matvei Kotov <mkotov@stevens.edu>, Alexander Ushakov <aushakov@stevens.edu>

Read("attack.g");
Read("test.g");

TestSuite(10, -10^10, 10^10, 10, -10^10, 10^10, ApplyAttack, 100);
