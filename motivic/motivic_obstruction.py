
# motivic/motivic_obstruction.py
# Skeleton for computing point counts over finite fields for Perm and Det varieties

import itertools
import numpy as np

def count_solutions_mod_p(n, p):
    # Count (Z, gamma, delta) in F_p satisfying g1*F1 + g2*F2 = 1 for trivial g1,g2
    # Here we just count F1=F2=0 solutions as a proxy
    count_perm = 0
    count_det = 0
    for Z_vals in itertools.product(range(p), repeat=n*n):
        Z = np.array(Z_vals).reshape((n, n))
        # Permanent mod p
        perm = sum(np.prod([Z[i, sigma[i]] for i in range(n)]) for sigma in itertools.permutations(range(n))) % p
        det = 0
        for sigma in itertools.permutations(range(n)):
            inv = sum(1 for i in range(n) for j in range(i+1,n) if sigma[i]>sigma[j])
            sign = 1 if inv%2==0 else -1
            det = (det + sign*np.prod([Z[i, sigma[i]] for i in range(n)])) % p
        if perm == 0:
            count_perm += 1
        if det == 0:
            count_det += 1
    return count_perm, count_det

if __name__ == "__main__":
    for n in [2, 3]:
        for p in [2, 3, 5]:
            cp, cd = count_solutions_mod_p(n, p)
            print(f"n={n}, p={p}, #Perm_zero={cp}, #Det_zero={cd}")
