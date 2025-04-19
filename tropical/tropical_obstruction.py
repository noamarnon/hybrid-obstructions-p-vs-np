
# tropical/tropical_obstruction.py
# Skeleton for computing tropical permanent and determinant valuations

import itertools
import numpy as np

def tropical_perm(matrix):
    # Tropical permanent: min over permutations of sum of entries
    n = matrix.shape[0]
    vals = []
    for sigma in itertools.permutations(range(n)):
        vals.append(sum(matrix[i, sigma[i]] for i in range(n)))
    return min(vals)

def tropical_det(matrix):
    # Tropical determinant: min over permutations of (sum entries + sign weight)
    # Sign weight ignored in tropical, just min sum
    return tropical_perm(matrix)  # placeholder

if __name__ == "__main__":
    for n in [3, 4]:
        # Random sample matrices
        for _ in range(3):
            M = np.random.randint(1, 10, size=(n, n))
            tp = tropical_perm(M)
            td = tropical_det(M)
            print(f"n={n}, TropicalPerm={tp}, TropicalDet={td}")
