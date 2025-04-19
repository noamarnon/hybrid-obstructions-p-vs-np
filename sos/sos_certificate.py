
# sos/sos_certificate.py
# Skeleton for computing minimal SoS certificate degree for F1 = Perm_n - gamma, F2 = Det_n - delta

import itertools
import numpy as np
from cvxopt import matrix, solvers

def build_gram_matrix_terms(n, degree):
    # TODO: Generate monomials up to given degree
    terms = []  # placeholder
    return terms

def setup_sos_sdp(n, degree):
    # Placeholder for setting up SDP for SoS certificate
    # Returns (G, h, A, b) for cvxopt.solvers.sdp
    G = matrix(np.eye(1))
    h = matrix(0.0, (1,1))
    A = None
    b = None
    return G, h, A, b

def find_min_sos_degree(n, max_degree=4):
    for d in range(1, max_degree+1):
        G, h, A, b = setup_sos_sdp(n, d)
        try:
            sol = solvers.sdp(G, h, A=A, b=b)
            if sol['status'] == 'optimal':
                return d
        except:
            continue
    return None

if __name__ == "__main__":
    for n in [3, 4, 5]:
        degree = find_min_sos_degree(n, max_degree=6)
        print(f"n={n}, minimal SoS degree = {degree}")
