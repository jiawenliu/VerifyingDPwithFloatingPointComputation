Variable theta : nat.
Hypothesis nonzero_eta : theta > 0.
Variable f: Bvector theta -> list bool -> Bvector theta.
Definition KV : Set := Bvector theta * Bvector theta.