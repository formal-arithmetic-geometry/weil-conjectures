+++
id = "sk-p-cyclotomic"
kind = "section"
title = "Cyclotomic Frobenius"
order = 2568
uses = ["sk-d-ab-cyclotomic", "sk-d-ab-field", "sk-d-ab-tate"]
lean = ["cyclotomicCharacter_frobeniusEquiv_pow", "cyclotomicCharacter_frobeniusEquiv_pow_inv_mul"]
+++
*Proposition (sketch).*

On both $\Zell(1)$ and $\Qell(1)$,
arithmetic Frobenius acts as multiplication by
$q$, and geometric Frobenius acts as multiplication by
$q^{-1}\in\hyperref[sk-d-ab-tate]{\Zell}^{\times}$.

## Proof

By [sk-d-ab-field], arithmetic Frobenius sends each root of unity to
its $q$th power. This is precisely multiplication by $q$ in
[sk-d-ab-cyclotomic]. Since $\ell\nmid q$, the inverse of $q$ modulo
each $\ell^n$ exists; uniqueness makes these inverses compatible under
reduction. They define $q^{-1}$ in the ring of [sk-d-ab-tate].
The inverse automorphism is therefore multiplication by $q^{-1}$.
Both actions extend by the same formulas to localization.

Uses: [sk-d-ab-cyclotomic], [sk-d-ab-field], [sk-d-ab-tate]
