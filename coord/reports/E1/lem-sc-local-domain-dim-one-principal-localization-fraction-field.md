# Delivery report

1. Files written:
   - `lem-sc-local-domain-dim-one-principal-localization-fraction-field.json` (statement, split; no new nodes).
   - `citations.json` (verbatim statement quotes for every citation in every step).
2. Attachments: none.
3. WANTED: none.
4. The item was already correctly stated and had no Lean declaration. I searched the whole DAG and blueprint before deciding that no auxiliary node was needed. The proof follows Algebra Tags 00CM and 00C8: dimension one leaves only the zero and maximal primes, localization removes the maximal prime because it contains `f`, and the resulting field containing `B` is its fraction field.
5. Nothing remains unfinished.

## Review by E1

I read the item source recorded as `literature/stacks-project/algebra.tex`, Algebra Lemmas Tags 00CM and 00C8, and checked the imported statement against the local-domain and localization hypotheses. I also read the statements of `def-weil-pbc-krull-dimension-ring`, `def-weil-ring-localization-away`, and `lem-weil-pbc-primes-of-localization`; the first supplies the strict-prime-chain meaning of dimension one, the second supplies the principal localization and its fraction representatives, and the third explicitly supplies the bijection between primes of `B_f` and primes of `B` avoiding `f`.

Step 1 uses only the Krull-dimension statement and the definitions of domain and local ring: `(0)` is prime, a nonzero prime cannot have a strict prime above it in dimension one, and locality identifies every maximal prime with `m`. Step 2 uses exactly clause (2) of the prime-correspondence node and the localization definition; `m` is excluded since `f` lies in it and `(0)` is allowed since `f` is nonzero in a domain. Step 3 uses the localization definition for the injective map and fraction representatives; the remaining assertions are the elementary maximal-ideal argument that a ring with only the zero prime is a field and the direct surjectivity calculation into `Frac(B)`.

I tested the statement on `k[t]_(t)` with `f=t` and on `Z_(p)` with `f=p`; both localizations identify with `k(t)` and `Q`, respectively. I also checked the edge conditions `f != 0` and `f in m`, since dropping either would invalidate the prime exclusion or injectivity arguments. The required Mathlib searches were run for the item: LeanSearch was unavailable, Loogle returned only general localization APIs, LeanFinder returned only general dimension/localization declarations, and the Mathlib grep found no exact theorem.
