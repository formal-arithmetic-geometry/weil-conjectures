Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-affine-constant-second.json`: split statement.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-charp-constant-second.json`: statement-only missing affine characteristic-ℓ vanishing node; Mathlib searches found no match.
- `citations.json`: verbatim step citations.

Attachments: none. The Lean theorem `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_constantZMod` is not an attachment because its sorry-free body reaches thirteen sorry declarations, including the affine characteristic-ℓ theorem.

WANTED: none.

The imported proof incorrectly cited the Artin–Schreier sequence and quasi-coherent acyclicity directly for the affine characteristic branch, while the project already has the more precise affine-scheme vanishing declaration as a sorry theorem. I replaced that branch by a statement-only node for the exact missing theorem. The prime-to-characteristic branch now explicitly cites the root-of-unity trivialization, Kummer divisor comparison, and Picard divisibility statements.

I could not prove the new affine characteristic-ℓ statement at stage 1; it is deliberately unsplit and records the sorry-backed Lean declaration.

## Review by J1

I read the item's imported node, the blueprint proof description, and `WeilConjectures/AlgebraicGeometry/Curve/Affine.lean` lines 295–331. The Lean theorem has the exact target statement but is transitively sorry-backed, so I did not attach it. For step 1 I reread the statements of `def-sc-mu-trivialization`, `lem-sc-second-kummer-divisors`, and `lem-sc-pic-affine`: they respectively provide the sheaf isomorphism, the identification with `Pic(C)/ell`, and surjectivity of multiplication by `ell`. For step 2 I reread the new node, whose statement exactly matches the affine characteristic-ℓ theorem used by the Lean branch. Hypotheses are checked by the item's smooth affine connected curve assumptions, algebraic closedness, and the two exhaustive cases `(ell : k) != 0` and `(ell : k) = 0`. I searched the DAG and blueprint before creating the new node; no duplicate statement was found. Mathlib searches were run for the item and new node; LeanSearch was unavailable and recorded as such.

## Second reading by J1

## Not duplicates

- `lem-sc-affine-charp-constant-second` vs `lem-sc-local-ring-artin-schreier-kernel`: the new node is a global higher-cohomology vanishing theorem for every affine scheme in characteristic $p$ and every $q\\ge2$; the existing node only identifies Frobenius-fixed elements in one local ring.
- `lem-sc-affine-charp-constant-second` vs `lem-sc-field-artin-schreier-kernel`: the new node is a global higher-cohomology vanishing theorem for affine schemes; the existing node only identifies Frobenius-fixed elements in a field.

- Item statement: checked against blueprint node `lem-sc-affine-constant-second`, including smooth affine connected curve, algebraically closed field, arbitrary prime, and etale $H^2$; verdict correct.
- Item step 1: checked `def-sc-mu-trivialization`, `lem-sc-second-kummer-divisors`, and `lem-sc-pic-affine`; verdict correct.
- Item step 2: checked the characteristic branch against the repaired affine Artin–Schreier node; verdict correct.
- New node `lem-sc-affine-charp-constant-second`: checked on $X=\\operatorname{Spec}(k)$, $X=\\operatorname{Spec}(k[t])$, and $q=2$; checked B1–B7 and Stacks Tag 0A3J, section-artin-schreier; verdict correct after repair.
- Changes: replaced curve-only dependencies with generic scheme, etale-site, and constant-sheaf definitions; changed the source to Tag 0A3J; removed redundant Subsingleton wording.
