# Stage-1 report: lem-sfb-symmetric-polynomial-cocycle-normal-form

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-polynomial-cocycle-normal-form.json`: statement, split; no Mathlib match. Eight explicit elementary coefficient-calculation steps, a strong induction with all branches, and finite assembly. Added the existing `def-pc-field-characteristic` citation and statement dependency; the mathematical assertion and hypotheses are unchanged.
- No new nodes; no new Mathlib leaves. The polynomial argument terminates in the already-existing definitions of field, characteristic, and polynomial rings. In particular, no node restates the homogeneous case or another clause of this item.
- `citations.json`: 19 entries, quoting the statement of each definition cited by each step verbatim.
- `searches.jsonl`: searches made by the prescribed msearch command. The six inherited search records are preserved, and the new logged queries are appended to the item's records with their actual results.
- `check_coefficients.py`, `edge-checks.txt`: independent finite coefficient-matrix sanity checks; sandbox-only supporting material.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for Witt, Lazard, polynomial cocycles and symmetric cocycles (including reversed word order); no matching declaration was found. No sorry declaration was treated as a proof.

## WANTED

None required for this proof. Milne's available book is the source of the statement and the coefficient-comparison route. Its reference to Lazard 1955, Lemme 3 / DG II §2, 4.6 is not used as an uncited theorem: the missing deduction is supplied explicitly here and `proof_origin.by` is `agent`.

## Source and inherited-record findings

Read Milne, *Algebraic Groups* (2017), Lemma 15.26 and its preceding definition of f_1, printed p.316; also Proposition 15.10 and Corollary 15.11, printed pp.308–309, to check the sign and meaning of the coboundary. Lemma 15.26 only says that its coefficient identities imply the result; it does not write their deduction. This is a proof omission to fill, not a false statement. The delivered proof does not assume uniqueness, group-extension classification, derivatives, Euler's identity, or a perfect field.

The item defines c_p using division in the integers before reduction. The degree-p calculation preserves precisely its negative sign. The only statement-text change adds a reference to the existing characteristic definition; there is no added hypothesis or weakened conclusion.

Read the recorded chapter/unit and the latest blueprint chapter, unit, and direct-image proof (3). This is an auxiliary coefficient calculation deep in the inherited direct-image/alteration/algebraic-group chain. It does not replace a unit step. `blueprint_refs.py ancestor` reports None, as for the parent; retained the inherited null ancestor, precise place and via chain rather than inventing an ancestor. Whole-blueprint searches for cocycle, symmetric polynomial, polynomial derivative, polynomial cocycle, Lazard, and additive cocycle found no equivalent blueprint statement. The symmetric-product hit concerns projective symmetric products, not cocycles.

## Not duplicates

No new nodes were created. Whole-DAG searches for symmetric cocycles, Lazard, Milne 15.26, polynomial derivatives and homogeneous identities were read: the current item and its parent are the relevant cocycle-normal-form records; abstract Galois/unit cocycles and disjoint-variable integration do not state this item. No Stacks tag is invoked, and no SGA source is used.

## Unfinished work

None in the mathematical split. This delivery contains no Lean and ran no compiler, Lake or build.

## Review by Q01

I checked the statement against Milne 15.26 and the coboundary convention of 15.10–15.11. I checked each step against the actual statements of the four existing definition nodes cited, not against facts found only in their proofs. `def-weil-pbc-mv-polynomial-ring` supplies finite monomial expansions, coefficientwise equality and substitution; `def-weil-polynomial-ring` supplies finite single-variable coefficient lists and b(0); `def-pc-field-characteristic` supplies exactly the integer-kernel divisibility criterion; `def-weil-field` supplies inversion of nonzero elements. These are the only black boxes. Every further identity is calculated in the steps.

1. Step 1 uses the two polynomial definitions to separate the finite homogeneous pieces. Linear substitutions preserve total degree, and normalization removes the pure terms and degrees 0 and 1. The induction quantifies over every homogeneous normalized symmetric cocycle of degree n, with the two base degrees stated before its use.
2. Step 2 uses the multivariate expansion and the characteristic interpretation of integers. I expanded all four cocycle terms at X^i Y^(n-1-i) Z: their contributions are respectively 0, -A binom(n-1,i), (n-i)u_i, 0. This gives (*), including i=n-1, without a derivative theorem.
3. Step 3 uses the characteristic and field definitions to invert n only when p does not divide n. The relation at n-i and symmetry give the second coefficient relation; their sum is Pascal's identity. The displayed polynomial is delta(-A/n T^n), so its sign and b(0)=0 are correct.
4. Step 4 verifies integer divisibility before coefficient reduction and the exact identity (p-i)(binom(p,i)/p)=binom(p-1,i). The factor p-i is nonzero for every interior index. Thus h=-A c_p, with no need to divide by p in k. In characteristic 2, c_2=-XY and this formula remains valid.
5. Step 5 uses (*) at n-p only when n>p, so that this index is interior. I checked the residue of binom(n-1,p-1) by multiplying by (p-1)!, which is invertible. For p=2 the sign -1 is 1 in k; for odd p the exponent p-1 is even. Thus A=0, and each coefficient with p not dividing i vanishes by a legitimate nonzero cancellation.
6. Step 6 uses the multivariate coefficient definition and characteristic. The coefficient list explicitly constructs g without taking any roots. I checked normalization, symmetry, homogeneity m=n/p<n, the binomial expansion in characteristic p, and the injective three-variable substitution. This establishes every induction hypothesis on g, not just its support restriction.
7. Step 7 applies that already-set-up induction at m<n. I checked the substitution on both the Witt terms and delta b, using c_p's integer-image coefficients fixed by Frobenius. The a_i are not raised to p and no roots of them are chosen. The new polynomial is b(T^p), with constant coefficient zero, and the coefficient list is shifted by one index.
8. Step 8 uses the finite coefficient definitions to sum the homogeneous representations and pad all lists to one finite length. It handles f=0 explicitly with r=0. The proof uses only field inverses of integers prime to p, so it applies to imperfect fields such as F_p(t).

The B–E checks found no self-contained-statement defect, hidden external theorem, circular citation, clause moved into a new node, missing induction base, or smallness/field-extension hypothesis. Each of the eight steps is shorter than 800 characters; none hides a separately quoted lemma. These are elementary coefficient operations written out, not the source's vague assertion that the identities suffice. It would create artificial nodes to extract Pascal's identity, finite coefficient regrouping, or distinct-monomial injectivity as new mathematical tasks.

For a separate small-case check I built the complete homogeneous cocycle and symmetry linear systems over F_p and checked their nullspaces, not merely the recurrence used in the proof. For p=2,3,5 I checked every degree 2 through 32; for p=7 I also checked degrees 49 and 50. In all 126 cases the kernel has dimension one and the expected generator (delta T^n off p-power degrees, a variable-power of c_p at p-power degrees) satisfies every equation. This covers the degree-p sign, the first Frobenius descent, and non-p-power divisible degrees. Degrees 0 and 1, f=0, and the absence of coefficient-root choices were checked directly as above. The computation is supporting evidence; the general proof is the eight-step coefficient induction.
