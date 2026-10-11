## Worker report

The new module `Sheaf.RingTheory.FiniteSpectrumMaximalPrimes` states
`Ideal.isMaximal_of_finite_primeSpectrum_of_finiteType`, with its sole proof `sorry`.
It defines no new notion and requires no additional nodes or dependency modules.
The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- “Let k be a field”: `(k : Type u) [Field k]`.
- “B a commutative k-algebra”: `(B : Type v) [CommRing B] [Algebra k B]`.
- “of finite type [def-weil-pbc-finite-type-algebra]”: `[Algebra.FiniteType k B]`.
- “allowing B = 0”: there is no `Nontrivial B` assumption.
- “Spec B has finitely many prime ideals [def-weil-affine-spectrum]”:
  `(hfin : Finite (PrimeSpectrum B))`. `PrimeSpectrum` is the type of all prime ideals,
  and `AlgebraicGeometry.Spec.topObj` is literally `TopCat.of (PrimeSpectrum B)`;
  the scheme `Spec` uses that space. Thus this is precisely finiteness of the underlying
  spectrum, with no topology condition added.
- “every prime ideal of B is maximal”: arbitrary `(p : Ideal B) (hp : p.IsPrime)`
  with conclusion `p.IsMaximal`.
- The parenthetical “equivalently dim B ≤ 0” identifies the same conclusion, rather than
  imposing a second condition: `Ring.krullDimLE_zero_iff` in
  `Mathlib.RingTheory.KrullDimension.Basic` is exactly the equivalence between
  `Ring.KrullDimLE 0 B` and `∀ I : Ideal B, I.IsPrime → I.IsMaximal`.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: Mathlib leaf `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType`, defined by finite generation of the top subalgebra.
  This module is imported directly.
- `def-weil-affine-spectrum`: Mathlib leaf `AlgebraicGeometry.Spec` in
  `Mathlib.AlgebraicGeometry.Scheme`. Read its definition and `Spec.topObj` in
  `Mathlib.AlgebraicGeometry.Spec`, plus the full `PrimeSpectrum` definition/docstring in
  `Mathlib.RingTheory.Spectrum.Prime.Defs`. Only the underlying prime-ideal type is needed
  here, supplied by the import `Mathlib.RingTheory.Spectrum.Prime.Basic`; importing the
  scheme construction itself would be unused.
- The proof docstring names the node's sole proof dependency,
  `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`. Its Mathlib match is
  `isJacobsonRing_of_finiteType` and `isJacobsonRing_iff_prime_eq` in
  `Mathlib.RingTheory.Jacobson.Ring`; their signatures and the Jacobson definition were read.
  This dependency is for stage 3, not an extra hypothesis in this stage-2 statement.

Edge cases checked: the zero ring has empty prime spectrum, and no prime ideal can satisfy
`hp`, so the conclusion is vacuous. The empty family of maximal ideals above a putative
prime cannot occur, as its intersection is the improper ideal. A field algebra B = k
has one prime, which is maximal. Products and nonreduced finite-dimensional algebras are
allowed: neither domain nor reducedness is required. No characteristic restriction occurs.
Independent explicitly declared universes `u v` allow arbitrary field and algebra sizes.
The finite-type hypothesis matters: a one-dimensional local DVR can have finite spectrum
but a nonmaximal zero prime; such a ring is not a finite-type field algebra.

Source check: the local Stacks checkout is absent on this machine. Read the official
[Stacks Tag 0ALW](https://stacks.math.columbia.edu/tag/0ALW), Lemma 10.61.3,
whose equivalence of (2) and (1) supplies the result for nonzero algebras. The node's
zero-ring extension is valid vacuously and uses dimension at most zero. No statement
correction or STATEMENT-DISPUTED issue is needed. The declaration docstring carries the
node's full Jacobson/intersection/finite-product proof, including the empty-family case.

Searches (all msearch queries used group G1 and this item):

- LeanFinder: “A finite type algebra over a field with finitely many prime ideals has all
  prime ideals maximal”. Eight related hits, including `Ring.KrullDimLE.mk₀`,
  `Ideal.isMaximal_of_isPrime`, and dimension-one variants; no exact statement.
- Loogle: `PrimeSpectrum, Ideal.IsMaximal, Algebra.FiniteType`: zero hits.
- LeanSearch: “A finite type algebra over a field with finite prime spectrum has every
  prime ideal maximal”: unavailable, Internal Server Error; no verdict inferred.
- Mathlib grep through msearch, query `finite.*[Pp]rime|isMaximal.*finite|finite.*isMaximal`
  in `RingTheory`: 25 related hits, including
  `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`. Read that theorem;
  it requires discreteness to derive maximality and is not this statement.
  Read the finite-fibre argument in `Mathlib.RingTheory.QuasiFinite.Basic` too:
  it composes several facts, with no exact declaration to reuse.
- `rg -n 'finite.*[Pp]rime|isMaximal.*finite|finite.*isMaximal|finite_spectrum'` over
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`:
  related residue-field, quasi-finite, and finite-dimensional results, no exact match.
- `grep -rn 'lem-pqf-finite-spectrum-maximal-primes'` in the source project: no hits.
- Exact fresh name `isMaximal_of_finite_primeSpectrum_of_finiteType` searched with `rg`
  in `dag/lean_names_upstream.json`, Mathlib, the source project, and `lean/Sheaf`:
  no hits.

Validation: the single module is compiled on the server with `scompile.py`; delivery
preflight and server compile are checked with `deliver2.py --no-push`. The independent
second reader supplies their own reading and performs delivery.

## Second reading by G1

Independently opened the sandbox node and Lean module, both statement-dependency nodes,
 their recorded Mathlib declarations, and the proof-dependency node and declarations.
No mathematical, signature, dependency, or documentation mismatch was found. The Lean
module and node record are retained unchanged; this section records the independent review.

Object/hypothesis/conclusion inventory and matching (H3):

- Object k, a field: `(k : Type u) [Field k]`. Exact; not restricted to algebraically
  closed, finite, or characteristic-zero fields.
- Object B, a commutative k-algebra: `(B : Type v) [CommRing B] [Algebra k B]`.
  Exact; no domain, reducedness, localness, or additional structure is assumed.
- Finite type over k: `[Algebra.FiniteType k B]`. Exact. Read the dependency
  `def-weil-pbc-finite-type-algebra` and `FiniteType.lean:39`: its top subalgebra is
  finitely generated, precisely the polynomial-generator definition in that node.
- B = 0 allowed: no `[Nontrivial B]` binder. Exact.
- Spec B has finitely many prime ideals: `(hfin : Finite (PrimeSpectrum B))`.
  Exact. Read `def-weil-affine-spectrum`, `Scheme.lean:470`, `Spec.lean:58`, and
  `Spectrum/Prime/Defs.lean:34`. The scheme's underlying space is the type of all
  prime ideals of the same B. Thus the statement uses the existing underlying
  spectrum directly, not a private replacement or a finite subset of its points.
- Every prime ideal of B is maximal: arbitrary `(p : Ideal B) (hp : p.IsPrime)`
  followed by `: p.IsMaximal`. Exact quantification, following all algebra hypotheses.
- Parenthetical equivalence with dimension at most zero: this is an alternative
  description of the preceding conclusion. Read `Ring.krullDimLE_zero_iff` in
  `KrullDimension/Basic.lean:102`, whose right side is exactly the universal conclusion
  here. No additional assertion or dimension-equals-zero restriction is needed.

Source: the repository has no Stacks checkout. Independently fetched the official
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex)
to this item's scratchpad, read its opening ring conventions and the lemma
`lemma-finite-type-algebra-finite-nr-primes` (lines 14790–14839), and checked
[Tag 0ALW](https://stacks.math.columbia.edu/tag/0ALW). Its (2) implies (1) is the
nonzero case. The node explicitly extends this to the zero ring using maximality of
all primes / dimension at most zero; that extension is vacuous and valid. No standing
source hypothesis is missing. In particular, Noetherian and Jacobson properties in
the source proof are consequences of finite type over a field, not extra hypotheses.

Edge cases: the zero ring has empty spectrum and no prime p satisfying hp; the
empty scheme is consequently included. For a fixed prime, the empty family of
maximal ideals above it would have intersection top, contradicting properness;
the docstring includes this case. B = k has one prime. Finite products, nilpotents,
and finite-type algebras generated by zero elements are included. There is no n
parameter or characteristic condition to exclude n = 0 or a characteristic.
Universes u and v are explicitly bound and independent; every variable in the
signature is bound. No hidden finiteness or nontriviality instance is requested.

Independent searches used different wording from the first reader:

- `msearch.py ... leanfinder "finitely generated field algebra semilocal zero
  dimensional all primes maximal"`: eight related results (including
  `Ring.KrullDimLE.isField_of_isDomain` and `PrimeSpectrum.instUnique`), no exact match.
- `msearch.py ... loogle '\"IsJacobsonRing\", \"Finite\", \"IsMaximal\"'`:
  no results.
- `msearch.py ... grep 'Jacobson.*[Ff]inite|[Ff]inite.*Jacobson|[Ss]emilocal'`:
  related Jacobson/finite-type and Artinian results, no exact statement.
- Direct rg in Mathlib's Jacobson and prime-spectrum modules and QuasiFinite/Basic
  checked finite-spectrum and finite-Jacobson variants. Read
  `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero` and the finite-fibre
  argument in `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`: these require
  composition of several facts and do not themselves state this node.
- Direct rg in the source project's WeilConjectures and repository lean/Sheaf for
  finite-spectrum, spectrum-finite, finite-maximality and dimension variants found
  only related results. The exact fresh declaration name has no collision in those
  trees, Mathlib, or dag/lean_names_upstream.json.
- The worker's recorded LeanSearch service failure is not treated as a negative
  search result; the independent LeanFinder, Loogle and source searches above give
  no exact declaration to reuse.

H4/H12/H13: no new notions, new nodes, dependency modules, or statement correction
are needed. Both statement dependencies have usable existing Mathlib notions. For
the proof dependency, read `isJacobsonRing_of_finiteType` (Jacobson/Ring.lean:666)
and `isJacobsonRing_iff_prime_eq` (:73); they supply precisely the intersection
property described by that node, with the field's Jacobson instance automatic.

H5/H6/H8/H9: there is no definition and hence no hollow data. The sole theorem's
proof is `sorry`, as required at stage 2. The module and theorem docstrings cite
Stacks 0ALW and the exact blueprint id. The proof docstring follows the node:
Jacobson intersection, finite family, empty-family exclusion, elements outside p,
finite product, primality contradiction, maximality, and the zero-ring case.
Imports are used by the finite-type and prime-spectrum binders, the namespace is
Ideal, and all lines are within 100 characters. The node's lean.statement is the
signature verbatim up to `:=`. No repair was necessary.
