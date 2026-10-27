## Worker report

Item: `lem-a1-affine-groupoid-constant-rank-norm-annihilator`.
Group: Q86. Date: 2026-10-24 (UTC).

The new module is
`Sheaf.AlgebraicGeometry.AffineGroupoidConstantRankNormAnnihilator`.
Its only declaration is
`AlgebraicGeometry.affineGroupoid_constantRank_norm_annihilator`, a theorem
whose proof is `sorry`. There are no new definitions, auxiliary theorems,
dependency repairs, or statement corrections. All original node fields are
preserved, with only `lean` added.

Source read: `literature/stacks-project/groupoids.tex`, lines 4239–4367,
especially `lemma-integral-over-invariants` (Tag 03BJ), second paragraph,
and `lemma-determinant-trick` (Tag 03BH); also `algebra.tex`,
`lemma-charpoly` (Tag 00DX). The node's last step uses the specified identity
section instead of the source's faithful-flatness argument. I also read the
current `literature/blueprint/latest` statement and proof of
`sec-purity-real-sheaves/sk-lem-wrp-hc2/lem-a1-affine-hc0`. They concern
lisse support, as the item's existing historical provenance explicitly
records; this delivery claims no affine-groupoid paragraph in that proof.

Hypotheses and objects, matched individually:

- `A B : CommRingCat.{u}` give the two commutative rings; `Spec A` and
  `Spec B` are exactly U and R. No algebra structure on B is independently
  chosen.
- `σ τ : A →+* B` are the source and target ring maps. The scheme maps
  are `Spec.map (CommRingCat.ofHom σ)` and
  `Spec.map (CommRingCat.ofHom τ)`. This is an equivalent parametrization
  of arbitrary affine s and t: `Spec.preimage`, `Spec.map_preimage`, and
  `Spec.preimage_map` identify the two presentations, without adding a
  hypothesis or restricting their maps.
- `e : Spec A ⟶ Spec B`, `i : Spec B ⟶ Spec B`, and `c` with domain the
  ordered pullback of the above source and target are the three remaining
  specified maps. `hG : Scheme.IsGroupoid ... e i c` uses the dependency's
  actual groupoid-law structure, including all unit, inverse, composition,
  and associativity laws on test schemes. It is not a replacement predicate.
- `[Nontrivial A]` is precisely the assumption A is not the zero ring.
- `r : ℕ`, `hr : 1 ≤ r`, and `hσ`, `hτ` with
  `IsFiniteLocallyFreeOfDegree r` assert positive common constant degree
  and finite local freeness of both maps. No global freeness, reducedness,
  domain, characteristic, or Noetherian assumptions occur.
- `a : A` is arbitrary. `P : Polynomial A` and
  `hP : P = Algebra.finiteLocallyFreeNormPolynomial σ r hσ (τ a)` name the
  polynomial introduced by “set P_a” in the node. This equality fixes P
  uniquely to the existing canonical construction; it is not an arbitrary
  norm, polynomial, or extra mathematical assumption. The construction is
  literally `N_{σ[T]}(X - C (τ a))`, using the polynomial-extension degree
  supplied by the existing characteristic-polynomial theorem.
- The invariant ring C is the existing Mathlib subring `σ.eqLocus τ`.
  `Polynomial.map` and `Polynomial.mapRingHom` are the coefficientwise
  extensions fixing the indeterminate.

Conclusions, in the exact order of the Lean conjunctions:

1. `P = Polynomial.X ^ r + ∑ j ∈ Finset.range r,
   Polynomial.C (P.coeff j) * Polynomial.X ^ j` is the displayed expansion.
   It uses actual coefficients as p_j, rather than existential coefficients
   subsequently requiring identification with them.
2. `∀ j : ℕ, j < r → σ (P.coeff j) = τ (P.coeff j)` gives every lower
   coefficient's invariance.
3. `P ∈ Polynomial.lifts (σ.eqLocus τ).subtype` is literally membership
   in the image of C[T] inside A[T], using Mathlib's definition of lifts.
4. `P.Monic ∧ P.natDegree = r ∧ P.coeff r = 1` gives monicity, degree r,
   and the displayed convention p_r = 1. Since A is nontrivial and P is
   monic, the natural degree here agrees with the ordinary degree.
5. The equality with `Algebra.finiteLocallyFreeDeterminantNorm
   (Polynomial.mapRingHom σ) r ...
   (Polynomial.map τ (Polynomial.X - Polynomial.C a))` is the node's
   identity `P_a = N_{σ[T]}(τ[T](T-a))`. Its degree witness is exactly the
   polynomial-base-change clause of the existing theorem.
6. `(Polynomial.map σ P).eval (τ a) = 0` is the precise Cayley–Hamilton
   annihilation identity requested in the node.
7. `τ (P.eval a) = ∑ j ∈ Finset.range (r + 1),
   τ (P.coeff j) * τ a ^ j` is the first evaluation comparison.
8. Equality of that sum with the corresponding sum of
   `σ (P.coeff j) * τ a ^ j` is the replacement of invariant coefficients.
9. Equality of the latter sum with `(Polynomial.map σ P).eval (τ a)` is
   the last polynomial-evaluation comparison.
10. `τ (P.eval a) = 0` records the zero at the end of the comparison chain.
11. `(Spec.preimage e).hom.comp τ = RingHom.id A` uses the specified
    identity map's pullback ε, not an existential retraction.
12. `P.eval a = (Spec.preimage e).hom (τ (P.eval a))` is the first equality
    in the final descent chain.
13. `(Spec.preimage e).hom (τ (P.eval a)) = 0` is its second equality.
14. `P.eval a = 0` is the final root assertion.

The two sums over `Finset.range (r + 1)` include exactly 0 through r.
In particular the leading coefficient participates in both comparison sums.
The theorem docstring carries all four original proof steps and names their
dependencies. The canonical norm's existing predicate
`Algebra.IsLocallyFreeDeterminantNorm` characterizes its value on every
principal free chart and every finite basis. Its uniquely determined norm
functions are supplied by the existing theorem, so this delivery adds no
choice of undetermined data.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`,
  and `Spec.map` (the recorded scheme and affine-spectrum dependencies).
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage`,
  `Spec.homEquiv`, and the inverse identities mentioned above.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its projections, exposed by the
  groupoid-law module's public pullbacks import.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`:
  `AlgebraicGeometry.Scheme.IsGroupoid`, including `target_id`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `IsFiniteLocallyFreeOfDegree`, publicly exposed by the norm-polynomial
  dependency and used by `hσ` and `hτ`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, with `X`, `C`,
  `coeff`, `eval`, `map`, and `mapRingHom` supplied by the polynomial
  modules imported by the recorded dependencies; `Monic` and `natDegree`
  are also already exposed there.
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts`:
  `AlgebraicGeometry.exists_finiteLocallyFree_norm_charts`. This is the
  recorded norm-charts source for the local determinant construction;
  its module is publicly imported as a statement dependency. The
  canonical function is reused from the next dependency, not reconstructed.
- `Sheaf.RingTheory.FiniteLocallyFreeNormCharacteristicPolynomial`:
  `Algebra.IsLocallyFreeDeterminantNorm`,
  `Algebra.finiteLocallyFree_norm_characteristicPolynomial`,
  `Algebra.finiteLocallyFreeDeterminantNorm`, and
  `Algebra.finiteLocallyFreeNormPolynomial`. This is a public import
  because its existing canonical construction occurs in the statement.
- `Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant`:
  `AlgebraicGeometry.affine_groupoid_polynomial_norm_invariant`.
  This proof dependency is imported without `public`. Its full signature
  and docstring were read, including its test-point groupoid presentation
  and chart characterization of Q. It supplies the invariance proof plan,
  not a new assumption in this theorem.
- Mathlib `RingHom.eqLocus` from
  `Mathlib.Algebra.Ring.Subring.Basic` and `Polynomial.lifts` from
  `Mathlib.Algebra.Polynomial.Lifts` give the existing notions of C and C[T].

Edge cases checked before writing:

- Identity groupoid, rank 1: the norm polynomial is T-a, with coefficients
  -a and 1, and each comparison reduces to ordinary evaluation at a.
- A trivial group action of order r on a nonreduced ring such as Z/4Z:
  the arrow algebra is a product of r copies, the norm is (T-a)^r,
  and invariance and root descent still hold. No reducedness was used.
- The order-two action on k[x] sending x to -x: for a=x the norm
  polynomial is T²-x². The coefficients are invariant and evaluation
  vanishes, including in characteristic two.
- Positive rank in any characteristic, including when that characteristic
  divides r: no division by r or separability occurs in the statement.
- Rank zero and the zero base ring are excluded exactly by the node's
  explicit hypotheses, not by hidden construction restrictions. Empty
  indexing issues do not introduce further assumptions; all sums are
  finite ranges and the leading index r is included in the evaluation.
- A finite locally free algebra with no global basis is allowed: all
  hypotheses and the reused norm use local freeness, not Module.Free on
  the global algebra. All rings and spectra use one arbitrary explicit
  universe u, as in the existing affine-scheme interfaces.

Searches made (through the prescribed wrapper, 2026-10-24):

- LeanFinder query: “For an affine finite locally free constant rank scheme
  groupoid, the norm polynomial of T minus target pullback has invariant
  coefficients and vanishes at the original element by the identity section”.
  Eight hits: affine-space coordinate constructions and Weierstrass norm
  formulas. None states this scheme-groupoid result.
- Loogle query:
  `Algebra.finiteLocallyFreeNormPolynomial, Polynomial.map, Polynomial.eval`.
  Zero hits; the service reports unknown identifier
  `Algebra.finiteLocallyFreeNormPolynomial` (a project declaration).
- LeanSearch query: “The norm characteristic polynomial for a finite
  locally free affine scheme groupoid is invariant and annihilates every
  element of its base ring”. Eight hits on linear-map and matrix
  characteristic polynomials and finite-group-action characteristic
  polynomials; none gives the finite locally free groupoid assertion.
- Wrapper grep query: `norm.*charpoly|charpoly.*norm|charpoly_mem_lifts`,
  restricted to Mathlib `RingTheory`. Six hits in Norm/Basic,
  Invariant/Basic, and Invariant/Galois. The finite-group-action polynomial
  is not this source norm on a general finite locally free groupoid.
- Direct `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `finiteLocallyFreeNormPolynomial|constant_rank_norm_annihilator|groupoid.*norm|norm.*groupoid`
  found the existing canonical norm polynomial and related invariance,
  integrality and orbit-fibre modules. Their declarations were inspected;
  none states the full expansion and evaluation comparison of this item.
- Direct `rg -n` for the item ID in `lean/WeilConjectures` found no match.
  A full-name search for the chosen theorem name in Mathlib/project
  sources and `dag/lean_names_upstream.json` found no existing declaration.
- Read the existing `Polynomial.lifts` and `RingHom.eqLocus` definitions
  and their membership signatures instead of creating private copies.

Validation: the prescribed `scompile.py Q86 <item> <file>` compiled both
the sandbox and the actual module path successfully against the server's
published library (7.5 s and 3.7 s respectively). It printed no errors or
warnings. All declarations and universes are explicitly bound. Every Lean
line is at most 100 characters. The theorem's sole proof is `sorry`.
No disputed statement or dependency fault was found.

## Second reading by Q86

I reread the completed file against the original node after compilation.
This is the final rereading by the single dispatcher worker; the
maintainer's independent review remains the separate delivery review.

The nonzero-ring, positive-degree, common-rank and full groupoid hypotheses
are present as `[Nontrivial A]`, `hr`, `hσ`/`hτ`, and `hG`. Using Spec.map
to present s and t is exhaustive by the recorded affine-spectrum
equivalence. The polynomial's equality binder fixes exactly the existing
canonical norm of T-τ(a), and does not request a global free basis or
provide a freely chosen map. Each p_j is the actual coefficient P.coeff j.

I checked the expansion, the j<r coefficient condition, membership in the
image of C[T], monicity, degree and p_r=1 separately. I checked the second
norm formula and Cayley–Hamilton identity separately. Both finite sums run
through r, carry the correct source/target coefficients, and evaluate at
τ(a), not at a. Their three comparison equalities and the zero assertion
are all written explicitly. The last three equalities use the actual
pullback of e, with its left inverse to τ explicitly concluded.

No mismatch was found and no mathematical correction was made during
this rereading. There are no new-node or dependency-module files to review.
