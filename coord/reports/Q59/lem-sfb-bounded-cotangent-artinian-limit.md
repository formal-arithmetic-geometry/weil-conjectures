## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedCotangentArtinianLimit` states
`AlgebraicGeometry.ArtinDeformation.bounded_cotangent_artinian_limit`, with its
whole proof `sorry`. Three explicit definition helpers belong to this same node:
`artinianSequenceLimit`, `artinianSequenceProjection`, `artinianSequenceResidue`.
Their data is constructed using Mathlib's equalizer subalgebra, evaluation algebra
homomorphisms, and the already recorded test-category augmentation. No other
notion is introduced, no new node is needed, and no existing node is corrected.

Source checked: `literature/stacks-project/formal-defos.tex`, Tag 06SF,
`lemma-limit-artinian` (lines 1060–1096), with Tag 06SE immediately before it.
The theorem docstring contains all eight steps of the accepted node proof,
including the nilpotent approximation without a coefficient field, renumbering
for arbitrary nilpotence exponents, and the explicit inverse-limit comparison.

The natural-language hypotheses and conclusions are rendered as follows.

| Node clause | Lean rendering |
| --- | --- |
| Commutative Noetherian local base Λ | `(R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]` |
| Field l finite as a Λ-module, with its Λ-structure | `(k : Type u) [Field k] [Algebra R k] [Module.Finite R k]` |
| Sequence of objects in C_{Λ,l} | `A : ℕ → TestCategory R k`; index `n` denotes positive source level `n + 1` |
| Transition morphisms q_n : A_{n+1} → A_n | `q : ∀ n : ℕ, A (n + 1) ⟶ A n` in the recorded category |
| Every transition is surjective | `hq : ∀ n : ℕ, Function.Surjective (map (q n))` |
| Some integer d ≥ 0 bounds every marked cotangent dimension | `hbound : ∃ d : ℕ, ∀ n : ℕ, Module.finrank (IsLocalRing.ResidueField (ring (A n))) (IsLocalRing.CotangentSpace (ring (A n))) ≤ d` |
| The literal compatible-sequence ring B | `artinianSequenceLimit A q`, the equalizer of the map whose n-th component is `map (q n)` applied to coordinate `n + 1`, and the identity of the product |
| Componentwise operations and diagonal Λ-structure | The equalizer is a `Subalgebra R (∀ n : ℕ, ring (A n))`, inheriting both from Mathlib's product algebra |
| B is local and Noetherian | `∃ hB : IsLocalRing (artinianSequenceLimit A q), IsNoetherianRing (artinianSequenceLimit A q) ∧ ...` |
| The specified residue field is l | `Function.Surjective (artinianSequenceResidue A q)` and equality of its kernel with `@IsLocalRing.maximalIdeal ... hB`; the augmentation is `(residue (A 0)).comp` the actual zeroth projection |
| Maximal-ideal completeness | `IsAdicComplete (RingHom.ker (artinianSequenceResidue A q).toRingHom) (artinianSequenceLimit A q)`, with this ideal explicitly identified as the maximal ideal |
| Each actual coordinate map p_n | `artinianSequenceProjection A q n`, product evaluation restricted along the equalizer inclusion |
| p_n is a surjective local Λ-map | `Function.Surjective (artinianSequenceProjection A q n) ∧ IsLocalHom (artinianSequenceProjection A q n)`; the map is an `AlgHom` over R |
| p_n preserves the residue marking | `(residue (A n)).comp (artinianSequenceProjection A q n) = artinianSequenceResidue A q` for all n |
| Every positive power contains some I_n | `∀ r : ℕ, 1 ≤ r → ∃ n : ℕ, RingHom.ker (artinianSequenceProjection A q n).toRingHom ≤ RingHom.ker (artinianSequenceResidue A q).toRingHom ^ r` |
| Every I_n contains some positive power | `∀ n : ℕ, ∃ r : ℕ, 1 ≤ r ∧ RingHom.ker (artinianSequenceResidue A q).toRingHom ^ r ≤ RingHom.ker (artinianSequenceProjection A q n).toRingHom` |

Using intrinsic residue fields in the bound does not alter its hypothesis.
Each test comes with a surjective R-augmentation to k whose kernel is the
maximal ideal. The quotient therefore has the specified R-algebra isomorphism
with k. Transport of the cotangent module across that field isomorphism gives
exactly its marked k-vector-space structure, with the same finite dimension.
Finiteness here is guaranteed by Artinian implies Noetherian and Mathlib's
`IsLocalRing.instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing`;
there is no infinite-dimensional-finrank-zero loophole. Similarly, a surjective
augmentation to k with maximal kernel is exactly the specified residue-field
isomorphism, as used by `IsTestAlgebra` itself. No arbitrary k-algebra structure
on any test or coefficient field inside any test is assumed.

The ℕ reindexing includes all positive levels and excludes none: A 0 is the
source A_1, q 0 is the source A_2 → A_1, and every existential n encodes a
positive source index n+1. The exponent r remains explicitly positive.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `AlgebraicGeometry.ArtinDeformation.TestCategory`, `IsTestAlgebra`, `ring`,
  `testLocal`, `testArtinian`, `residue`, `map`. The category is the full
  subcategory of augmented algebras. Its arrows preserve augmentations and are
  automatically local; its objects contain the recorded local and Artinian
  properties and a surjective augmentation with maximal kernel. This interface
  is usable unchanged. It places the base, residue field and test rings in the
  same object universe, as in the project's size convention.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (the recorded
  noetherian-ring dependency); the recorded `isNoetherianRing_iff` and its
  finite-ideal interpretation were read. This import is already public through
  the test-category module.
- `Mathlib.Algebra.Field.Defs`: `Field` (the field node's mathlib_match),
  publicly available through the test-category imports.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`
  (the recorded completion dependency), publicly imported by the test-category
  module. `IsAdicComplete` is Hausdorff plus precomplete and is equivalent to
  bijectivity of the canonical completion map; its use matches the node.
- `Mathlib.RingTheory.Ideal.Cotangent`: `IsLocalRing.CotangentSpace`,
  `IsLocalRing.ResidueField`, their canonical scalar structure, and the finite
  dimensionality instance for Noetherian local rings.
- `Mathlib.Algebra.Algebra.Pi`: `Pi.evalAlgHom`, `AlgHom.pi` and the componentwise
  product algebra. `AlgHom.equalizer` is Mathlib's existing subalgebra construction.

The following stated proof prerequisites are imported without `public`:
`Mathlib.RingTheory.LocalRing.Module` (`IsLocalRing.map_mkQ_eq_top`, the Nakayama
match), `Mathlib.Algebra.MvPolynomial.Basic` (`MvPolynomial`, the polynomial-ring
node), and `WeilConjectures.RingTheory.FiniteModuleComplete`
(`finite_module_complete_over_complete_noetherian`). The Artinian-local
Noetherianity/nilpotence match is provided by the public
`Mathlib.RingTheory.HopkinsLevitzki` import of the test-category module, including
`instIsNoetherianRingOfIsArtinianRing` and
`isArtinianRing_iff_isNilpotent_maximalIdeal`. The proof-only nodes
`lem-sfb-artin-completed-polynomial-test-ring` and
`lem-sfb-artin-descending-ideal-adic-topology` have no Lean record at the time of
reading, so no speculative module import is added. They are not needed to TYPE
this statement, and their unchanged proof dependencies remain in the DAG.

Edge cases checked mathematically before writing:

- Constant marked tower, including all A_n = k and identity transitions:
  the literal limit is the constant sequences, all kernels are zero, and both
  cofinality directions hold with exponent 1.
- Bound d = 0: all Artinian tests have zero cotangent dimension and hence are
  fields; the markings make the tower constant up to its specified isomorphisms.
  The statement permits this case, with zero maximal ideal.
- Mixed characteristic, R = ℤ_(p), k = F_p, A_n = ℤ/p^(n+1): no coefficient
  field is assumed; the predicted inverse limit is ℤ_p with the usual cofinal
  filtrations.
- Equal characteristic, R = k, A_n = k[t]/(t^(n+1)): the statement predicts
  k[[t]], and the filtration containments are in the right directions.
- Arbitrarily delayed/repeated levels: no hypothesis ties n to a nilpotence
  exponent. The cofinality conclusions allow arbitrary witnesses, matching the
  renumbering in the proof.
- Neither a zero test ring nor an empty tower can occur: an augmentation onto
  the nontrivial field k excludes the zero ring, and the sequence has level 0.
  No accidental extra restriction on a valid tower is imposed.

Searches for an existing statement or construction:

1. `msearch.py ... leanfinder` with query
   "An inverse sequence of surjective Artinian local algebras with bounded
   cotangent dimension has Noetherian complete local inverse limit" returned
   eight hits: the finite-dimensional cotangent instance,
   `IsAdicComplete.henselianRing`, `Ideal.instIsNoetherianCotangentOfSubtypeMem`,
   completion flatness, finite local Krull dimension, power-series
   Noetherianity, finite-module completion, and local Hausdorffness. None states
   the bounded-cotangent inverse-limit assertion.
2. `msearch.py ... loogle` with query
   `Ideal.Cotangent, IsLocalRing.ResidueField` returned three cotangent-space
   interface lemmas (`toCotangentSpace_eq_toCotangent`,
   `toCotangentSpace_apply`, `CotangentSpace.span_image_eq_top_iff`). No match.
3. `msearch.py ... grep` with query
   `inverseLimit|[Bb]ounded.*[Cc]otangent|[Aa]rtinian.*[Ll]imit` in `RingTheory`
   returned zero hits. A direct `rg` of the project Lean trees for cotangent and
   Artinian-limit terms found only other cotangent results and unrelated
   Artinian towers in homological categories, not this ring-limit theorem.
4. `rg` for the exact node id in `lean/WeilConjectures` returned no match.
   `rg` for all four proposed declaration names throughout Mathlib,
   `lean/WeilConjectures` and `lean/Sheaf` returned no collision.
5. Direct source searches found Mathlib's already existing `AlgHom.equalizer`,
   `AlgHom.pi` and `Pi.evalAlgHom`. The helpers merely apply those constructions
   to the tower in the item; they do not duplicate generic limit infrastructure.

Validation: the prescribed `scompile.py Q59
lem-sfb-bounded-cotangent-artinian-limit` compiled the module in sandbox mode
and at its real library path with no errors or warnings. All variables and the
universe u are explicitly bound; the only postponed theorem is the item itself.
No statement fault or source discrepancy was found.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
