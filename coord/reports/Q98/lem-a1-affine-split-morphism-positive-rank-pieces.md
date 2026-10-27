## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSplitMorphismPositiveRankPieces` states
`AlgebraicGeometry.affine_split_morphism_positive_rank_pieces`. Its only theorem
has proof `sorry`. There are no new definitions, helper theorems, dependency
repairs, or statement changes. The existing statement and proof plan are retained.

Hypothesis and clause correspondence:

- The arbitrary commutative rings are `A B : CommRingCat.{u}`; their schemes are
  literally `Spec B` and `Spec A`. The morphism is `f : Spec B ⟶ Spec A`.
  There is no nonzero-ring, connectedness, Noetherian, or field hypothesis.
- Finite locally free is exactly `[f.IsFiniteLocallyFree]`, the recorded class
  extending `IsFinite f`, `Flat f`, and `LocallyOfFinitePresentation f`.
- The section is `a : Spec A ⟶ Spec B` and `ha : a ≫ f = 𝟙 (Spec A)`.
  Lean composes left to right, so this is the node's `f ∘ a = id`.
- The stated dimension `d(y)` is `f.fiberDegree y`, not the rank of a different
  module. Its definition is `Module.finrank ((Spec A).residueField y)
  Γ(f.fiber y, ⊤)` with `Scheme.Hom.fiberAlgebra`. The latter is the algebra
  induced by `f.fiberToSpecResidueField y`; `f.fiber y` is by definition
  `pullback f ((Spec A).fromSpecResidueField y)`. Thus this uses the specified
  scheme-theoretic fibre, its global functions, and the canonical field action.
- `∀ y : Spec A, 1 ≤ f.fiberDegree y` is positivity at every point.
- The existential family `U : ℕ → (Spec A).Opens` is identified with the exact
  level sets by `∀ (r : ℕ) (y : Spec A), y ∈ U r ↔ f.fiberDegree y = r`.
  Natural numbers encode precisely the node's integers r ≥ 0.
- `∀ r, IsClopen (U r : Set (Spec A))` is the open-and-closed assertion.
  `Pairwise (fun r s : ℕ ↦ Disjoint (U r) (U s))` is pairwise disjointness.
  `iSup U = ⊤` is union equal to the target and `U 0 = ⊥` is the empty zero piece.
- The open subschemes are the existing coercions `Scheme.Opens.toScheme`.
  `IsAffineOpen (U r)` means that this very open subscheme is affine.
  `IsAffineOpen (f ⁻¹ᵁ U r)` states the same for the specified inverse image.
- `(f ∣_ U r).IsFiniteLocallyFreeOfDegree r` uses the existing canonical
  `morphismRestrict`, whose source is `(f ⁻¹ᵁ U r).toScheme` and target is
  `(U r).toScheme`. The recorded degree class includes finite locally free
  and fibre dimension exactly r, so no part of the restricted-morphism clause
  is omitted.
- For every r the existential `∃ (b : A) (b' : B)` and equations
  `b ^ 2 = b ∧ b' ^ 2 = b'` give the two idempotents. The equalities
  `U r = PrimeSpectrum.basicOpen b` and
  `f ⁻¹ᵁ U r = PrimeSpectrum.basicOpen b'` identify the actual open sets
  with the principal opens D(b) and D(b'). The underlying space of `Spec A`
  is definitionally `PrimeSpectrum A`, and similarly for B.
- The existential set `I : Set ℕ` is required to equal exactly
  `{r : ℕ | 1 ≤ r ∧ (U r : Set (Spec A)).Nonempty}`. It does not merely
  contain the nonempty ranks. `I.Finite` is finiteness of precisely this set.
- `Nonempty (IsColimit (Cofan.mk (Spec A) (fun r : I ↦ (U r.val).ι)))`
  states the scheme coproduct universal property with the specified open
  inclusions as coprojections. In particular this is the actual decomposition
  `Y = ∐_{r∈I} Y_r`, rather than an arbitrary isomorphism or a point-set-only
  partition. No coproduct or nonempty-index assumption is added.
- `IsEmpty (Spec A) → I = ∅` is the final empty-target implication.

Recorded dependency declarations were read with their full signatures/docstrings:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme` (the latter is the scheme morphism category).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-finite-locally-free`: `Scheme.Hom.IsFiniteLocallyFree` and
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`, in
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`. The same module's
  `fiberDegree`, `fiberAlgebra`, and `finrankΓ` supply the stated dimension.
- `def-weil-residue-field`: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`,
  in `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, and `pullback.lift`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. These are used
  by the existing `Scheme.Hom.fiber`/`fiberToSpecResidueField` in
  `Mathlib.AlgebraicGeometry.Fiber`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`; the corresponding open subschemes
  and inclusions are `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, and the
  canonical `morphismRestrict` in `Mathlib.AlgebraicGeometry.Restrict`.

These statement interfaces are available through the public imports of
`FiberDegree` and `Mathlib.AlgebraicGeometry.Limits`. The public spectrum topology
import supplies `PrimeSpectrum.basicOpen`. The proof-plan-only imports are
`WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`,
`Mathlib.AlgebraicGeometry.OpenImmersion`, `Mathlib.AlgebraicGeometry.AffineScheme`,
and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`. They respectively expose
`finiteLocallyFree_fiberDimension_isLocallyConstant`,
`Scheme.isOpenImmersion_SpecMap_localizationAway`,
`Scheme.compactSpace_of_isAffine`, and `quasiSeparatedSpace_of_isAffine`.
The clopen-idempotent proof dependency is
`PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` and
`PrimeSpectrum.isIdempotentElemEquivClopens` in
`Mathlib.RingTheory.Spectrum.Prime.Topology`, already needed publicly for basic opens.
All seven proof dependencies are represented by these imports or the statement
interfaces above; none is omitted for a cycle.

Source check: read Stacks `groupoids.tex`, labels
`lemma-finite-locally-free-disjoint-free` (03BI) and
`lemma-integral-over-invariants` (03BJ), including their proofs; read
`morphisms.tex` label `lemma-finite-locally-free` (04MH), `algebra.tex` label
`lemma-disjoint-decomposition` (00EE), and `schemes.tex` label
`lemma-standard-open-affine` (01I3). The node extracts the section argument
for positivity and the quasi-compact rank reduction; it does not claim the
additional groupoid-invariance assertions of 03BI.

Edge cases checked before writing:

- A the zero ring: `Spec A` is empty. Existence of f then forces the source
  empty as well. All U r and their inverse images can be empty affine schemes;
  every fibre-degree assertion is vacuous, all idempotents can be zero,
  I is empty, and the empty cofan has the empty scheme as its colimit.
- A field and `Spec (k^n) → Spec k` with a section, n ≥ 1: only rank n is
  nonempty and the corresponding idempotents are one; other pieces use zero.
- The identity, and more generally an isomorphism, has the single nonempty
  rank 1 when the target is nonempty. Positivity excludes a rank-zero fibre.
- Mixed ranks 1 and 2 over a two-component affine target give two elements
  of I. No connectedness or fixed-degree assumption was introduced.
- For every absent rank, including r = 0, both pieces are empty; degree r
  for an empty-target restriction is the correct vacuous class condition.
- The common universe u is arbitrary; natural-number and subtype indexing of
  the cofan do not impose a nonempty or finite-type instance as an assumption.

Searches (all before writing; prescribed `batch2/msearch.py Q98 <item>`):

- `leanfinder`, query `A finite locally free morphism of affine schemes with a
  section decomposes into finitely many clopen affine pieces of positive fibre
  rank`: eight hits, including `IsFinite.finite_app`, finite fibres, and
  affine-cover auxiliaries; none states this decomposition with its section,
  positivity, idempotents, and finite positive-rank index set.
- `loogle`, query `"IsFiniteLocallyFree", "rank"`: zero hits.
- `grep`, query
  `(finiteLocallyFree|finite_locally_free|IsFiniteLocallyFree).*(section|strat|rank)|rankAtStalk_pos_iff`:
  nine hits in Mathlib's FlatRank, FreeLocus, TotallySplit, and Flat/Rank;
  these are component rank-positivity facts, not the node's full statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, query
  `positive.*rank.*pieces|split.*morphism|rank.*strat`: unrelated splittings
  and derived rank-stratum statements; no exact match.
- `grep -rn` of this item's id in `lean/WeilConjectures`: no match.
- `rg` for `finiteLocallyFree.*positive.*rank|affine_split_morphism_positive_rank_pieces`
  across Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no declaration-name conflict or exact match.
- Direct source inspection of `FiberDegree` and
  `FiniteLocallyFreeDegreeLocallyConstant` confirmed reusable component
  interfaces and that the latter alone omits section positivity, affine
  pieces, idempotents, finite support, and the restricted positive-rank coproduct.

Validation: `scompile.py` compiled the file as a sandbox module and at its intended
library module path cleanly. A final compiler/preflight pass is run by `deliver2.py`.
No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q98

This dispatcher assignment explicitly forbids starting another agent. This section
records an author second pass; the maintainer's independent review remains separate.
I reopened the node, the final theorem signature, and the definitions of `fiberDegree`,
`IsFiniteLocallyFreeOfDegree`, `IsAffineOpen`, `morphismRestrict`, and open inclusion.
The clause correspondence above was checked against those sources. In particular,
I checked the direction of the section equation, the canonical residue-field action,
all nonnegative ranks including empty ones, both rings' idempotents, equality rather
than containment in the definition of I, the exact open inclusion cofan, and the
empty-target clause. No mismatch or statement correction was needed. The spectrum
topology import was made public because `basicOpen` occurs in the signature.
