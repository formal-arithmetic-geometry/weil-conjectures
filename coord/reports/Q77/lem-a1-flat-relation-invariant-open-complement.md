## Worker report

The module `Sheaf.AlgebraicGeometry.FlatRelationInvariantOpenComplement` states
`AlgebraicGeometry.flat_relation_invariant_open_complement`, with its sole proof `sorry`.
It introduces no definitions. The source is Stacks Project, `groupoids.tex`, Tag 0APB,
proof of `lemma-second-observation`, read in the local literature source. The six-step
proof docstring preserves all of the node's proof steps and names their dependencies.
The node is unchanged except for `lean`; no statement correction or dispute is needed.

Hypothesis-by-hypothesis correspondence:

- Schemes `R,V`: `{R V : Scheme.{u}}`; the universe `u` is declared explicitly.
- Source and target morphisms: `(s t : R ⟶ V)`.
- Both are flat: `[Flat s] [Flat t]`.
- Both are affine: `[IsAffineHom s] [IsAffineHom t]`.
- The common section: `(e : V ⟶ R)` with `hes : e ≫ s = 𝟙 V` and
  `het : e ≫ t = 𝟙 V`. Category composition is written in diagrammatic order.
- Saturation of every subset is invariant: `hsat` quantifies over every `A : Set V`,
  requiring `s ⁻¹' (t '' (s ⁻¹' A)) = t ⁻¹' (t '' (s ⁻¹' A))`.
  Here `t '' (s ⁻¹' A)` is exactly sigma(A); no new notion is required.
- The quasi-compact open `H`: `(H : V.Opens) [CompactSpace H]`.
  The bundled open supplies openness; `CompactSpace` is on the subtype topology,
  with no Hausdorff requirement. It is equivalent to compactness of `(H : Set V)`.
- The subset inside `H`: `(K : Set V)` with `hKH : K ⊆ (H : Set V)`.
- Invariance of `K`: `hK : s ⁻¹' K = t ⁻¹' K`.
- Stability under generalization: `hgen : StableUnderGeneralization K`.
  The Mathlib definition is `∀ ⦃x y⦄, y ⤳ x → x ∈ K → y ∈ K`, and
  `specializes_iff_mem_closure` identifies `y ⤳ x` with `x ∈ closure {y}`.
  This is the node's direction of generalization, with no reversal.

For the conclusions, expand `Z` as `(H : Set V)ᶜ`, `T` as
`t '' (s ⁻¹' (H : Set V)ᶜ)`, `B` as the closure of this image, and `W` as its
complement. These are literal expressions, without opaque helpers or `let` binders.
The nine successive conjuncts say:

1. `Z ⊆ T`.
2. `K ∩ T = ∅`.
3. `∀ y ∈ B, ∃ y' ∈ T, y ∈ closure ({y'} : Set V)`.
4. `s ⁻¹' B = t ⁻¹' B`.
5. `K ∩ B = ∅`.
6. `IsOpen W`.
7. `s ⁻¹' W = t ⁻¹' W`.
8. `K ⊆ W`.
9. `W ⊆ (H : Set V)`.

All hypotheses and clauses are retained, including quasi-compactness of `H` (unused
in the mathematical proof but part of the node), both affine hypotheses, and the
specialization assertion for every point of the closure. No groupoid multiplication,
inverse, finite presentation, separation or Noetherian hypothesis is added.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Opens` for `def-pc-scheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, whose
  `iff_flat_stalkMap` identifies the affine-pair interface with stalkwise flatness,
  for `def-weil-flat-morphism`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`,
  requiring affine preimages of every affine open, for `pqf-def-affine-morphism`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, for
  `def-weil-pbc-quasi-compact-scheme`, applied to the open subtype.
- `Mathlib.Topology.Inseparable`: `StableUnderGeneralization` and its specialization
  convention, reused rather than redefined.

All stated proof dependencies are imported privately, using their existing attachments:
`Scheme.IdealSheafData.subschemeι` from `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`;
`Scheme.compactSpace_of_isAffine` from `Mathlib.AlgebraicGeometry.AffineScheme` and
`quasiSeparatedSpace_of_isAffine` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`;
`IsClosedImmersion` from `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`;
`IsClosed.isCompact` from `Mathlib.Topology.Compactness.Compact`;
`LocallyOfFiniteType` and the transitively imported `QuasiCompact` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`;
`exists_specializes_of_mem_closure_range` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`;
and `Flat.generalizingMap` from `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.
Their signatures and docstrings were read; no dependency module is needed.

Edge cases checked mathematically before writing:

- `V` empty: every set is empty; the map `R → V` also forces `R` empty.
- `H = V`: `Z = T = B = ∅`, and `W = V`.
- `H = ∅`: `K = ∅`, while the section gives `T = V`, hence `B = V`, `W = ∅`.
- `K = ∅`: disjointness and its inclusion in the complement hold vacuously.
- Identity relation: `R = V`, `s = t = e = id`; `T = Z` is already closed,
  so `B = Z` and `W = H`. Closure points specialize from themselves.
- The argument uses quasi-compactness, never compact Hausdorffness; arbitrary
  nonseparated and non-Noetherian schemes remain allowed.

Searches (prescribed `msearch.py`, group Q77, this item):

- LeanFinder query: “For flat affine scheme source and target maps the closure of a
  saturated closed complement is invariant and misses every invariant generalization
  stable subset of the open”. Eight results, including `Flat.generalizingMap`,
  `Scheme.Hom.coborderRange`, `map_vanishingIdeal`, and `Scheme.Hom.support_ker`;
  none states this theorem.
- Loogle query: `AlgebraicGeometry.Flat, closure`. Zero results.
- Mathlib grep query: `invariant.*closure|closure.*invariant|saturat.*[Cc]losed`,
  subdirectory `AlgebraicGeometry`. Zero results.
- LeanSearch query: “The open complement of the closure of the saturation of a closed
  subset under a flat affine relation is invariant and contains any disjoint invariant
  subset stable under generalization”. Eight results: complements of opens/closeds,
  `IsOpen.stableUnderGeneralization`, `StableUnderSpecialization.compl`,
  `StableUnderGeneralization.compl`, `stableUnderGeneralization_iff_exists_sInter_eq`,
  and `stableUnderSpecialization_compl_iff`. No whole-statement match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` using the same grep expression and
  this node id found only unrelated invariant algebraic closures, group invariants,
  saturated categories, and monoid algebras. No matching declaration or node attachment.
- `rg` for `flat_relation_invariant_open_complement` in both Lean trees and
  `dag/lean_names_upstream.json`: no collision.

Validation: the initial module compiled cleanly in sandbox and library mode via
`scompile.py`; the final module additionally disables auto-implicit parameters.
Final per-file compilation and server preflight are performed by `deliver2.py`.

## Second reading by Q77

No second reading by a worker: this dispatch requires direct delivery without other
agents. The maintainer's independent review is the only independent review.
A final self-check reread the node against the signature, especially the direction
of singleton-closure specialization, the two section equalities, and all nine conjuncts;
no mismatch was found and no correction was made.
