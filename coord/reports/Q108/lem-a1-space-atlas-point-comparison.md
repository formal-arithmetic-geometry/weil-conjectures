## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceAtlasPointComparison` states
`AlgebraicGeometry.AlgebraicSpace.exists_atlas_point_comparison`, with a single
`sorry` proof. It introduces no definitions. The node is unchanged except for `lean`.
The statement follows the common-presentation argument of Stacks 03BX and the
point-pair lifting argument of Stacks 03H4, read in `spaces-properties.tex`.

Hypotheses and clauses, matched individually:

- The base scheme is `{S : Scheme.{u}}`; the algebraic space over it is
  `(E : AlgebraicSpace S)`.
- All schemes and arrows are over `S`: `(W V : Over S)` and the existential
  `(Q : Over S) (a : Q ⟶ W) (b : Q ⟶ V)` retain those base structures.
  The explicit universe `u` is the universe of the existing algebraic-space framework;
  its point-class type is `Type (u + 1)`. There is no independent restrictive universe.
- `w : yoneda.obj W ⟶ E.obj.obj` and `p : yoneda.obj V ⟶ E.obj.obj` are exactly
  the two scheme-source natural transformations.
- Their representable étale hypotheses are `hw : IsEtale w` and `hp : IsEtale p`.
  These definitions include scheme-test representability. Their representable
  surjectivity hypotheses are `hsw : IsSurjective w` and `hsp : IsSurjective p`.
  No extra representability assumption or choice of atlas data is needed.
- The existence of the representing fibre-product scheme is the existential `Q`
  with `IsPullback (yoneda.map a) (yoneda.map b) w p`. This is the universal
  property in the category of presheaves; since all objects here are sheaves,
  it is also precisely the sheaf fibre product. It does not assume a scheme
  fibre product over the nonschematic target.
- Both projections are explicitly étale and surjective through `Etale a.left`,
  `Surjective a.left`, `Etale b.left`, and `Surjective b.left`.
- Their continuity and openness are explicit: `Continuous a.left`, `IsOpenMap a.left`,
  `Continuous b.left`, and `IsOpenMap b.left`.
- Every equal-image pair is lifted by the quantified `x : W.left`, `y : V.left`,
  hypothesis `schemePointMap w x = schemePointMap p y`, and conclusion
  `∃ z : Q.left, a.left z = x ∧ b.left z = y`. Uniqueness is not asserted.
- Every subset of the algebraic-space point set is covered by
  `∀ A : Set (Point E.obj.obj)`.
- The first displayed identity is
  `a.left '' (b.left ⁻¹' (schemePointMap p ⁻¹' A)) = schemePointMap w ⁻¹' A`.
- The second displayed identity is
  `b.left '' (a.left ⁻¹' (schemePointMap w ⁻¹' A)) = schemePointMap p ⁻¹' A`.
- The final equivalence is
  `IsOpen (schemePointMap w ⁻¹' A) ↔ IsOpen (schemePointMap p ⁻¹' A)`.
  All topology occurrences concern scheme point types. No topology or continuity
  hypothesis on `Point E.obj.obj` is introduced.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, used through `Over S` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsEtale`, and
  `AlgebraicGeometry.AlgebraicSpace.IsSurjective`. Their full definitions were read:
  they use representing pullback squares with scheme-test projections.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`:
  `AlgebraicGeometry.AlgebraicSpace.Point`, `PointRepresentative.Rel`, and
  `schemePointMap`. The latter uses the actual residue-field point; no replacement
  equivalence relation or private map is introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `def-weil-size-convention` is the existing metatheoretic convention and has no
  declaration or module to import; its size choices are rendered by explicit `u`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` supplies scheme surjectivity.
- Proof-only imports retain the already-stated proof dependencies:
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`, with
  `AlgebraicGeometry.Scheme.Hom.isOpenMap`, and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint`, with
  `AlgebraicGeometry.AlgebraicSpace.exists_scheme_fibreProduct_point`.
  The latter signature expands the common-field equality condition. For its eventual
  use, equality of the quotient classes here is translated to that condition using
  the relation in `AlgebraicSpacePointClasses`; this is the same common-field argument
  in Stacks 03H4. No unusable statement interface is used as an assumption.

Edge cases checked mathematically before writing: the empty algebraic space and
empty atlases give an empty representing scheme and vacuous pair lifting; `A = ∅`
and `A = Set.univ` give the empty and full scheme subsets in both identities;
identity atlases and the fold atlas `V ⨿ V → V` satisfy the same comparisons.
Pair lifting asserts existence only, allowing several fibre-product points over one
pair (for example residue-field tensor products that split). No nonemptiness,
affineness, separatedness, finiteness or field-characteristic hypothesis is added.
There is no statement dispute or required source correction.

Searches performed with the prescribed `msearch.py` (all successful):

- LeanSearch: "Two surjective etale scheme atlases of an algebraic space detect
  the same open subsets by a common fibre product". Eight hits, including
  `Scheme.smallEtaleTopology`, `IsOpenImmersion.opensEquiv` and scheme covering
  results; none states this algebraic-space common-atlas point comparison.
- LeanFinder: "Two surjective etale atlases of an algebraic space have a scheme
  fibre product, lift pairs of points with equal class, and detect the same open
  subsets". Eight hits on scheme étale sites, scheme covers and ring presentations;
  none is this statement.
- Loogle: `"IsPullback", "IsOpen"`. Four hits on scheme open immersions and ideal
  sheaves; none has an algebraic-space target or the two atlas comparisons.
- Mathlib grep: `AlgebraicSpace|atlas.*point.*comparison`. No hits.
- Direct project searches: `rg` for `AlgebraicSpace|atlasPoint|atlas_point` in
  `lean/WeilConjectures` and `grep -rn` for this node id there give no match.
  `rg` for `AtlasPoint|atlas_point|atlas.*comparison|schemePointMap` in
  `lean/Sheaf/AlgebraicGeometry` finds existing point maps, topology definitions,
  affine-cover theorems and unrelated atlas comparisons, but no exact statement.
  Exact-name search for `atlas_point_comparison|atlasPointComparison` in Mathlib,
  the upstream-name index, `lean/Sheaf`, and `lean/WeilConjectures` gives no match.
  The existing algebraic-space and point-class modules are reused.

Validation: the prescribed `scompile.py Q108 lem-a1-space-atlas-point-comparison`
compiled this module in sandbox and library modes, with no errors or warnings.
Every binder and universe is explicit, the proof is `sorry`, and the declaration
and module docstrings name the source and blueprint node. The theorem docstring
records all five natural-language proof steps. No new nodes or dependency repairs
are included. Independent review is left to the maintainer, as instructed by the
remote-worker brief.

## Second reading by Q108

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
