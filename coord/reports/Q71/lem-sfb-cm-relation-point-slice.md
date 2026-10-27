## Worker report

The module `Sheaf.AlgebraicGeometry.CohenMacaulayRelationPointSlice` states
`AlgebraicGeometry.exists_cm_relation_point_slice`, with `sorry` as its entire proof.
No definition, helper theorem, dependency repair or statement correction is needed.
Only the assigned node's `lean` field changes. No mathematical statement is disputed.

Read the node, every statement dependency and its recorded declaration/docstring,
and the available proof-dependency interfaces. Read More on Groupoids, Situation
04MY and Lemmas 04MZ/04N0, in `literature/stacks-project/more-groupoids.tex`, including
04N0's proof and clauses (1)--(4). The node deliberately asserts only the slice and
saturation properties; the source also gives an immersion and restricted-groupoid
conclusions, which are not added to this statement. The prescribed CompactObject
example is now a withdrawn module with no declarations; the new file follows the
current module/public-import/expose convention and the nearby FlatRelationCMOpen
statement's sectionwise relation and depth-equals-dimension encodings.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Arbitrary base scheme and size convention: `{S : Scheme.{u}}`, with explicit
  `universe u`; there is no finiteness, Noetherianity or separation condition on S.
- S-schemes V and R: `{V R : Over S}`. Their S-morphisms are `(s t : R ⟶ V)`;
  compatibility with the structural maps is part of being a morphism in `Over S`.
- Injectivity of the relation map on every test S-scheme:
  `hinj : ∀ T : Over S, Function.Injective (fun r : T ⟶ R ↦ (r ≫ s, r ≫ t))`.
  Pairs of sections in `Over S` are exactly the sections of V ×_S V.
- Its image is an equivalence relation:
  `hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
  ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b)`.
  The two hypotheses together give the required identification with its image,
  without choosing identity, inverse or composition operations as additional data.
- Flatness of both projections: `[Flat s.left] [Flat t.left]`.
- Every local ring of every s-fibre is Noetherian and its depth equals its Krull
  dimension: `hcm_s` quantifies over every `v : V.left` and every
  `x : s.left.fiber v`, with `IsNoetherianRing` of the fibre stalk and the equality
  `(IsLocalRing.depth (R := stalk) stalk : WithBot ℕ∞) = ringKrullDim stalk`.
  `hcm_t` is the identical assertion for `t.left.fiber v`. The coercion merely
  compares the existing ENat-valued depth and WithBot-ENat-valued dimension.
- Local finite presentation of both projections:
  `[LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left]`.
- The given finite-type point is `(v : V.left)` with both
  `[LocallyOfFiniteType (V.left.fromSpecResidueField v)]` and
  `[QuasiCompact (V.left.fromSpecResidueField v)]`. This is exactly finite type
  of the canonical Spec κ(v) map, not finite type of V over S.
- The affine S-scheme, its S-map to V and its point are
  `∃ (A : Over S) (g : A ⟶ V) (a : A.left)` and `IsAffine A.left`.
  This is affineness of A as a scheme, not relative affineness of its structure map.
- Local finite presentation of g is `LocallyOfFinitePresentation g.left`.
- The prescribed image of the point is `g.left a = v`.
- The saturation is the actual scheme morphism
  `pullback.snd g.left t.left ≫ s.left`, with source A ×_{g,V,t} R.
  The three final conjuncts are its `Flat`, `LocallyOfFinitePresentation`, and
  `Scheme.Hom.IsLocallyQuasiFinite` properties, respectively. The last is precisely
  the recorded Stacks predicate, including the local finite-type condition.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`;
  `Mathlib.CategoryTheory.Comma.Over.Basic`: `CategoryTheory.Over`, its objects and
  morphisms, and their `.left` projections.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.snd`; scheme pullbacks are available
  through `Mathlib.AlgebraicGeometry.Fiber` and its imports.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`, the existing
  affineness predicate (an isomorphism to Spec of global sections).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth`, `IsLocalRing.depth`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite` and its `IsQuasiFiniteAtPoint` definition.

Available proof dependencies are plain imports: Mathlib Yoneda,
`Sheaf.AlgebraicGeometry.GroupoidScheme`,
`Sheaf.AlgebraicGeometry.GroupoidQuasiFiniteLocusDescent`,
`Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension`, and
`WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`.
The Mathlib affine-spectrum pullback comparison and local-finite-presentation
composition are already in the imports of the statement dependencies.
`lem-sfb-cm-groupoid-maximal-slice` has no Lean record or Mathlib match in the current
DAG; it is a proof-only prerequisite, so there is no unstated object in the signature
and no dependency module is needed to state this item. The complete five-step
natural-language proof is in the theorem docstring, retaining that prerequisite.

Edge cases checked before writing:

- Empty V has no v, so the point-indexed theorem makes no assertion in that case.
  Empty R with nonempty V is excluded by reflexivity on sections, as intended.
- No Noetherian condition on the base or V is inserted. Only the local rings of
  the actual scheme-theoretic fibres are required Noetherian.
- Stalks at points are nonzero local rings; coercing depth into `WithBot ℕ∞` does
  not exclude any legitimate zero-dimensional or positive-dimensional local ring.
  No finite-dimension bound was silently added; the equality includes infinite
  values. Empty fibres have no stalks, so their fibre-local conditions are vacuous.
- The identity relation is covered, with no positive-dimensional-fibre assumption.
- The finite-type condition applies to the canonical residue-field map, and both
  its finite-type conjuncts are present. No hypothesis on residue characteristic,
  algebraic closure or rationality is introduced.
- Tests range over all S-schemes in the same fixed scheme universe. No smaller
  independent test-object universe makes the relation hypotheses vacuous.
- A is affine as a scheme and carries its actual S-structure. g is an S-map.
  The projection order in the saturation is R first, then s, as in the node.

Searches for an existing statement or notion:

- `msearch.py ... leanfinder` with “An equivalence relation of schemes with Cohen
  Macaulay locally finitely presented projections admits an affine slice through a
  finite type point with flat locally finitely presented locally quasi finite
  saturation”: 8 hits, about affine properties, smooth charts and local finite
  presentation; none states the relation-slice result.
- `msearch.py ... leansearch` with “A Cohen Macaulay equivalence relation on a scheme
  admits an affine locally finitely presented slice with flat locally quasi finite
  saturation at a finite type point”: 8 hits, local quasi-finiteness, flatness and
  finite-presentation infrastructure only; no slice theorem.
- `msearch.py ... loogle 'Equivalence, Scheme'`: 0 hits; the tool reports that the
  unqualified identifier Scheme is unknown. Direct source searching below supplies
  the relevant relation API inspection rather than relying on that failed query.
- Repeated Loogle with qualified string filters `"AlgebraicGeometry.Scheme",
  "Equivalence"`: 3 hits (equivalence of rational partial maps and affine-etale
  site equivalences), none stating the slice theorem.
- `msearch.py ... grep '[Cc]ohen.?[Mm]acaulay|[Ee]quivalence[Rr]elation'
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` in Mathlib CategoryTheory found `EquivalenceRelation` and
  `IsEquivalenceRelation`, which are internal relation structures, not this slice
  theorem. The statement's sectionwise hypotheses are written directly as the node
  specifies, consistently with the existing `exists_flat_relation_cm_open` theorem;
  no new competing predicate is defined.
- `rg` in project `lean/Sheaf/AlgebraicGeometry` and
  `lean/WeilConjectures/AlgebraicGeometry` for CohenMacaulay/cohenMacaulay,
  equivalence-relation names and point_slice/pointSlice/exists.*relation.*slice
  found fibre-CM lemmas, FlatRelationCMOpen, and a groupoid hypersurface slice;
  none states this assertion. Searching the upstream-name index found no matching
  point-slice declaration. Searching `lean/WeilConjectures` for this blueprint id
  found none.

Validation: the prescribed `scompile.py Q71 lem-sfb-cm-relation-point-slice` compiled
both the sandbox and intended library-module names successfully, with no diagnostics
(2.1 s and 2.3 s). The delivery dry run also passed server preflight and compilation
(`OK (dry run)`, commit 89a7d849724). Every universe and variable is explicitly bound; no local notation,
private auxiliary definition, additional axiom or postponed data construction occurs.

## Second reading by Q71

A fresh self-check reopened the node and completed Lean file and matched every
hypothesis and conclusion as listed above. In particular it checked both CM
projections, all test S-schemes, the actual canonical finite-type-point map, the
S-structure of A and g, affineness rather than affine structure morphism, and all
three properties of the correctly ordered saturation map. It found no mismatch
and required no correction. This is a self-check, not a claim of an independent
agent review: the dispatcher explicitly forbids starting other agents, and the
maintainer's independent delivery review is separate.
