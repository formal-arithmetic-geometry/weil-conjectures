## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricConnectedComponentSurjective` states
`AlgebraicGeometry.Scheme.geometric_connected_component_surjective`. Its only proof
is `sorry`; no definitions or additional lemmas are introduced. The node is unchanged
apart from its `lean` attachment.

Hypotheses and clauses, matched individually:

- The field is `(k : Type u) [Field k]`.
- An arbitrary algebraic closure is `(K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K]`; this is not restricted to Mathlib's chosen closure.
- The scheme over k is `(X : Scheme.{u})` with its specified structure map
  `f : X ⟶ Spec (CommRingCat.of k)`.
- Nonemptiness and connectedness are exactly `[ConnectedSpace X]`; the recorded
  connectedness definition already includes nonemptiness.
- Local finite type is `[LocallyOfFiniteType f]`, with no quasi-compactness assumption.
- Finiteness of irreducible components is
  `hcomponents : (irreducibleComponents X).Finite`.
- Write W for the actual term `pullback f
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))` (the prose W is only explanatory).
  The exact reduction term in the statement is `W.nilradical.subscheme`, denoted Z
  in this report. There is no alternate construction or arbitrary comparison map.
- The first conjunct `(irreducibleComponents Z).Finite` asserts the finiteness for Z.
- The second conjunct `Nonempty Z` asserts existence of a nonempty component:
  every point z belongs to its connected component. Conversely a nonempty component
  supplies a point of Z.
- Every component is covered by `∀ z : Z, ∃ U : Z.Opens,
  (U : Set _) = connectedComponent z ∧ ...`. Mathlib's `connectedComponent z` is
  the maximal connected subset containing z; every maximal nonempty connected
  subset equals this one for any point it contains. Hence this quantification
  loses no component and introduces no connectedness hypothesis on the component.
- Openness is the actual open-subset datum `U : Z.Opens`; closedness is
  `IsClosed (U : Set Z)`. The equality identifies that datum with the component.
- Its open subscheme structure is `U.toScheme`, with canonical inclusion `U.ι`.
- Nonempty and connected are `ConnectedSpace U.toScheme`, which includes both.
- Reducedness is `IsReduced U.toScheme`.
- Local finite type over K is `LocallyOfFiniteType
  (U.ι ≫ W.nilradical.subschemeι ≫ pullback.snd f (Spec.map ...))`.
  The second projection is the specified K-structure map.
- Finiteness of its irreducible components is
  `(irreducibleComponents U.toScheme).Finite`.
- Surjectivity onto X is `Surjective
  (U.ι ≫ W.nilradical.subschemeι ≫ pullback.fst f (Spec.map ...))`.
  This is exactly the inclusion, reduction immersion, and first projection.

Dependency declarations read and used (all statement dependencies are Mathlib notions):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`, supplying precisely an
  algebraic algebraically closed field extension.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; scheme pullbacks use Mathlib's canonical limit.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.nilradical`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.IdealSheafData.subscheme`, `Scheme.IdealSheafData.subschemeι`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`
  provide the already recorded scheme node's open subscheme notion.

Proof imports include the recorded upstream
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme` and Mathlib's
surjective base-change, closed-immersion, integral, universally-open, proper,
and localization modules. The finite-preimage proof dependency has no recorded
module and is not restated here. The docstring carries all five proof steps.

Sources inspected: local `literature/stacks-project/varieties.tex`, the first proof
paragraph of Tag 04L7 (lines 5363 onward), Tag 04KZ (3) (line 1812 onward), and
Tag 038H (line 1524 onward). The node extracts the geometric component argument;
reducedness of X is used later in 04L7 for injectivity of sections and is not
required for this node's conclusion. No statement correction is needed.

Edge cases checked: the empty scheme is excluded exactly by `ConnectedSpace`;
the case k already algebraically closed is included; finite separable field
spectra can split into several geometric points and each point still surjects;
purely inseparable extensions and nonreduced X are included by reduction, with
no perfectness assumption; connected locally finite type schemes need not be
quasi-compact, so no `CompactSpace` or `QuasiCompact` assumption is present.
The zero-component case is excluded by nonemptiness, rather than an added
finiteness or positivity assumption. The universe u is explicit throughout.

Searches actually run through msearch.py, Q151, this item:

- LeanFinder: “Every connected component of the reduced algebraic closure base
  change of a connected locally finite type scheme with finitely many irreducible
  components is clopen and surjects onto the scheme”. Eight hits, including
  `finite_appTop_of_universallyClosed`, pointsPi surjectivity, and affine-space
  surjectivity; none states this result.
- LeanSearch: “A connected component of the reduced base change to an algebraic
  closure is open closed and surjective over a connected locally finite type
  scheme”. Eight hits: general clopen-component lemmas, surjective base-change
  stability, geometrically reduced rings, and closed/open immersion facts; no
  full match.
- Loogle: `AlgebraicGeometry, connectedComponent, Surjective` returned unknown
  identifier AlgebraicGeometry. Corrected query `"AlgebraicGeometry",
  "connectedComponent"` returned `Scheme.Hom.connectedComponentsHomeomorph`
  and its evaluation lemma. Read their source: they require geometrically
  connected fibers and do not assert this node.
- Mathlib grep: `connectedComponent|geometric.*[Cc]omponent` in AlgebraicGeometry
  returned nine hits, the preceding component homeomorphism and unrelated
  constant-sheaf/geometrically-reduced material; no exact match.
- Direct rg of `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for the same pattern found curve decompositions,
  fiber component results, and generic component splitting. No exact match.
  Follow-up rg of both full source roots for the prospective declaration and
  geometric-component-surjectivity patterns found only unrelated incidence
  prose and the consumer `RelativelyClosedConstantsUnitsFG` docstring.
  Searching `lem-sfb-geometric-connected-component-surjective` in
  `lean/WeilConjectures` found no declaration.

Validation: the required scompile.py server compile and deliver2.py dry run are
performed for this module. Expected sorry warnings alone are accepted.

## Second reading by Q151

Self-check of the finished node and module; the maintainer supplies the independent
review, as required by this dispatcher's brief. The two projections were checked
separately: snd gives the K-structure and fst gives the map onto X. Checked that
connectedness entails nonemptiness in both occurrences; that the existential
open datum represents every component by its carrier equality; and that finiteness
is asserted separately for Z and for each component. The reduction is the recorded
nilradical construction and no component is replaced by an arbitrary subscheme.
No mismatch, disputed statement, or dependency repair was found.
