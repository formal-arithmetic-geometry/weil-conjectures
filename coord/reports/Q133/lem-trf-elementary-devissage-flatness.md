## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.elementary_devissage_flatness` in
`Sheaf.TraceFormula.ElementaryDevissageFlatness`. Its only theorem has proof `by sorry`;
there are no new definitions or helper theorems. The node changes only in `lean`.

I read Stacks `flat.tex`, `lemma-devissage-flat` (057U), both its neighbourhood and stalk
assertions and its proof, together with `lemma-elementary-devissage` (057S), whose diagram
and data it assumes. The Lean follows the already recorded elementary-module-devissage
interface and retains every hypothesis of this node. In particular it does not assume
`LocallyOfFinitePresentation f`. No statement correction or disputed assertion is needed.

Hypothesis-by-hypothesis translation:

- Schemes and the locally finite-type morphism are `{X S : Scheme.{u}}`, `f : X ⟶ S`,
  and `[LocallyOfFiniteType f]`. All other schemes have the same unrestricted scheme
  universe `u`, as in the dependency declaration; every variable and universe is bound.
- The finite-type quasi-coherent module is `F : X.Modules` with
  `_hF : F.IsQuasiCoherentFiniteType`. This is the recorded predicate, literally
  `SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFiniteType F`, not coherence or
  finite presentation.
- `s` is represented by `f x`. The fibre is `f.fiber (f x)`, definitionally the pullback
  of `f` along `S.fromSpecResidueField (f x)`, with projection `f.fiberι (f x)`.
  The fibre module is `(tensorPullback (f.fiberι (f x))).obj F`. The marked point is
  `f.asFiber x`. The hypothesis `hx` says its stalk is not subsingleton, exactly membership
  in the support of the fibre module.
- `n : ℕ` and `_hn` identify `(n : WithBot ℕ∞)` with `topologicalKrullDimAt` of the point
  `⟨f.asFiber x, hx⟩` in the support subtype. The topology on that subtype is the subspace
  topology, so this is local dimension of the support, not dimension of the whole fibre
  or of the closure of the point.
- `X' Z' Y' S'`, the six maps `g e f' i π h`, points `x' s' z'`, and `G : Z'.Modules`
  are all explicit binders. `y'` is written as `π z'` throughout, exactly its definition.
- The elementary pointed neighbourhoods are `[Etale g]`, `[Etale e]`, `_hg : g x' = x`,
  `_he : e s' = f x`, and the two `IsIso` hypotheses on `g.residueFieldMap x'` and
  `e.residueFieldMap s'`. These are the induced residue maps, not arbitrary field
  isomorphisms.
- `_hfg : g ≫ f = f' ≫ e` renders `fg = ef'`. The assertion that the finite map is
  over `S'` is `_hπ : i ≫ f' = π ≫ h`, the second square of the 057S diagram and of
  the recorded dependency declaration; this introduces no extra geometric restriction.
- Affineness is `[IsAffine X'] [IsAffine Z'] [IsAffine Y'] [IsAffine S']`.
- The finitely presented closed immersion is `[IsClosedImmersion i]` together with
  `[LocallyOfFinitePresentation i] [QuasiCompact i] [QuasiSeparated i]`. These are the
  three parts of finite presentation recorded by def-sbc-locally-finite-presentation.
- Finiteness is `[IsFinite π]`; the module hypothesis is
  `_hG : G.IsQuasiCoherentFiniteType`, with the same exact finite-type interpretation.
- `_hiso : Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F)` is the assertion
  that the two indicated module sheaves are isomorphic. It is only a hypothesis asserting
  existence of the node's isomorphism, not a choice used to define any construction.
- `[SmoothOfRelativeDimension n h]` and `[GeometricallyIntegral h]` render the stated
  smoothness and geometric integrality of all fibres. The latter is Mathlib's existing
  predicate, integral after every field-valued base change.
- `_hi : i z' = x'` and `_hs : h (π z') = s'` are the marked point equations.
  `_hfibre : (π ⁻¹' ({π z'} : Set Y')) = {z'}` is exactly the singleton set-theoretic
  fibre hypothesis, not a stronger scheme-theoretic fibre assertion.
- `_hpure` uses `Algebra.IsPurelyTranscendentalExtension` with the canonical algebra
  structure `(h.residueFieldMap (π z')).hom.toAlgebra`. Its base is written as
  `S'.residueField (h (π z'))`, identified with `κ(s')` by `_hs`. No arbitrary algebra
  structure is assumed, and no `let` occurs in the signature.

Clause-by-clause translation:

- The first conclusion is `(1 ↔ 2)` for neighbourhood flatness, the second is `(2 ↔ 3)`;
  their conjunction asserts precisely the equivalence of the three conditions of 057U.
  Condition (1) is an open `U : X.Opens` with `x ∈ U` and
  `((tensorPullback U.ι).obj F).IsFlatOver (U.ι ≫ f)`.
  Condition (2) is the corresponding open `U : Z'.Opens` containing `z'`, with
  `((tensorPullback U.ι).obj G).IsFlatOver (U.ι ≫ π ≫ h)`.
  Condition (3) is an open `U : Y'.Opens` containing `π z'`, with the tensor restriction
  of `(pushforward π).obj G` flat over the base through `U.ι ≫ h`.
  Pullback along an open inclusion is restriction, so these are the actual module
  restrictions on scheme opens. `IsFlatOver` is exactly the recorded affine-section
  definition. The map through `π ≫ h` equals the map through `i ≫ f'` by `_hπ`.
- The third conclusion is `(a ↔ b)` and the fourth is `(b ↔ c)`, separately from the
  neighbourhood assertions. Each stalk is the object given by
  `RingedSpace.moduleStalkFunctor`. Its scalar action over the base ring is explicit
  through `ModuleCat.restrictScalars` along `f.stalkMap x`, `(π ≫ h).stalkMap z'`,
  or `h.stalkMap (π z')`, respectively. The ring for (a) is
  `S.presheaf.stalk (f x)`. The rings for (b) and (c) are
  `S'.presheaf.stalk ((π ≫ h) z')` and `S'.presheaf.stalk (h (π z'))`;
  the points agree definitionally and equal `s'` by `_hs`. Thus no stalk is tested
  for flatness over its own source local ring in place of the base local ring.
- No equivalence between stalk flatness and the existence of a flat neighbourhood
  is asserted. These are the two distinct equivalence chains of the source.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms and
  `Spec`; `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`; the finite-type constituent is
  `SheafOfModules.IsFiniteType` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, as used by the imported
  `GeometricallyIntegral` predicate in `Mathlib.AlgebraicGeometry.Geometrically.Integral`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its
  projections, used by Mathlib's `Scheme.Hom.fiber` and `fiberι` in
  `Mathlib.AlgebraicGeometry.Fiber`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded normalized
  adjunction interface and its public import of
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, whose `tensorPullback` is the
  actual tensor construction. I read the current upstream source through
  `scompile.py --source WeilConjectures.AlgebraicGeometry.TensorPullback` because the
  older local checkout does not contain this module. No pullback is redefined.
- `Sheaf.FieldTheory.PurelyTranscendentalExtension`:
  `Algebra.IsPurelyTranscendentalExtension`.
- `Sheaf.TraceFormula.ElementaryModuleDevissage`:
  `Scheme.Modules.exists_elementary_module_devissage`; its full signature and docstring
  supply the convention for the support, dimension, canonical residue maps, diagram,
  and geometric predicates. This lemma guarantees existence of data; the present
  statement applies to any data satisfying those same conditions.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, read with its affine-section definition and stalkwise
  interpretation; `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, read using `scompile.py --source`.

The recorded modules of the stated proof dependencies are imported without `public`:
`AffineCoverModuleTensorFlatCriterion`, `EtaleLocalRingFlatness`,
`RelativeFlatnessSourceCover`, upstream `AffinePushforwardBaseChange`, upstream
`ClosedPushforwardStalks`, Mathlib `Morphisms.UniversallyOpen`, upstream
`Mathlib.AlgebraicGeometry.Modules.Tilde`, and Mathlib `Morphisms.Affine`.
Statement/proof dependencies shared by both lists use the public imports.
`lem-trf-finite-singleton-fibre-localization` has no Lean record or Mathlib match on
this base, so there is no module to import for that proof-only prerequisite. It is
named explicitly in the proof docstring. It is not needed to type this statement.

Edge cases checked before writing:

- The support hypothesis deliberately excludes the zero fibre stalk and empty schemes
  with no marked points, as the node itself does. No extra nonemptiness hypotheses occur.
- `n = 0` is permitted. There is no positive dimension assumption.
- Neither source nor target is required Noetherian, and `f` need only be locally finite
  type. Finite presentation is required solely for the given closed immersion `i`.
- The empty transcendence basis is allowed by the recorded predicate, so trivial residue
  extensions and identity elementary neighbourhoods are retained. No characteristic
  restriction or finite transcendence basis is imposed.
- Opens in the conclusions are arbitrary opens containing the marked point; no affine
  neighbourhood restriction strengthens the conclusion. Stalk and neighbourhood
  assertions are kept separate: stalk flatness alone is not claimed open.
- All zero stalks away from the closed image remain permitted in the neighbourhood
  comparisons; the proof plan uses flatness of zero there.
- The singleton fibre hypothesis concerns only the marked fibre of `π`, not other fibres.
- Scheme universe `u` is arbitrary, and no extra equality of distinct site universes is
  introduced. The modules use the dependency's ordinary `X.Modules` convention.

Searches for an existing statement (all four remote searches used `msearch.py`):

- LeanFinder query: "Relative flatness of a quasi coherent module equivalent under
  elementary etale devissage and finite pushforward with singleton fibre". Eight hits,
  including `RingHom.Flat.propertyIsLocal`, `AlgebraicGeometry.Flat.iff_flat_stalkMap`,
  and `Algebra.FormallyUnramified.flat_of_restrictScalars`; none is this module-sheaf
  equivalence with the given geometric data and both conclusion chains.
- Loogle query: `Module.Flat, AlgebraicGeometry.Etale`. Zero hits.
- Mathlib grep query: `devissage|devissage_flat|devissageFlat`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- LeanSearch query: "relative flatness equivalent under elementary etale devissage and
  finite pushforward with singleton fibre". Eight hits, including
  `Module.Flat.of_isLocalizedModule`, `Module.Flat.of_flat_tensorProduct`, and
  `AlgebraicGeometry.Flat`; none states this theorem.
- `rg` in the read-only upstream `WeilConjectures` and shared `lean/Sheaf` trees for
  `devissage|Devissage|devissage_flat|lem-trf-elementary-devissage-flatness` finds the
  existing elementary-module existence statement, the finite-presentation sibling,
  other unrelated devissage results, and proof references to this item in
  `FiniteTypeFlatEtaleNeighborhood`. There is no existing flatness statement.
- Exact-name search for `elementary_devissage_flatness|elementaryDevissageFlatness` in
  the upstream tree, shared `lean/Sheaf`, and `dag/lean_names_upstream.json` has no hits.
  Searching the upstream tree for the exact node id also has no hits.

Validation: the prescribed `scompile.py Q133 lem-trf-elementary-devissage-flatness`
compiled this file cleanly as both sandbox and library module, with no errors or
warnings. A final read against 057S/057U and the dependency module found no hypothesis
or clause mismatch. The two equivalence chains have been checked separately, and the
JSON `lean.statement` is extracted verbatim from the declaration signature.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
