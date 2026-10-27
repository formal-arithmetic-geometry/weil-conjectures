## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAssassinContainmentConstructible` states
`AlgebraicGeometry.AlgebraicSpace.fibreAssassinContainment_locallyConstructible`,
with `sorry` as its entire proof, and defines the auxiliary set expression
`fibreAssassinContainmentLocus` with real data. Both declarations belong to this node
and are listed in `lean.declarations`. No new mathematical notion, dependency repair,
or statement correction is needed. Only the item's `lean` field changes.

Sources read: `literature/stacks-project/spaces-divisors.tex`,
`lemma-relative-assassin-constructible` (Tag 0CVV), and
`literature/stacks-project/morphisms.tex`, `lemma-constructible-containing-open`
(Tag 05LW). In particular, the parenthesis in the proof of 0CVV explicitly says
that the associated points of a fibre are exactly the fibre of the relative assassin.
This permits the containment set to be expressed on the existing total-space point
classes without constructing a second fibre-assassin interface.

Hypothesis and clause correspondence:

- The ambient base is precisely `Spec (CommRingCat.of (ULift.{u} ℤ))`. The explicit
  universe `u` allows every scheme universe covered by the size convention;
  `Point X.obj.obj` has its existing universe `u + 1`. No equality between separate
  site, scheme or point universes is imposed.
- The scheme base is `Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))` (the final
  parenthesis closes the binder in the actual Lean). Its underlying scheme is
  `Y.left`; `schemeSpace Y` is its canonical algebraic space.
- The algebraic-space source is `X : AlgebraicSpace (...)`, and the morphism is
  `f : X ⟶ schemeSpace Y`. Morphisms are the existing full-subcategory morphisms,
  whose `.hom.hom` are the natural transformations of presheaves.
- Finite presentation is `_hfp`: the conjunction of
  `MapIsLocallyOfFinitePresentation f`, `MapIsQuasiCompact f.hom.hom`, and
  `MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. This is exactly local finite
  presentation, quasi-compactness and quasi-compact diagonal, with no assumption
  of separatedness or quasi-compactness on Y itself.
- The quasi-coherent module is `M : X.QCoh`, using the existing full subcategory
  defined by `SheafOfModules.IsQuasicoherent`. Its finite presentation is `_hM :
  SheafOfModules.IsFinitePresentation M.obj`. Mathlib's predicate is local finite
  cokernel presentations of the unit module, exactly the stated finite-free
  presentations; it does not mean a presentation of global sections.
- An open subspace is represented by its source `W`, inclusion `j : W ⟶ X`, and
  `_hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`.
  This uses the existing scheme-test predicate, with no private open-immersion
  definition and no chosen atlas. Its point subset is the existing
  `pointImage j.hom.hom`.
- Relative quasi-compactness of the open is `_hW : MapIsQuasiCompact
  (j.hom.hom ≫ f.hom.hom)`, so it is the map W to Y that is quasi-compact.
  Quasi-compactness of j alone is neither substituted nor added.
- The existing `relativeAssassin Y f M.obj` is the union of scheme relative
  assassins over all representable etale charts. Scheme relative association
  uses the existing tensor pullback to the point's own fibre and stalk association.
  The helper selects the points ξ of that set satisfying
  `mapPoint f.hom.hom ξ = schemePointMap (𝟙 (yoneda.obj Y)) y` and requires them
  all to lie in `pointImage j.hom.hom`. This is exactly
  `Ass_(X_y)(M_y) ⊆ |W_y|`: the source's fibre identification, together with the
  point subset of the open inclusion, gives this containment on total-space
  point classes. No arbitrary map, fibre module or associated-point set is supplied
  as a hypothesis.
- The first conclusion is `∀ y : Y.left, ∃ V : Y.left.Opens, y ∈ V ∧
  IsAffineOpen V ∧ Topology.IsConstructible (...)`. The set in parentheses is
  `(Subtype.val : V → Y.left) ⁻¹' fibreAssassinContainmentLocus ...`, so its
  constructibility is in the subspace topology on |V|. This is the node's explicit
  affine-neighbourhood meaning of local constructibility, including schemes
  which are not quasi-separated globally.
- The second conclusion quantifies every `y : Y.left`. Its premise says that
  every `t` satisfying `y ∈ closure ({t} : Set Y.left)` lies in the locus; the
  specialization direction is therefore exactly the node's generalization
  convention. Its conclusion is `∃ V : Y.left.Opens, y ∈ V ∧
  (V : Set Y.left) ⊆ fibreAssassinContainmentLocus ...`. There is no extra
  requirement that this final neighbourhood be affine.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` and `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` and the sheaf fibre-product model.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh`; its exact Mathlib predicate is
  `SheafOfModules.IsQuasicoherent` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, where
  `SheafOfModules.IsFinitePresentation` is also defined.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicSpace.moduleTensorPullback` and its specified adjunction; used by
  the existing chart/fibre-module conventions rather than redefined here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocallyOfFinitePresentation`; its imported
  `ProperCurveModuli` supplies `MapIsQuasiCompact` and `mapPoint`.
- `Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity`:
  `AlgebraicSpace.relativeAssassin`; its imported `EnlargedEtaleRingedSite`
  supplies `AlgebraicSpace.schemeSpace`.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `Scheme.Modules.relativeAssassin` and `Scheme.Modules.associatedPoints`;
  these are the definitions used inside space relative association.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointImage` and `pointTopologicalSpace`; its existing
  point-class module supplies `Point` and `schemePointMap`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, exactly the
  recorded `mathlib_match` of `def-weil-constructible-subset`.
- `def-weil-size-convention` has the explicit metatheoretic convention record,
  not a declaration to import; it is rendered by explicit universe polymorphism.

All stated proof dependencies are imported privately, including flat/proper/fp
locality, affine quasi-compactness tests, quasi-compact fppf locality,
representable-etale scheme tests, affine chart calculus, the Zariski/etale module
comparison, the Mathlib affine/spectral facts and the upstream
`Topology.exists_mem_iInter_closure_singleton`. The main docstring reproduces all
seven proof steps with their DAG references. The following proof dependencies
have no Lean record or Mathlib match in the read repository, so no module is
invented for them: `lem-sfb-space-fp-qcqs-source`,
`lem-sfb-qc-space-affine-etale-atlas`, `lem-sfb-space-qcqs-permanence`,
`lem-sfb-space-separated-fp-composition`,
`lem-sfb-space-fibre-assassin-etale-atlas`, and
`lem-sfb-scheme-assassin-open-constructible`. None is needed to type this statement.

Edge cases checked before writing:

- Empty Y makes both conclusions vacuous and does not require a base point.
- Empty X or the zero module gives an empty relative assassin and the whole
  base as containment locus. The helper has the correct vacuous universal condition.
- W equal to X also gives the whole base; no nonemptiness or proper-open condition
  appears. For empty W, the predicate asks that the fibre assassin be empty,
  with no falsely assumed associated point on an empty/zero fibre.
- Identity and arbitrary open inclusions are allowed; the condition is on W to Y.
- A non-Noetherian, non-quasi-compact, or non-quasi-separated base scheme is
  allowed. Only affine neighbourhoods enter the constructibility conclusion.
- Generalizations include y itself since y lies in its own singleton closure;
  the neighbourhood premise therefore ensures y is in the locus.

Searches actually run using `msearch.py Q67
lem-sfb-space-assassin-containment-constructible`:

- `leanfinder`: "For a finitely presented algebraic space and module, the base
  points where all fibre associated points lie in a relatively quasi compact
  open form a locally constructible set". Eight hits: Chevalley image statements
  for schemes and prime spectra, constructible-set data, and basic
  constructibility lemmas. No relative-assassin containment statement.
- `loogle`: `Topology.IsConstructible, Topology.IsLocallyConstructible`.
  Five hits relating the two predicates, including the implication on a compact
  prespectral quasi-separated space; none is the assigned theorem.
- `grep`: `assassin|associatedPoints`, subdirectory `AlgebraicGeometry` of
  Mathlib. Zero hits.
- `leansearch`: "The locus where all associated points of a fibre lie in an open
  subspace is locally constructible". Eight hits on `Topology.IsConstructible`,
  `Topology.IsLocallyConstructible`, and their open-cover/retrocompact lemmas;
  none states fibre-assassin constructibility.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for assassin,
  associatedPoints, containment/constructible combinations, and the planned
  helper name: existing scheme and space association definitions, base-change
  and spreading statements, but no theorem stating this item. The prescribed
  `grep -rn` of the exact item id under `lean/WeilConjectures` had no hits.
  `dag/lean_names_upstream.json` had no matching containment-constructibility
  declaration. The existing definitions are reused, not restated.

No STATEMENT-DISPUTED issue or source mismatch was found. No theorem is proved.
The sole postponed theorem is the assigned node's main declaration.

Validation: `scompile.py Q67 lem-sfb-space-assassin-containment-constructible
<module path>` succeeded both as sandbox module (33.8 s) and as its final library
module (5.2 s), with no diagnostics. Every variable/universe is explicitly bound;
`autoImplicit` is false. No local notation, private definition, local instance,
statement-level `let`, hollow data, or extra hypothesis is introduced.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
