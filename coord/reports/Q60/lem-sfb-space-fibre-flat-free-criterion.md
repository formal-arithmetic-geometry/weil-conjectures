## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreFlatFreeCriterion` states
`AlgebraicGeometry.AlgebraicSpace.finiteFree_near_iff_representativeFibre_flat`.
Its only postponed proof is this theorem, with the complete three-step DAG proof
in its docstring. No theorem is proved in this delivery. Five auxiliary definitions
construct exactly the objects introduced by the item: the Yoneda morphism of a
field-valued representative, its field fibre, the projection to X, the tautological
section (ξ,id), and its point class. Their data are explicit; the algebraic-space
property of the sheaf pullback uses the existing fibre-product theorem. These are
helpers of this item's own statement, as authorized by the launcher brief, rather
than independent replacement notions or arbitrary choices.

The statement is unchanged. Three already-landed definition nodes are added to
stmt_deps to name the existing constructions explicitly used here:
`def-trf-scheme-algebraic-space`, `def-trf-space-module-scheme-restriction`, and
`def-pc-module-stalk-functor`. There are no new nodes and no dependency repairs.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; the two spaces are
  `{X Y : AlgebraicSpace S}`, with the recorded fppf-sheaf/atlas definition.
- The morphism is `(f : X ⟶ Y)`, and local finite presentation on every compatible
  pair of étale charts is `(hf : MapIsLocallyOfFinitePresentation f)`. No flatness
  of f itself, separatedness, or global finite presentation is imposed.
- `(M : X.QCoh)` is the full subcategory for Mathlib's `IsQuasicoherent` on the
  recorded small étale structure sheaf. `(hM : M.obj.IsFinitePresentation)` is
  Mathlib's exact local-finite-presentation condition: a covering of the terminal
  sheaf, with finite generators and finite relations on its localized sites.
- `(x : Point X.obj.obj)` is the existing field-valued point class.
- `hflat` quantifies over every `U : X.EtaleSite`, `V : Y.EtaleSite`, and scheme
  morphism `h : U.obj.left ⟶ V.obj.left` commuting with f. `EtaleSite` already
  includes the representable étaleness of both chart maps. For every ordinary
  scheme point `t` with `schemePointMap U.obj.hom t = x`, it requires `Module.Flat`
  over `(Y.etaleForget.obj V).presheaf.stalk (h.left t)` of the ordinary stalk of
  `(X.schemeRestriction U).obj M.obj`. `ModuleCat.restrictScalars` along the
  actual `(h.left.stalkMap t).hom` supplies precisely its target-local-ring action.
  Thus the hypothesis is pointwise flatness, rather than flatness on a neighbourhood
  or flatness of all sections.
- `(ξ : PointRepresentative X.obj.obj)` quantifies over every field K in the site's
  size convention, its base map `Spec K ⟶ S`, and a section representing
  `Spec K ⟶ X`. Its bundled `field` is exactly a `Field ξ.K`; `hξ : Quot.mk _ ξ = x`
  says that it represents the fixed x. There is no algebraic-closure, separability,
  characteristic, residue-field-equality, or preferred-representative assumption.
- `PointRepresentative.toMorphism` uses `yonedaEquiv.symm ξ.value`, with the actual
  representable sheaf `schemeSpace (Over.mk ξ.base)`. Therefore
  `(ξ.toMorphism ≫ f)` is exactly y_K, not an unspecified morphism to Y.
- `representativeFibre f ξ` is the actual sheaf pullback of f and y_K, endowed with
  the algebraic-space property from `fibreProduct_isAlgebraicSpace`.
  `representativeFibreProjection` is its first projection. The fibre module in the
  theorem is `(moduleTensorPullback (representativeFibreProjection f ξ)).obj M.obj`.
- `representativeFibreSection` is the universal-property lift of `(ξ,id)`; its first
  projection is ξ and its second projection is the identity by the defining pullback
  lift. `representativeFibrePoint` evaluates that section at the identity of the
  given field spectrum and takes its existing point class. No arbitrary lift or
  existence-only choice occurs.
- Condition (i) is the left side of `↔`: `∃ U : X.EtaleSite`, membership of x in
  `pointImage U.obj.hom`, then `∃ r : ℕ` and an isomorphism between the étale
  restriction `(X.etalePullback U).obj M.obj` and
  `SheafOfModules.free (R := X.structureSheaf.over U) (ULift.{u} (Fin r))`.
  The recorded definition of `etalePullback` is restriction to the localized site,
  which is precisely tensor pullback along an étale chart. `free` is the coproduct
  of copies of the unit structure-module sheaf, so this is O_U^{⊕r}, not a constant
  module sheaf. The ULift only places the finite basis in the section universe.
- Condition (ii) is the right side: the identical chart/stalk flatness test for the
  fibre module, restricted to points equal to `representativeFibrePoint f ξ`.
  For the structure map `id` the compatibility equation is simplified to
  `U.obj.hom = yoneda.map h ≫ V.obj.hom`; this is the same commuting square after
  removing composition with the identity. No chart flatness condition is omitted.
- The equivalence holds for each ξ because ξ and hξ are ordinary universal theorem
  parameters. The same formula applies to every K and every representative of x.

Dependency declarations read and used (all under the recorded modules):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.Algebra.Field.Defs`: `Field` (available through the public dependencies).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `EtaleSite`,
  `structureSheaf`, `Modules`, `etalePullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`,
  with Mathlib `SheafOfModules.IsQuasicoherent` and `IsFinitePresentation` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation` and its exact all-chart test `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  with its specified chart-limit direct image and retained tensor adjunction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`, using
  `PointRepresentative`, `Point`, and `schemePointMap` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (the actual sheaf pullback with its universal property).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with `Module.Flat` from
  `Mathlib.RingTheory.Flat.Basic` and its injective-tensor criterion.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` (actual Yoneda sheaf).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`
  (actual restriction to open subschemes, with the canonical ring comparison).
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`: `SheafOfModules.free`.

All available recorded proof modules are imported privately, including the Mathlib
modules for open immersions being étale, affine-morphism permanence and the
finite-free-module finiteness/flatness statements. The proof-only nodes
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` and
`lem-sfb-space-fibre-flatness-chart-comparison` currently have no Lean records or
Mathlib matches, so no module is available to import for them. Their entire uses
are retained in the proof docstring. Neither is needed to type this stage-2 statement.

Edge cases checked against the node and Tags 0CZS/05WY:

- M=0 has the empty finite basis r=0, and every relevant zero stalk is flat.
- r=0 is allowed by `r : ℕ` and `Fin 0`; no `Nonempty` basis or positive-rank condition.
- If X has no points there is no x, exactly as in the node's pointwise assertion.
  There is no extra nonemptiness assumption on a space or on a chart.
- f=id and identity scheme charts give the usual finite-presentation local freeness
  versus flatness criterion. Source/target charts need not be affine in the statement.
- Extension or change of the representative field is allowed, including nonclosed
  and inseparable fields; the tautological point retains that field and its base map.
- The parameter u is arbitrary; fields and scheme charts have the same allowed size
  as the recorded point-class definition. No independent universe equality is added.

Searches (2026-10-24):

1. `msearch.py ... leanfinder` with “A finitely presented quasi-coherent module flat
   over the base is finite free near a point if and only if its fibre is flat at that
   point”: eight hits, including `Module.free_of_flat_of_isLocalRing`,
   `Module.freeLocus_eq_univ`, and `Module.Flat.tfae_equational_criterion`; none is
   the algebraic-space field-fibre equivalence.
2. `msearch.py ... loogle 'SheafOfModules.IsFinitePresentation, Module.Flat'`:
   zero hits. Direct source reading found the existing finite-presentation predicate.
3. `msearch.py ... grep 'IsFinitePresentation|IsLocallyFree|FlatAt'
   Algebra/Category/ModuleCat/Sheaf`: ten hits, locating Mathlib's exact
   `IsFinitePresentation` and the distinct global locally-free notion.
4. `msearch.py ... leansearch` with “A finitely presented quasi-coherent module flat
   over the base is finite free near a point if and only if its field fibre module
   is flat at the tautological point”: eight hits, including the finite-presentation
   data and local-ring module freeness; no exact equivalence for algebraic spaces.
5. `rg` in `lean/WeilConjectures` for flat/free, FlatAt and finite presentation, and
   `grep -rn 'lem-sfb-space-fibre-flat-free-criterion' lean/WeilConjectures`: no exact
   theorem. Found only algebraic local-ring or scheme-level flat/freeness results.
6. `rg` in `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*` for finite freeness, finite
   presentation, flatness loci, and pointwise flatness found `ModuleIsFlatOver`
   (global, too strong for the hypothesis), `MapIsFlatAt` (morphism flatness, not
   module flatness), and `moduleFlatLocusOverSpectrum` (target restricted to an
   affine spectrum). The item therefore spells out its chartwise stalk predicate.
   The existing `finiteFreeLocus` in `AlgebraicSpaceRelativeFiniteFreeLocusBaseChange`
   uses exactly the slice-free expression used here. That theorem is a downstream
   consumer of this item, so importing it would close a proof dependency cycle;
   no second definition of `finiteFreeLocus` is introduced.
7. Searched `lean/Sheaf`, `lean/WeilConjectures` and `dag/lean_names_upstream.json`
   for `representativeFibre`, `PointRepresentative.toMorphism` and the new theorem
   name: no existing declarations. The direct Yoneda conversion and pullback
   projections use existing canonical category constructions.

Source inspection: read `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-flat-and-free-at-point-fibre` at line 5940 (0CZS) and
`lemma-flat-on-fibres-at-point` at line 5632 (05WY). The latter explicitly uses an
arbitrary field representative and its induced rational point, justifying the
node's exact choice-independent formulation. No statement fault or dispute found.

Validation: `scompile.py Q60 lem-sfb-space-fibre-flat-free-criterion <module>`
compiled both sandbox and library forms cleanly. The first probe found an identity
field-notation elaboration issue in the right-hand commuting equation; replacing
composition with the identity by the equal direct chart maps repaired it without
changing the condition. All universes and variables are explicitly bound, and
`set_option autoImplicit false` is enabled.

## Second reading by Q60

A separate self-reading of the node, source text and complete Lean file was performed;
no other agent was started, as the dispatcher explicitly requires this worker to work
alone. The maintainer's independent review remains the independent second reader.

Rechecked the scheme and algebraic-space binders, local finite presentation, QCoh and
finite presentation, the fixed point x, and the all-chart/all-lifts target-stalk-flatness
hypothesis. In particular `hflat` is only at x, not at every point of X, and it is module
flatness, not flatness of f. Rechecked the arbitrary field/base/value packaged in ξ and
its equality to x. Expanded the five auxiliary definitions: their fibre is the sheaf
pullback along fξ, the first projection defines the fibre pullback, and their point is
exactly (ξ,id) over ξ.K. Compared condition (i) to the previously landed finiteFreeLocus
formula and to the source's étale neighbourhood; they agree. Compared condition (ii)
to the same chartwise stalk test for the identity of that fibre; its simplified
commuting equation is identical. Rank zero and the zero module remain included.
No mathematical mismatch was found; only the elaboration repair described above was
needed. No hypotheses, conclusions or node statement were changed. No new node or
dependency module is part of this delivery.
