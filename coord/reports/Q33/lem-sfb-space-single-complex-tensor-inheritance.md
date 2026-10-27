## Worker report

Q33 states `AlgebraicGeometry.AlgebraicSpace.SingleComplex.singleComplexTensorInheritance`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexTensorInheritance`. The statement is
Stacks Tag 0DKI(1), with the comparison of equation-bc preceding Tag 0DKG, for actual
algebraic spaces and geometric étale structure-module stalks. The original statement,
proof and proof dependencies are preserved. The item's statement dependencies only gain
four definition nodes and the already landed small-model derived-category node.

The inherited stage-1 ending about an unchanged reviewed split does not apply: the
current assignment is stage 2, and the target had no Lean attachment. The current
brief-stage2 section 0 explicitly permits this stage handoff. No reopening of the
accepted split is needed. No statement dispute or statement correction is proposed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Scheme S | `{S : Scheme.{u}}`. |
| Algebraic spaces over S with their actual structure sheaves | `{X X' Y Y' : AlgebraicSpace S}` and the existing `SmallModules`, `smallStructureSheaf` and module equivalences. |
| Universe convention, unbounded module derived categories | Explicit universes `u w`; `[∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]`; `DerivedModules` is the recorded `DerivedCategory` of that small model. No equality with the larger étale-site object universe is imposed. |
| Canonical tensor pullback and derived functor | `pullback f` conjugates the recorded `moduleTensorPullback f` by the fixed basis equivalences; `derivedPullback f` is its universal total left derived functor and `counit f` is its shared derived counit. |
| K-flat derived tensor | `tensor X` is exactly `X.derivedDualityModel.closed.tensor`; `tensorModel` uses that existing datum's specified representative isomorphism. The ordinary total is the existing direct-sum total tensor. |
| Cartesian square with the two projections | Four morphism binders and `sq : IsPullback g' f' f g`, allowing any specified representative of the fiber product. |
| Geometric point Spec Ω → X' | `StalkCondition` quantifies over `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, `s : Spec (.of Ω) ⟶ S`, and `x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj`. This is a morphism to the algebraic space in Sch/S. |
| x, y', y | Composition with `g'.hom.hom`, `f'.hom.hom`, and then `f.hom.hom`; `point_square` transports between the two paths to Y using `sq`. |
| Stalks as colimits of pointed étale scheme neighborhoods | `Neighbourhood` consists of lifts to actual affine étale charts in the fixed small basis. `ringDiagram`, `moduleDiagram`, `StalkModel.ringIsColimit` and `moduleIsColimit` retain the complete ring and additive-group colimit universal properties. This basis is cofinal among pointed étale scheme neighborhoods. Germ scalar and map equations pin the module action and functor maps. |
| R,A,B,C and D=A tensor_R B | `R f g' s x`, `stalkRing s (x ≫ g'.hom.hom)`, `stalkRing s (x ≫ f'.hom.hom)`, `stalkRing s x`; `leftAlgebra` and `rightAlgebra` specify the two R-actions. D is Lean's algebra tensor product with these actions. |
| Projection-induced D → C | `tensorMap_existsUnique` requires both restriction equations, and `tensorMap` selects that unique ring map. It is not an arbitrary algebra structure. |
| K,K' have quasi-coherent cohomology | `K : X.DerivedQCoh`, `K' : X'.DerivedQCoh`, using the landed full subcategories and their original QCoh cohomology predicate. |
| Given phi | `φ : (derivedPullback g').obj K.obj ⟶ K'.obj`. No invertibility of phi is assumed. |
| The displayed beta map with its D-linear cohomology action and extension to C | `comparison` uses `ModuleCat.baseDerivedTensorCohomologyModel` and its `localizedComparison i`, followed by `extendedStalkCongr`, the germ-normalized `tensorStalkIso`, and homology of the stalk of the representative chain map. The source is precisely H^i(derived scalar extension over R) tensor_D C. |
| Canonical map induced by phi | `Coordinates.represents` equates the shared derived counit, the localized chain map and the target identification with `derivedPullback.map e.hom ≫ φ`. The pullback-stalk isomorphism sends b tensor germ(m) to the germ of the recorded adjunction-unit local tensor. |
| All original beta maps invertible | `h_stalk : StalkCondition ... K.obj K'.obj φ`. `StalkCondition` quantifies over all points and all `i : ℤ`, as well as all normalized coordinate presentations. Coordinates exist by `coordinates_nonempty`; this is the usual invariant coordinate expression of the same map, not a restriction or vacuous quantification. |
| Every E in D_QCoh(X), no boundedness | `∀ E : X.DerivedQCoh`; all complexes are indexed by ℤ without truncations, boundedness or Tor-amplitude assumptions. |
| E tensor^L K, and Lg'^*E tensor^L K' | The two arguments of the conclusion's `StalkCondition` are `(tensor X).obj (E.obj,K.obj)` and `(tensor X').obj ((derivedPullback g').obj E.obj,K'.obj)`. Their QCoh property is the closure fact in the node's proof; the ambient stalk condition is defined for all derived objects. |
| psi is the canonical tensor comparison followed by 1 tensor phi | `(derivedTensorComparison g').hom.app (E.obj,K.obj) ≫ (tensor X').map (Prod.mkHom (𝟙 _) φ)`. The selected comparison is uniquely pinned by its ordinary local pure-tensor formula, summand formula on signed totals, and the shared derived-counit equation on K-flat representatives. |
| Every beta_psi is invertible | The conclusion is exactly the same `StalkCondition` for those two objects and psi. |
| No flatness of the square | There is no flatness binder on any of the four space morphisms or on the square. The D → C flatness used in the proof is a geometric consequence, not a new assumption. |

Existing declarations used, with owning modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms and Spec.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`, `etaleForget`,
  `structureSheaf`, `Modules`; their original sheaf and chart objects are retained.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  Mathlib's `SheafOfModules.IsQuasicoherent` rather than a private predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleTensorSection`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `smallEtaleInclusion`,
  `smallStructureSheaf`, `SmallModules`, `smallModuleRestriction`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`, `DerivedQCoh`,
  `derivedQCohProperty`, `derivedDualityModel` with its existing normalized tensor model.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `Qh`; `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`:
  `Functor.totalLeftDerived` and its counit.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `CochainComplex.IsKFlatIndependentCoefficients`, `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`: `total` and `tensor`, with the
  existing coproduct totalization and Koszul differential.
- `WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`:
  `ModuleCat.baseDerivedTensorCohomologyModel`, `localizedComparison`; these retain the
  canonical D-action and cohomology counit. No local copy of this model is introduced.
- `Sheaf.Paper.RingedTopoiTensorComparisonData`: `SheafOfModules.ringedComparisonPure`,
  the actual presheaf tensor followed by the sheafification unit.
- Mathlib `ModuleCat.extendScalars`, algebra tensor products, colimit cocones,
  `StructuredArrow`, natural isomorphisms and termwise homological-complex functors.

The target module imports every already stated proof dependency: the recorded generic
canonical ringed-topos pullback theorem; independent-coefficient K-flat resolutions;
ringed-site K-injective resolutions; point exactness, K-flat stalk criterion and tensor;
cochain inverse-image tensor comparison; total tensor model; canonical tensor-comparison
data; and the existing base-derived tensor cohomology action/model and localized
inheritance theorem. In particular the source/library declarations are used instead of
restating them. The Mathlib K-injective Hom bijection is reachable via those imports.
The two space-specific proof dependencies without a recorded declaration are left as
future proof inputs in the docstring, not assumed as extra hypotheses. They are not
needed merely to type the present statement. The full seven-step proof of this item
is transcribed in its theorem docstring.

Edge cases checked by reading the expanded types and formulas:

- Empty spaces: no geometric point is introduced, and the stalk conditions are
  universally quantified over the empty collection; the theorem is still meaningful.
- Zero K, K', or E and a zero coefficient morphism: all categories, complexes,
  homology maps and tensor maps allow zero; no nonzero premise is present.
- Identity and nonidentity squares: the same regular-function germ equations,
  projection restriction equations and ordinary pure-tensor normalization apply.
- Arbitrarily unbounded E and K: direct-sum totalization over all p+q=i is used;
  integers of either sign occur and the summand comparison introduces no symmetry sign.
- Nonflat f or g: no implicit square-flatness hypothesis is used in the definitions.
  The A and B actions are explicit; no R-flatness is substituted for the D-action.
- Geometric residue fields and characteristics: Ω is any algebraically closed field
  in the section universe; there is no characteristic, finite-type, separatedness,
  qcqs, perfection or boundedness hypothesis.
- Noninvertible phi: the representative t need not be a quasi-isomorphism. Only
  its specified localized cohomology comparisons are required to be invertible.
- The coordinate predicate is nonvacuous, by the named resolution/representation
  theorem. Its representative equation fixes the given phi rather than a freely
  chosen map with merely matching source and target.

Searches: `msearch.py` LeanFinder, Loogle, LeanSearch and Mathlib grep were run with
queries recorded verbatim in each new node's `mathlib_searches` and `searches.jsonl`.
The LeanFinder query about derived tensor preserving geometric-stalk base-change
returned scheme stalk and module-pullback facts. Loogle `"tensor", "baseChange"`
returned ordinary scalar-extension tensor isomorphisms. Mathlib grep for
`singleComplexBaseChange|baseChangeCondition|AlgebraicSpace.*stalk` and subsequently
`AlgebraicSpace.*(stalk|derivedPullback)|CanonicalTensorComparison|StalkCondition`
returned zero hits. LeanSearch on geometric stalk colimits and on algebraic-space
derived pullback returned topological or scheme stalks and general ordinary
pullback APIs. The final LeanFinder query combining pointed affine neighborhoods
and the canonical total derived comparison again returned scheme stalk facts.

Project searches used `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the
requested target-id grep in upstream sources (no match). The existing
`AlgebraicGeometry.singleComplexInheritedTensorCondition` is for schemes and
Zariski stalks, not algebraic spaces with geometric étale stalks, so it is not an
existing declaration of this node. Existing algebraic-space derived tensor and
small-model categories were found and reused. DAG grep and
`tools/blueprint_refs.py search` found scheme geometric-stalk nodes and two unrelated
blueprint units for pullback tensor comparison, but no algebraic-space normalized
geometric-stalk or canonical derived-pullback interface. The ancestor query gives None.

Every definition has real data. Choices use a full colimit universal property, a
universal total derived functor, or an explicitly unique germ/summand/counit
normalization. There is no definition chosen from a mere unconstrained existence of
a comparison, and no sorry term inside a definition. The thirteen postponed named
proof obligations are:

- Derived-pullback models: `pullback_additive`, `pullback_hasLeftDerived`,
  `coordinates_nonempty`.
- Geometric stalk models: `stalkModel_nonempty`, `stalk_additive`,
  `stalkMap_existsUnique`, `pullbackStalk_existsUnique`.
- Stalk condition: `point_square`, `tensorMap_existsUnique`.
- Canonical tensor comparison: `ordinaryTensor_existsUnique`,
  `ordinaryTotal_existsUnique`, `canonicalTensor_existsUnique`.
- Item: `singleComplexTensorInheritance`.

Each is explicitly included in its owning node's `lean.declarations`, its mathematical
assertion is included in that node's definition specification, and its docstring gives
the source and proof. All theorem proofs are `by sorry`, as required at stage 2.

Validation: `scompile.py` has compiled all five files in dependency order, including
private overlay, standalone sandbox and final module compilations. The sole earlier
line-width warning was repaired. All five final files compiled cleanly through the delivery wrapper. The first
preflight requested `import_flags` on each new definition node; empty lists were
added. Grouped dependency citations were expanded to individual [id] citations,
and the new-node TeX backslashes were normalized. The dry run is repeated on
these repaired records before the push.

## Second reading by Q33

This is the worker's second pass through the node, source and all five modules; the
independent review is the maintainer's delivery review specified in the dispatch.
No second agent was started and no independent reading is claimed here.

I re-read equation-bc and 0DKI(1) alongside the hypothesis/clause table above. The
scheme/Zariski theorem does not match this node. The ring action must be the
D=A tensor_R B action, so the delivered definition uses the existing normalized
base-derived cohomology model. The path to the Y stalk must be transported using
the square, not identified definitionally; `point_square` and `rightAlgebra` do this.
The original representative chain map need not be invertible; none is asserted.
The conclusion uses the inverse-direction pullback tensor comparison followed by
1 tensor phi, with the scalar on the first factor and 1 on the second. The
ordinary-unit, summand and derived-counit equations fix all three normalizations.

During type checking I corrected the explicit inclusion of the square hypothesis
in `point_square`, a parenthesization of the termwise scalar-extension functor,
class-definition reducibility annotations and one long line. The four additional
modules correspond to distinct missing notions: universal derived pullback and
coordinates, geometric stalks, the equation-bc predicate, and its canonical tensor
comparison. Their definitions preserve all source clauses. No hypothesis or
conclusion of the target node was changed during these repairs.

## New nodes

`def-sfb-space-derived-pullback-models` owns
`AlgebraicSpaceDerivedPullbackModels.lean`. It defines the total left derived
functor of the recorded small-model tensor pullback and its counit, bundles
flat-term K-flat representatives, reuses the existing normalized tensor, and
specifies coordinates of a derived coefficient map. Sources are 06YS, 07A4 and the
0DKG setup. The searches above found ordinary pullback and the existing ambient
derived category, but no unbounded algebraic-space pullback/coordinate interface.

`def-sfb-space-geometric-stalk-models` owns
`AlgebraicSpaceGeometricStalkModels.lean`. It gives ring and module colimits on
pointed affine étale charts, the actual germ-normalized scalar action and maps,
and the unique pullback-stalk isomorphism with its local-unit tensor formula.
Sources are Properties of Spaces 03G7/03ED, Modules on Sites 03D7 and equation-bc.
Existing DAG/module stalks were for schemes, Zariski spaces or general topos
points; none supplied these actual algebraic-space pointed-chart colimits.

`def-sfb-space-single-complex-stalk-condition` owns
`AlgebraicSpaceSingleComplexStalkCondition.lean`. It defines the projection-induced
D → C map and the canonical equation-bc comparison using the existing base-derived
tensor cohomology model, and requires invertibility at all points and degrees.
The source is equation-bc before 0DKG. The scheme/Zariski analogue does not state
this algebraic-space geometric condition, and no matching DAG definition was found.

`def-sfb-space-pullback-tensor-comparison` owns
`AlgebraicSpacePullbackTensorComparison.lean`. Its ordinary comparison is uniquely
specified on local pure tensors, its total comparison on every homogeneous
summand, and its natural derived comparison by the shared-counit square on all
flat-term K-flat representatives. Sources are Modules on Sites 03EL, Cohomology
on Sites 07A4 and 0DKI(1). General ringed-topos comparison data were found and
reused for pure sheaf tensors, but no recorded algebraic-space comparison could
be applied without first supplying this missing canonical specialization.
