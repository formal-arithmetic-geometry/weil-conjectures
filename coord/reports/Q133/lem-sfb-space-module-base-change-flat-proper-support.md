## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport` states
`AlgebraicGeometry.AlgebraicSpace.moduleTensorPullback_flat_properSupport_baseChange`.
Its only theorem has proof `sorry`; it defines no new notion or arbitrary map.
The item's natural-language statement and all existing node fields are unchanged;
only `lean` is added. There is no released repair note for this item.

Clause-by-clause correspondence:

- `S : Scheme.{u}`, `T T' : Over S`, and `g : T' ⟶ T` give precisely the three
  schemes with their structural maps and an S-morphism. `Over` is the bundled
  encoding of the node's two schemes over S; it adds no condition on them.
- `X : AlgebraicSpace S` and `f : X ⟶ schemeSpace T` give the space and the map
  to the represented scheme T. `schemeSpace` is the existing actual Yoneda sheaf,
  not an arbitrary space or a chosen equivalence to a scheme.
- `hf : MapIsLocally (@LocallyOfFiniteType) f` is exactly local finite type on
  compatible etale scheme charts, from the recorded morphism-properties node.
  It does not assert finite presentation, quasi-compactness, or separatedness.
- `X'`, `p`, `f'`, and `sq : IsPullback ...` express X'=X times_T T' and BOTH
  projections, with the bottom arrow the actual Yoneda map of g. An arbitrary
  cartesian representative is used rather than fixing a choice of pullback.
  Every sheaf pullback in the node supplies such a square, and its universal
  property identifies any such square with that pullback. This is an encoding
  of the specified object, not an added mathematical hypothesis.
- `M : X.Modules` is the recorded small-etale structure-sheaf module category.
  `hqc : M.IsQuasicoherent` uses Mathlib's local arbitrary-free-presentation
  predicate, the same predicate as the recorded `QCoh` full subcategory.
- `hfp : M.IsFinitePresentation` is Mathlib's local finite-free cokernel
  presentation: both free-generator and relation index sets are finite. Rank
  zero is permitted. This is exactly the finite m,n presentation in the node.
- `hflat` quantifies over EVERY `U : X.EtaleSite`, without surjectivity or
  affineness restrictions on a chart. `schemeRestriction X U` is the actual
  restriction to its Zariski opens, with the canonical regular-function scalar
  comparison. The scheme map to T is
  `(yoneda.preimage (U.obj.hom ≫ f.hom.hom)).left`.
  `Scheme.Modules.IsFlatOver` is the dependency's recorded affine-section
  condition, explicitly documented there as equivalent to stalk flatness for
  quasi-coherent modules. Scheme/etale quasi-coherent comparison makes each
  chart restriction quasi-coherent, so its ordinary Zariski stalk is exactly
  the colimit in the node. Scalar restriction is along this actual scheme map.
  Thus this use of the recorded predicate retains precisely the ordinary-stalk
  condition and does not replace it by geometric-stalk flatness or a test on
  only one atlas.
- `hsupp` is the exact carrier criterion: a space Z, a representable closed
  immersion i into X, `MapIsProper (i ≫ f)`, a module G on Z which is both
  quasi-coherent and finite type, and `Nonempty ((moduleDirectImage i).obj G ≅ M)`.
  `IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left)` tests the closed
  immersion on all scheme pullbacks. Finite type is Mathlib's etale-local finite
  generation. No reduced or annihilator support is substituted for this carrier.
- The four conjunctions in the conclusion are exactly quasi-coherence, finite
  presentation, the same all-chart relative flatness over T', and the identical
  carrier criterion with `f'` and `(moduleTensorPullback p).obj M`.
  This is the recorded canonical tensor pullback, the left adjoint to the
  normalized compatible-chart-section direct image, not a freely chosen functor.
- There is no flatness, noetherianity or finite-presentation assumption on g,
  and no finite-presentation assumption on f. Universe `u` is explicit throughout;
  schemes, rings and section carriers use the existing framework's bound, with
  small-etale objects in u+1. `set_option autoImplicit false` forbids auto-binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `EtaleSite`, `Modules`, and `structureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (sheaf pullback closure and universal property).
  It is publicly reached through `AlgebraicSpaceMorphismProperties`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsProper`, with separatedness, finite type and universal closedness.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, publicly reached
  through `AlgebraicSpace.Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice sheafification instances; the defining predicate is the recorded
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` declaration
  `SheafOfModules.IsQuasicoherent`.
- That same Mathlib file supplies `SheafOfModules.IsFinitePresentation`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` supplies `IsFiniteType`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `moduleTensorPullback`, retaining the specified chart-limit normalization.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, with its full affine-open signature and docstring.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, publicly
  exposed through the dependency record's `AtlasEtaleRestriction` module.
- `def-weil-size-convention` is a metatheoretic convention and has no declaration;
  this module states its universe explicitly instead of introducing a fake object.

The plain imports are the recorded, already-stated proof dependencies: module
quasi-coherence pullback; finite-presentation module limits (including arbitrary
pullback); scheme Zariski/etale comparison; relatively flat module pullback;
space module restriction comparison; relative flatness source cover; etale and
closed-immersion scheme permanence; left-adjoint preservation of colimits.
The enlarged-site dependency is public because its actual represented scheme is
used in the signature. `lem-sfb-space-proper-base-change` and
`lem-sfb-space-affine-module-base-change` have neither usable recorded modules nor
Mathlib matches in the read DAG; they are proof-only prerequisites, so no import
is possible yet and no replacement theorem is invented. Their later proofs are
not needed to type the statement. The seven-step proof docstring retains their
roles and all other steps of the node's proof.

Sources checked: Stacks `spaces-morphisms.tex` lemma-base-change-module-flat
(Tag 05VW(1)); `sites-modules.tex` lemma-local-pullback (Tag 03DO(5)-(7));
`spaces-perfect.tex` lemma-module-support-proper-over-base (Tag 0CZI(3)) and
lemma-base-change-module-support-proper-over-base (Tag 0CZJ). The current
`literature/blueprint/latest` direct-images statement/proof was also read; this
is the inherited proper-support Quot prerequisite, not a replacement unit route.

Edge cases checked mathematically: zero M (take the empty proper carrier), empty
X or charts (all local assertions vacuous), zero generator/relation ranks,
identity and arbitrary isomorphic pullback squares, a non-flat base change such
as Spec(F_2) to Spec(Z), and nonreduced closed carriers. None is excluded by the
binders. In affine charts the pullback is A' tensor_A N, flat over A' if N is
flat over A; no flatness of A' over A is required. Properness of the carrier is
stable under precisely that arbitrary base change. No statement dispute found.

Searches made for an existing statement (all 2026-10-24):

- `msearch.py ... leanfinder`: "Tensor pullback of a finitely presented relatively
  flat quasi coherent module on an algebraic space preserves finite presentation
  flatness and proper support under arbitrary base change". Eight results:
  scheme flat/local-finite-presentation permanence and algebraic tensor finite
  presentation; no algebraic-space module theorem.
- `msearch.py ... loogle`: `SheafOfModules.IsFinitePresentation,
  SheafOfModules.pullback`. Zero results.
- `msearch.py ... grep`:
  `AlgebraicSpace.*(Flat|Support)|pullback.*(ProperSupport|properSupport)|baseChange.*module.*flat`.
  Four ring Kaehler/JacobiZariski hits; no match.
- `rg` in project `lean/Sheaf` and `lean/WeilConjectures` for proper-support,
  relative-flatness, finite-presentation and chart-restriction names found the
  existing predicates/interfaces above. `ModuleIsFlatOver` is a general all-pairs
  chart predicate; `HasProperAnnihilatorSupport` requires a specified annihilator
  closed subspace and is not the existential carrier convention of this item.
  Neither is redefined. The existing scheme theorems
  `tensorPullback_flat_proper_support` and `properSupport_tensorPullback_properties`
  were read: they concern Zariski modules on schemes, not arbitrary spaces.
- `grep -rn` of the exact item id in `lean/WeilConjectures` found no declaration.
  `rg` of the proposed theorem name in Mathlib, upstream, project Lean and
  `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py Q133 lem-sfb-space-module-base-change-flat-proper-support`
compiled the delivered file as sandbox and final library module, respectively
6.0 and 6.8 seconds, with no errors or unexpected warnings. No global build run.

## Second reading by Q133

A separate self-review reopened the node and final signature after compilation.
The dispatcher explicitly prohibits starting another agent; the independent
reading is the maintainer's delivery review, not something claimed here.
The check matched every binder and conclusion above. In particular, `sq` is
cartesian rather than merely commutative; `g` is any map in Over S; `hflat`
quantifies over every etale chart and uses its actual map to the represented T;
both support clauses require finite-type quasi-coherent G and an isomorphism
with the canonical direct image. The conclusion lists all four required
properties. The existing scheme `IsFlatOver` equivalence is applicable because
M and its chart restrictions are quasi-coherent. No mismatch or correction was
found. No definitions, helper theorems, new nodes, dependency repairs or statement
changes are delivered.
