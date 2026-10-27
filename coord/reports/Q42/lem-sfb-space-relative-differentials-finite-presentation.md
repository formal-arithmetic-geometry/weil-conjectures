## Worker report

The module states `AlgebraicGeometry.AlgebraicSpace.spaceRelativeDifferentials_finitePresentation`.
Its sole theorem proof is `sorry`. The four supporting definitions have real data.
The node's statement, proof, and proof dependencies are unchanged. Its statement dependencies
add the already-landed `def-sfb-space-small-ringed-model`,
`def-sfb-space-morphism-properties`, and `def-sfb-sheaf-differentials`.

Hypothesis and clause correspondence:

- The arbitrary base scheme is the explicit section binder `{S : Scheme.{u}}`.
  `{X Y : AlgebraicSpace S}` and `(f : X ⟶ Y)` are the specified spaces and morphism over S.
- Local finite presentation on compatible étale scheme charts is
  `hfp : MapIsLocallyOfFinitePresentation f`. Its recorded definition is exactly the
  test of `LocallyOfFinitePresentation` on every compatible pair of representable
  étale scheme charts, with no cartesian-square assumption.
- The representing module `Omega_{X/Y}` is `spaceRelativeDifferentials f`.
  This is `SheafDifferentials.omega (cotangentRingMap f)` on the existing small affine
  model, transported by `X.smallModuleEquivalence.inverse`. `cotangentRingMap` is the
  canonical map from the inverse image of O_Y to O_X, characterized by pullback of
  regular functions on charts. `omega` is the actual sheafification of sectionwise
  Kähler differentials; its universal derivation is the sectionwise derivation followed
  by the sheafification unit. Thus this construction represents exactly derivations
  vanishing on the inverse-image base ring. It is not a chosen unrelated module or map.
  The inverse equivalence is the recorded inverse of actual affine-chart restriction,
  in the original coefficient universe u.
- Compatible étale scheme charts are `U : X.EtaleSite`, `V : Y.EtaleSite` and
  `g : U.obj.left ⟶ V.obj.left`. The displayed equality
  `U.obj.hom ≫ f.hom.hom = yoneda.map g ≫ V.obj.hom` is their commutative square.
  Membership in the two sites already includes representable étaleness.
- Restriction to the ENTIRE scheme site U_et is expressed by precomposition along
  `differentialChartInclusion U`. The three chart helpers construct exactly
  `(W → U) ↦ (W → U → X)`, including maps. The inclusion's proof uses the existing
  representable-etale scheme-test criterion and composition, not a new etaleness notion.
- The first conjunct gives an isomorphism `e` of additive presheaves between that
  restricted module and
  `(Scheme.Modules.etaleTensorSectionsSheaf g.left.relativeDifferentials).obj`.
  A natural isomorphism compares all restriction maps, not just individual values.
  Its following equation, for EVERY étale W/U, scalar r in Γ(W,O), and section m,
  says its components are linear for the actual regular-function action. Thus it is
  precisely an isomorphism of module sheaves on U_et. The target is the recorded
  associated étale sheaf of the recorded usual differential module. Expressing the
  comparison through its underlying presheaves does not weaken it: both being sheaves
  and linearity of the inverse follow from the target sheaf and the linear natural
  isomorphism. This also avoids introducing a separate continuity or transport datum.
- The second conjunct is `(spaceRelativeDifferentials f).IsQuasicoherent`, exactly
  Mathlib's local-presentation predicate used by the dependency's `QCoh` category.
- The last conjunct is `(spaceRelativeDifferentials f).IsFinitePresentation`.
  Its `exists_quasicoherentData` gives a covering and, on every localized site, a
  presentation with finite relation and generator sets. This is exactly the local
  sequence O^(m) → O^(n) → Omega → 0 with finite m,n. Finite sets can be enumerated
  by Fin of their cardinality, and no globally uniform m,n is asserted.
- All modules are the existing `X.Modules` / `ringedSiteModules` categories,
  i.e. Mathlib `SheafOfModules`; the presentation predicate uses cokernel exactness
  in those categories. There is no Noetherian, separated, quasi-separated,
  quasi-compact, smooth, or finite-atlas hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`, `IsEtale`, and `isEtale_comp`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; used by the existing chart predicate.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, whose definition is actual module sheafification.
  `WeilConjectures.AlgebraicGeometry.TangentBundle` exposes this and its
  `Scheme.Hom.isQuasicoherent_relativeDifferentials` instance, needed to form the
  associated étale sheaf for every chart morphism.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`:
  `Scheme.Modules.etaleTensorSectionsSheaf`, with its actual tensor-section presheaf
  and restriction maps. The explicit scalar action is `Scheme.Modules.smul`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the slice
  sheafification instances, using `SheafOfModules.IsQuasicoherent` unchanged.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  it transparently abbreviates `SheafOfModules`, as used in the construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation` and `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallEtaleModel`, `smallStructureSheaf`, `SmallModules`, `smallModuleRestriction`,
  and `smallModuleEquivalence`. This keeps site and section universe u.
- `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`:
  `SheafDifferentials.omega`, as recorded by `def-sfb-sheaf-differentials`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentRingMap` and its
  chart-normalized structural-map construction, already in proof dependencies.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`:
  `representable_etale_scheme_tests`, clause identifying Yoneda étaleness with
  ordinary scheme étaleness, used only as an inherited definition obligation.

Already-stated proof dependencies are imported with plain imports:
ChartwiseEtalePermanence, SheafifiedDifferentialsCokernel, CoherentFiniteType,
RelativeDifferentialsAffineSections, QuasicoherentFiniteTypeAffine, and the exact
Mathlib ring-level finite-presentation-of-differentials instance from
RingTheory.Extension.Cotangent.Basic. SpaceCotangentRingMap and
InverseImageDifferentials are public imports because the construction also uses them.
The two scheme étale comparison proof nodes currently have no Lean declarations,
so there are no recorded modules to import for those two. Their steps remain in
both the node's unchanged proof and the theorem docstring.

Source checks: read spaces-more-morphisms.tex at definition-sheaf-differentials,
lemma-match-modules-differentials, lemma-localize-differentials,
lemma-module-differentials-quasi-coherent and lemma-finite-presentation-differentials
(Tags 04CT, 04CS, 04CU, 04CV, 05ZF). Read the current latest blueprint's
sk-thm-sf-ctf-stability-direct-images.proof.md: this item is the lower generic
space-differential input to the recorded direct-image route, not that unit's statement.

Edge cases checked before statement and rechecked after elaboration:
identity and étale morphisms give zero differentials, admitting a zero-rank local
presentation; the empty source is allowed, as are empty étale test charts. Polynomial
algebras of finite rank over arbitrary non-Noetherian rings are included. Closed
immersions such as Spec(F_p) → Spec(Z) have zero relative differentials and are
included without flatness. Non-quasi-compact sources can have unbounded presentation
ranks on different components: the conclusion has only local finite presentation.
The chart square need not be cartesian, and neither chart is required to be surjective.
All universes are explicit and autoImplicit is false; no equality of independent
site and coefficient universes is imposed.

Searches (full tool records are also in sandbox searches.jsonl):

- LeanFinder: "Relative differentials of a locally finitely presented morphism of
  algebraic spaces are a finitely presented quasi coherent module" returned eight
  hits, including the ring-level finite-presentation instance, relativeDifferentials'
  and quasicoherentDataOfIsFinitePresentation. None states this space theorem.
- Loogle: "SheafOfModules.IsFinitePresentation, KaehlerDifferential" returned no hits.
- LeanSearch: "The relative differential module of a locally finitely presented
  algebraic space morphism is of finite presentation" returned eight hits, including
  the same ring instance, IsFinitePresentation, and relativeDifferentials'.
- msearch grep "relativeDifferentials|IsFinitePresentation" in AlgebraicGeometry
  reported no hits. Direct source searches compensate for that search service result:
  rg of lean/WeilConjectures and lean/Sheaf found the existing scheme differentials,
  general sheafified omega, ring map, and chart finiteness predicates, all reused.
  The exact item-id search in lean/WeilConjectures returned no match. Searching
  space/differential and omega/cotangentRingMap found no duplicate space theorem.
- DAG definition search found and reused `def-sfb-sheaf-differentials`; no duplicate
  general differential object is defined. `tools/blueprint_refs.py search
  'relative differentials'` returned one projective-space blueprint unit, no copy of
  this theorem. The small-model and chart-property definition nodes are also reused.

The specialized differential object and chart inclusions are helpers belonging to
this item's own notion, as permitted in the brief. No independent new notion or
new node, dependency repair, or statement correction was necessary. No
STATEMENT-DISPUTED fault was found.

Validation: scompile.py compiled both sandbox and library-name versions cleanly,
with the expected postponed theorem and no other warnings or errors. The initial
probe exposed missing public access to the scheme-test criterion and an endpoint
inference issue in Over.homMk, both repaired by an explicit public import and
explicit endpoints. The scalar action uses its actual bundled additive-map projection.

## Second reading by Q42

Reopened the node and final Lean file for a separate clause-by-clause reading.
The base, spaces, over-S morphism and local chart finite-presentation hypothesis
are exactly the binders described above. The canonical module uses the existing
structural inverse-image map and existing sheafification, with unchanged sections
universe. The compatible chart square is a plain equality; no pullback or
surjectivity assumption entered. The natural presheaf isomorphism is on every
étale test scheme over U, and the scalar equation is essential: without it the
comparison would only identify abelian sheaves. The final file includes that
linearity equation, so it identifies the specified module sheaves. The recorded
scheme differential and associated étale sheaf occur literally in its target.
The two final predicates are exactly quasi-coherence and local finite presentation
by finite free presentations; neither finite type alone nor global finite
presentation of the morphism is substituted. Read their Mathlib definitions
alongside the file to check this. All definition helper data are actual functors
or a specified equivalence transport; no existence-based arbitrary object is used.
No mathematical mismatch or statement correction was found. The earlier compiler
interface repairs affect only elaboration, and the final file compiled cleanly.
No other agent was started, as the dispatcher brief explicitly prohibits it.
