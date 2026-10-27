## Worker report

The module `Sheaf.Paper.WeilFrobeniusActionResolutions` states
`WeilConjectures.WeilFrobeniusAction.frobenius_action_resolutions`, with one postponed
proof. Its docstring gives the seven-step proof, including the exact LEFT adjoint
argument for preservation of K-injectives. All auxiliary definitions contain real
data or explicit predicates; no data is selected from this existence theorem.
The auxiliary structures package the clauses of this single node rather than
postulating a new coefficient object, module category, or homological predicate.
The repair adds only the missing definition citation to the node statement; its
mathematical content is unchanged. No statement is disputed.

Hypothesis and clause correspondence:

- The finite base field and its arbitrary fixed algebraic closure are
  `D : FiniteFieldDatum.{u}`. The prime is `l` with `[Fact l.Prime]`, and
  `_hl : l ≠ D.p` is exactly the unequal-characteristic condition. The coefficient
  closure is the project's `PadicAlgCl l`, its fixed representative of Qbar_l.
- `T₀ : Over (Spec (CommRingCat.of D.k₀))` and the three instances
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` render separated finite type.
  `D.geometricFiber T₀` and `D.geometricFrobenius T₀` are the recorded fibre and
  actual id-times-geometric-field-Frobenius automorphism, without requiring it to
  be a morphism over k.
- `Site T := AsSmall.{u+1} T.ProEt` retains EVERY bounded pro-etale object, rather
  than choosing a skeleton not closed under translation. Its morphisms are lifted
  to u+1, so its small-category structure is compatible with coefficient universe
  u+1; the original site's object and morphism universes remain u+1 and u.
  `topology` is the induced original topology. `postcompose` is the actual comma
  category equivalence induced by the scheme automorphism. Hence its inverse,
  all integer iterates, and pullbacks are retained. `Realization.covering` and
  `inverseCovering` explicitly assert covering preservation. Equivalences preserve
  pullbacks, and the original pro-etale category has them.
- `translation g` is postcomposition by g inverse. Consequently its inverse
  reindexes sections along postcomposition by g, which is g inverse-image on
  sheaves (base change along g is postcomposition by g inverse). This direction
  is essential for `pullback` to mean geometric Frobenius pullback.
- `coefficient` restricts the existing `ProEtale.padicAlgClSheaf`, using the recorded
  `sectionRingSheaf`. This is the sheafification of functions taking values in a
  finite subextension, NOT the unrestricted continuous-function sheaf.
  `generator` is the actual sheafification unit on those functions.
  `Realization.a` is the ring-sheaf isomorphism; `functions` normalizes it on every
  such generating section. Postcomposition leaves the domain scheme literally
  unchanged, so the same function, continuity, and same finite field are retained.
  The transported topology and sheafification retain the LOCAL finite-field
  condition as well. No arbitrary scalar automorphism is permitted.
- `Modules` is the recorded module-sheaf category on this equivalent small model.
  `ambientModules` explicitly returns to internal modules over the original
  coefficient on the original site. `ambientEquivalence` and `ambientAdditive`
  assert its equivalence and additivity. Thus this is a concrete small-site
  presentation of A, with unchanged underlying sections, rather than a second
  coefficient theory. `Pairs` is literally `Endofunctor.IsoAlgebra (pullback D)`;
  `forget` is its recorded forgetful functor. The structure map is invertible
  and its morphisms are intertwining maps, with no extra finiteness constraint.
- `Realization.presentation` is the FULL recorded
  `TwistedActionRingedSite.Presentation`. Its `modules` equivalence, used in the
  inverse direction, gives B equivalent to action-site modules; `modules_add`
  supplies additivity. `restriction`, `geometric`, `geometric_inverse`,
  `structural`, `structural_eq`, and `modulePullback` identify U with the actual
  ringed-topos module pullback with invertible structural map.
- The same presentation's `tensor`, `tensor_pure`, `sigmaTensor_pure`,
  `tensor_action`, `hom`, `sigmaHom_evaluation`, `hom_action`, `symmetry`, and
  `evaluation` assert precisely diagonal tensor, contragredient Hom and the usual
  underlying symmetry/evaluation. Its unit normalization is also retained.
- `conservative`, `createsLimits`, `createsColimits`, `exact_limits` and
  `exact_colimits` give ordinary exact conservative U creating all small diagrams
  in the chosen universe. `induction`, `inductionAdjunction`, `inductionSum`,
  `induction_shift`, `induction_zero`, `induction_add`, `induction_limits`, and
  `induction_colimits` give the exact additive LEFT adjoint, all integer summands,
  the shifting action and its zero-summand adjunction normalization.
- `ResolutionAssertions.derived` concerns the canonical `forget.mapDerivedCategory`
  on UNBOUNDED `DerivedCategory`, asserting triangulatedness and reflection of
  isomorphisms. `cohomology` is a natural isomorphism of functors for each integer
  degree, not merely unrelated object isomorphisms. `HasDerivedCategory.{wA}` and
  `.{wB}` are quantified choices of localization universes, not extra mathematical
  restrictions or an equality imposed on the site universes.
- `Constructible` spells out the clause's finite locally closed stratification
  using the RECORDED `FiniteLocallyClosedStratification`, followed by the recorded
  `CondensedRing.LocallyFree` on the actual inverse-image restriction. That predicate
  allows varying finite ranks and rank zero. `ResolutionAssertions.constructible`
  requires boundedness and this predicate on all underlying cohomology, and
  concludes boundedness and the same predicate after D(U). The natural cohomology
  isomorphism transports the very same witnesses; no assertion about fixed pairs
  in D(A) is made.
- `onActionSite` is the actual inverse module equivalence applied termwise.
  `KFlat` uses the dependency's `IsKFlatIndependentCoefficients` under that tensor
  equivalence; `FlatTerms` uses its `IsFlatOnSite`, not substitute notions.
  `flat_resolution` quantifies EVERY integer-indexed complex in B and gives a
  quasi-isomorphism L to K, K-flat L with flat terms, and a quasi-isomorphism after U.
- `injective_resolution` supplies ONE functor I and natural transformation id to I
  whose components are quasi-isomorphisms, whose values satisfy the recorded
  `CochainComplex.IsKInjective`, and whose forgotten augmentations are
  quasi-isomorphisms. This is the requested functorial choice, not unrelated
  existence witnesses for individual complexes.
- `preserves_flat` quantifies all K-flat complexes with flat terms and preserves
  both properties. `preserves_injective` quantifies all K-injective complexes.
  `quasiIso` explicitly preserves every quasi-isomorphism. Every localization
  above is of the actual abelian fixed-pair category, never fixed pairs in D(A).

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`; `Sheaf.Paper.CompletedCondensedCoefficients`
  and `WeilConjectures.CategoryTheory.RingObjects.EllAdic` supply the coefficient
  comparison and `ProEtale.padicAlgClSheaf`, `padicAlgClRingPresheaf`,
  `PadicAlgCl.finiteIntermediateFieldValued`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra` and
  `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra`:
  `Endofunctor.IsoAlgebra`, `.forget` and their inherited abelian/exact interfaces.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `.topology`;
  `def-weil-size-convention` supplies the metatheoretic universe convention.
- `Sheaf.CategoryTheory.TwistedActionRingedSite` and its Data module:
  `TwistedActionRingedSite.sigma`, `Modules`, `Presentation`, `presentation`.
  `Sheaf.CategoryTheory.RingedToposMorphism`: `RingedToposMorphism`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; upstream ExactFunctor: `Functor.mapDerivedCategory`;
  `DerivedCategory.homologyFunctor`, `DerivedCategory.TStructure.t.bounded`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`;
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- Added existing landed dependency records for
  `def-weil-pbc-internal-abelian-sheaf-module-equivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf`, `.sectionModuleEquivalence` in
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`;
  `def-sf-proetale-locally-finite-free-module`:
  `ProEtale.CondensedRing.LocallyFree` in `Sheaf.Paper.ContinuousLocallyFreePullback`;
  and `def-constructible-stratification`:
  `Scheme.FiniteLocallyClosedStratification` in
  `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`.
  No dependency record is repaired or duplicated.

Edge cases checked: empty T (zero strata allowed), zero modules and rank zero,
nonconstant local ranks, negative and zero integer translates, degree zero and
arbitrary positive/negative cohomology, arbitrary unbounded complexes and localized
morphisms, and arbitrary fixed algebraic closure of k0. No finite-order action,
continuity of a discrete Z action, constructible terms, bounded resolution, or
k-linearity of geometric Frobenius is assumed. The small-model universe lift does
not identify the original object's universe with its morphism universe.

Searches made on 2026-10-24, before writing the final declaration:

- `msearch.py leanfinder`: “Frobenius equivariant module sheaves action site forgetful
  functor preserves K-flat K-injective resolutions”: eight ordinary module/condensed
  hits including `SheafOfModules.forgetToSheafModuleCat` and
  `LightCondensed.instIsGrothendieckAbelianLightCondMod`; no full statement match.
- `msearch.py loogle`: `"IsoAlgebra"`: three `algEquivIsoAlgebraIso` hits, irrelevant
  to this ringed-site and resolution specialization.
- `msearch.py grep`: `Frobenius|IsoAlgebra|KFlat`, `AlgebraicGeometry/Sites`: no hits.
- `msearch.py leansearch`: “Frobenius equivariant module sheaves have an exact
  conservative derived forgetful functor preserving K flat and K injective
  complexes”: eight ordinary forgetful module-sheaf results; no full match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Frobenius/site/resolution,
  `IsoAlgebra`, `nativeForget`, and the item id: generic fixed-pair infrastructure,
  native closed-forgetful consumer and Frobenius cohomology results, no declaration
  stating the complete item. The prescribed recursive item-id grep likewise gives
  no existing declaration of this item in WeilConjectures.
- Additional `rg` for `FiniteLocallyClosedStratification`, `Constructible`,
  `LocallyFree`: reused the exact landed partition and local-free predicates;
  `IsConstructibleProEtaleModuleSheaf` concerns finite constant coefficients,
  finite stalks and locally constant restrictions and is not this Qbar_l clause.
  Upstream `Scheme.Stratification` additionally imposes constructible strata, so
  the recorded weaker `FiniteLocallyClosedStratification` was used instead.

The latest blueprint's `cor-coef-verdier-weil-equivariance.proof.md` was read,
particularly its internal-Hom/evaluation/transposition paragraph; the native
seven-step argument in the DAG supplies this item's refinement. The first clean
server compile checked both the sandbox module and its library module name.

## Second reading by Q50

The dispatch explicitly prohibits starting other agents, so this is a separate
self-review pass, not a claim of an independent worker review. The maintainer's
independent delivery review remains required. With both node and module open,
I checked every clause using the correspondence above. The pass corrected the
translation direction (sigma reindexes by the inverse translation) and replaced
upstream constructible-strata partitions with the recorded finite locally closed
partition. It also checked that functorial K-injective replacement is one functor
with a natural augmentation, K-flat preservation applies to all flat-term K-flat
complexes, the LEFT adjoint is exact, and definitions contain no sorry. There is
one named theorem with a seven-step natural-language proof and postponed Lean proof.


## Returned delivery repair

The return on immutable head `2ad1093ac536` identifies H2/H12: the previous
statement dependency on `lem-weil-pbc-continuous-locally-free-pullback` used only
its helper predicate, not its pullback conclusion. Removed that theorem from
`stmt_deps`; the replacement is the new definition node
`def-sf-proetale-locally-finite-free-module`. The node statement cites this
new definition at “pro-etale locally finite free restrictions”. The Lean remains
on exactly `AlgebraicGeometry.ProEtale.CondensedRing.LocallyFree`; its declaration
is not moved or duplicated. Only the `Constructible` docstring now names its DAG
owner. The main theorem signature and every mathematical clause are unchanged.
The sandbox was compared with current main: the original item has no landed
Lean module on main, and all original non-Lean fields agreed before this repair.
Delivery tooling builds the replacement commit on current main.

The advisory about the unpinned natural cohomology isomorphism was not a required
change. The existing natural-isomorphism assertion is retained as independently
accepted in this return.

## New nodes

`def-sf-proetale-locally-finite-free-module` attaches the EXISTING declaration
`AlgebraicGeometry.ProEtale.CondensedRing.LocallyFree` in
`Sheaf.Paper.ContinuousLocallyFreePullback` with `existing: true`, no new module,
and no `lean.file`. For arbitrary `X`, arbitrary associative unital ring object
`R` in its abelian pro-etale sheaves, and internal `R`-module `P`, the predicate
means there is a pro-etale scheme cover `C` such that for every member `s`,
`Mod.IsFree ((ProEtale.upperStar Ab (C.f s)).obj R)` holds on the corresponding
`mapMod` inverse image of `P`. The existing `Mod.IsFree` is exactly existence of
an isomorphism to `finiteFree R n` for some natural `n`, the finite biproduct of
regular modules; it includes rank zero and allows ranks to vary with `s`.
The coefficient universe is u+1 on `X : Scheme.{u}`. The predicate is defined
for arbitrary ring objects, so it applies directly to the inverse image of
`padicAlgClSheaf`, without an extra condensed-ring comparison assumption.
Its dependencies cite the recorded pro-etale site, general module notion, and
`def-sf-proetale-ring-sheaf-operations` for the exact existing `mapMod` inverse
image. The latter is `ProEtale.ringSheafInverseImage` in
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`, whose data and signature
were read along with the existing `LocallyFree` and `Mod.IsFree` definitions.

Sources: Stacks `sites-modules.tex`, `definition-site-local` item (2), the
final-object characterization Tag 03DN item (2), and Tag 03DO, alongside the
Bhatt--Scholze Section 6.8 specialization already cited by the predicate module.
The latest blueprint's internal-Hom/evaluation paragraph and native refinement
step 5 supply its use here. `blueprint_refs.py ancestor` reports no ancestor id,
so the new node retains null ancestry and prefixes the item's inherited via list
with the item itself.

Searches before attaching the node, reproduced in its `mathlib_searches`:
LeanSearch query “A module over an arbitrary ring object in pro etale abelian
sheaves is locally finite free if a pro etale scheme cover makes it a finite
direct sum of the regular module” returned eight finite-type/free-module hits;
LeanFinder query “An internal module over a ring object on the pro etale site is
locally finite free on a pro etale scheme cover, allowing locally varying finite
rank and zero rank” returned eight finite-generation/presentation hits. Neither
states this predicate. Mathlib grep `LocallyFree|IsLisseCoefficientModule` in
`AlgebraicGeometry` returned zero hits. Source grep for those names returned no
general upstream predicate. Sheaf grep found the exact existing declaration at
`ContinuousLocallyFreePullback.lean:31`. Recursive DAG grep found its uses but no
definition-node attachment. `blueprint_refs.py search locally finite free` found
94 blueprint hits, all with different scopes. `IsLisseCoefficientModule` was read:
it requires `condensedRingObj Λ X` and cannot take the arbitrary ring object in
this predicate. The new node reuses, rather than defines again, the exact
existing declaration specifically requested by the return.

## Statement corrected

This is a citation-only correction required by the return, not a mathematical
statement change. The old statement is stored verbatim in
`statement_change.old_statement`; the single text addition is the citation
`[def-sf-proetale-locally-finite-free-module]` after “pro-etale locally finite free
restrictions”. `old_stmt_deps` records current main verbatim. The previous
unlanded dependency on the pullback theorem is replaced with the definition node;
the other accepted added dependencies are retained. No proof text or proof
dependency changes. The full five-citer audit found by recursive grep is:

- `lem-sf-native-open-derived-tensor`: holds true. Uses equivariant K-flat resolutions and their forgetting; both assertions are unchanged.

- `lem-sf-native-proper-projection-realization`: holds true. Uses preserved equivariant K-flat/K-injective representatives; the new definition citation changes neither.

- `lem-sf-native-weil-open-proper-forgetting`: holds true. Uses inverse site equivalences and coefficient-preserving Frobenius pullback; those assertions are unchanged.

- `lem-sf-native-weil-scalar-frobenius-counit`: holds true. Uses exact derived forgetting of fixed-pair complexes; that assertion is unchanged.

- `lem-sf-weil-native-closed-forgetful`: holds true. Uses the action-site presentation, derived forgetting and bounded constructibility; the new node names exactly the existing local-free predicate.

The second reading of this repair checked all five uses without editing a citer.
It also compared the new node's full signature verbatim with the existing
abbreviation and checked empty schemes, zero rings, zero modules, rank zero,
varying ranks and the absence of an imposed common rank or condensed presentation.
The dispatch forbids other agents, so this is an explicit self-review; the
maintainer's independent immutable-head review remains the independent reading.

The first repair dry run required the current new-node schema key `import_flags`;
added the empty list and reran the prescribed dry run.
