## Worker report

The module `Sheaf.Paper.RingedDerivedSliceLocalization` states
`SheafOfModules.ringedDerivedSliceLocalization`. Its sole postponed theorem is the
item itself. Its helper structures and definitions carry actual data; no derived
functor or comparison is defined by choosing a witness of a mere existence theorem.
The theorem produces the global and local derived adjunction models existentially,
with their left/right universal derived transformations and the original-adjunction
normalization. Thus their functors are determined by universal properties.

Hypothesis and clause matching:

- The two small sites are `D C : Type u`, `[SmallCategory D]`, `[SmallCategory C]`,
  with Grothendieck topologies `K J`. The module universe is `u`, so the sites are
  small relative to module coefficients, as in the node's size convention.
- The presentation is `u : D ⥤ C`, `[u.IsContinuous K J]`, and
  `[PreservesFiniteLimits (u.sheafPullback (Type u) K J)]`. This is the given
  geometric inverse-image/direct-image adjunction, not an arbitrary additive functor.
- The coefficients are the actual commutative ring sheaves `R S`. The structural
  ring map is its adjunct `a : R ⟶ u_* S`. Adjunction recovers `f⁻¹ R ⟶ S`.
  No flatness or invertibility of this map is imposed.
- `V : D` is the target-slice object, and `u.obj V` is exactly U. The theorem
  produces the continuity instance for `Over.post u` on `K.over V` and
  `J.over (u.obj V)`. Its coefficient map `localizedRingedSiteMap u a V` has
  component `a.hom.app (op T.left)` at `T → V`.
- All four module categories are the recorded `SheafOfModules` specialization;
  the four `HasDerivedCategory.{w}` instances choose the localization morphism size.
  No boundedness of a complex is assumed.
- `RingedSliceDerivedImage u a` contains the left derived functor of Mathlib's
  actual module `pullback`, its `epsilon` and `IsLeftDerivedFunctor`; it also
  contains the right derived functor of the actual `pushforward`, its `eta` and
  `IsRightDerivedFunctor`. Its adjunction's `normalized` equation is exactly
  the canonical derived-adjunction normalization on cochain maps, using the recorded
  localization Q from cochain complexes at quasi-isomorphisms.
  These are output data, not hypotheses asking the consumer to supply the result.
  `ringedSliceModulePullback` and `ringedSliceModulePushforward` are definitionally
  Mathlib's existing functors; the named heads keep their additive-instance inference
  from matching unrelated functors. `ringedSliceModuleAdjunction` is the actual
  `pullbackPushforwardAdjunction`, with no new choice of adjunction.
- Restriction is the direct view `ringedSliceRestriction` of the already recorded
  `ringedDerivedRestrictionSized`, specializing
  `ringedDerivedRestrictionGeneral` to a small site and the underlying ring of R or S.
  It is the functor induced by the exact `SheafOfModules.overFunctor`.
  `ringedSliceRestrictionFactors` is its existing `mapDerivedCategoryFactors`
  isomorphism, with the module and derived-category presentations fixed explicitly.
  These helpers name the original functor and factorization; they construct no second
  restriction or comparison.
- `d.beta : e.right ⋙ jV ≅ jU ⋙ l.right` states the first displayed isomorphism for
  every M. As a natural isomorphism, it includes naturality in all derived arrows.
- `d.lambda : jV ⋙ l.left ≅ e.left ⋙ jU` is the inverse direction of the second
  displayed isomorphism; its inverse is the exact orientation used in the statement.
  It includes naturality in every N and every derived arrow.
- The first conjunct fixes beta on complexes: restriction of the universal
  right-derived map, followed by beta, equals the exact-restriction comparison,
  the ordinary sectionwise identity `ringedSlicePushforwardComplexIso`, and the
  local universal right-derived map. This prevents an arbitrary scalar multiple
  from serving as the supposedly canonical comparison.
- The comparison structure field `d.counit` is the counit square, explicitly
  `l.left.map (beta.hom.app M) ≫ εV = lambda.hom.app (e.right.obj M) ≫ jU.map ε`.
- The comparison structure field `d.unit` is the unit square, explicitly
  `jV.map η ≫ beta.hom.app (e.left.obj N) ≫ l.right.map (lambda.inv.app N) = ηV`.
  Together with the normalized derived adjunctions these fix the pullback comparison
  as the adjunction mate of beta.
- The last clause quantifies over every `t : R.obj.obj (op V)`. Its image is
  literally `a.hom.app (op V) t`. The objects on both sides are the existing
  `ringedSectionLocalization` on the corresponding slice, via `ringedSliceSection`,
  put in degree zero with `CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q`.
  The isomorphism `loc` has source the local derived pullback of R|V[1/t] and
  target S|U[1/a(t)]. It requires no global extension of t.
- The final generator equation normalizes loc against the actual localization
  unit. Its right side is the left-derived comparison followed by the chain map
  induced by `pullbackObjUnitToUnit` and the target's `ringedSectionLocalizationUnit`.
  This specifies the canonical scalar-extension localization isomorphism.

Dependency declarations read and used:
`CategoryTheory.RingedToposMorphism` in `Sheaf.CategoryTheory.RingedToposMorphism`;
`CategoryTheory.Precoverage.IsSiteForCoverings` in `Sheaf.CategoryTheory.SiteCoveringAxioms`;
`SheafOfModules.over`, `overFunctor`, and `Sheaf.over` in Mathlib's
`Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and `CategoryTheory.Sites.Over`;
`CategoryTheory.ringedSiteModules` in `Sheaf.CategoryTheory.RingedSiteModules`;
`DerivedCategory`, `DerivedCategory.Q/Qh`, and `HasDerivedCategory` in Mathlib's
`Algebra.Homology.DerivedCategory.Basic`;
`SheafOfModules.ringedTopoiDerivedPullback` in `Sheaf.Paper.RingedTopoiDerivedPullback`;
`SheafOfModules.ringedProjectionMateExact` in `Sheaf.Paper.ProjectionMateExact`;
`CategoryTheory.ringedLocalizationRing` and its module comparison in
`Sheaf.CategoryTheory.RingedSectionLocalizationRing`, retaining
`ringedSectionLocalization`, `ringedSliceSection` and `ringedSectionLocalizationUnit`;
`CategoryTheory.ringedDerivedRestrictionGeneral` and `ringedDerivedRestrictionSized`
in `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`.
The derived-restriction node was already landed and is added to the item's stmt_deps.
The already landed `def-weil-pbc-local-coefficient-localization` is also cited for
`CategoryTheory.localCoefficientOver_hasDerivedCategory` in
`Sheaf.CategoryTheory.LocalCoefficientLocalization`. This existing instance transports
the same derived-category data between forgetting commutativity before restriction
and after restriction; no new universe equality or independent derived category is imposed.
The ordinary comparison dependency is repaired as described below; its previous full
signature and docstring were read before deciding that its precoverage constraints
were inappropriate for this general statement. All recorded proof dependencies with
available modules are imported for the subsequent proof.

Edge cases: t=0 or nilpotent gives the zero localization on each side; the generator
normalization still makes sense. For t=1, the clause reduces to derived pullback of
the regular module, with its unit map. Zero rings and zero complexes are allowed.
A nonflat structural map such as Z→Z/2 is allowed: it is LF, not ordinary exact
pullback, throughout. Complexes unbounded in both directions are permitted. An
empty site cannot supply V, so that case is the correctly vacuous universally
quantified assertion. Identity site functors and nontrivial slices are included;
no `Final u`, preservation of site products, or subcanonical topology is assumed.
No STATEMENT-DISPUTED flag or statement correction is needed.

Searches made before writing (2026-10-17 UTC):

- msearch.py LeanSearch: “Restriction to a slice of a ringed site commutes with
  derived pushforward and derived pullback and sends section localization to
  localization at the image section”. Eight results, chiefly affine structure-sheaf
  localization lemmas, `SheafOfModules.pushforwardSections` and global sections;
  none states this general unbounded ringed-site theorem.
- msearch.py LeanFinder: “Derived slice restriction base change for module sheaves
  on ringed sites”. Eight results, including ordinary `SheafOfModules.over`,
  `pullback`, and `restrictScalars`; none is the requested derived assertion.
- msearch.py Loogle: `"SheafOfModules.overFunctor"`. Two exact ordinary restriction
  declarations, `overFunctor` and `overFunctorMap`; no derived comparison.
- msearch.py grep: `slice.*derived|derived.*slice|localization.*pullback` in
  Mathlib CategoryTheory: zero hits.
- rg in the source `WeilConjectures` for the item id and derived/slice patterns:
  no matching general theorem. rg in `lean/Sheaf` found the existing derived
  restriction and section-localization definitions, which are reused. A name
  collision search for every newly chosen main/helper name in Mathlib, upstream
  WeilConjectures, and lean/Sheaf found no declaration with these names.
- The underlying APIs were then read in Mathlib's `Sheaf/PullbackContinuous`,
  `Sheaf/PushforwardContinuous`, `Sheaf/PullbackFree`, `DerivedCategory/ExactFunctor`,
  and the recorded project modules. Stacks 099J's complete local Hom calculation
  and Tag 04J0's statement/proof were read in the local source files.

## Dependency modules

`lem-weil-pbc-localize-ringed-site-morphism` is repaired by
`Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`. The old record requires
`Precoverage.IsStableUnderComposition`, whose closure for arbitrarily repeated
indices is stronger than the current site's recorded covering axioms (see the
already landed `SiteCoveringAxioms` docstring). Requiring it on the consumer would
add a hypothesis absent from Tag 04J0. The new theorem works directly with the
Grothendieck topologies and the presented geometric morphism. It retains the slice
geometric morphism, inverse-image set and ring comparisons, the restricted ring
map's adjunction equation, both ordinary module natural isomorphisms and the
identity-on-sections direct-image normalization. An inverse-adjunct equation fixes
the ordinary pullback comparison too. `localizedRingedSiteMap` is the actual
componentwise restriction; `ringedSiteModuleMap` merely forgets commutativity of
this same map. Only this dependency's lean record changes. No new DAG node is added.

## Second reading by NN

Author's self-check, as required by the dispatcher brief's direct-delivery workflow;
independent review is left to the maintainer, and no second worker was started.
I reread the complete item node, the repaired dependency node, and both modules.
The checks above match every hypothesis and displayed formula. In particular,
lambda has the inverse orientation and is used with that orientation in both
adjunction equations; the local coefficient map sends t to a_V(t), with no global
section assumption. The localized objects are the original module sheafifications,
not an unrelated ring with an existence-only characterization. The derived model
contains both universal transformations and their adjunction normalization, so it
cannot be replaced by an arbitrary adjunction of unrelated functors. The repair
removes the stronger precoverage interface instead of adding it to the item.
A compile warning about a global maxHeartbeats setting was fixed by scoping it
to the expanded theorem. The additive instance's field was corrected to use its
implicit arguments. The derived model uses Q directly from cochain complexes,
removing unnecessary transports through the homotopy quotient. The reduced-budget
compiler diagnostic located a missing presentation transport for slice derived-category
instances. The binders now use the underlying-ring restriction, and the existing
`localCoefficientOver_hasDerivedCategory` supplies the commutative-ring presentation.


Resumption self-check (2026-10-17 UTC): the saved packet's first dry run found a
100000-heartbeat timeout while inferring the objects of the derived normalization
maps. Their source and target objects are now written explicitly. The normalization
uses the existing `CategoryTheory.ringedSliceComplexRestriction` from
`Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`, which fixes the same slice
coefficient presentation before elaborating its consumers; its landed node
`lem-weil-pbc-ringed-slice-evaluation-transpose` is added to stmt_deps. The library,
upstream and Mathlib name search found this existing helper, which is reused without
a duplicate declaration. Its full signature and docstring were read, and its
statement/proof dependencies have no path back to this item. The derived restriction
and its factorization remain the recorded exact-restriction construction. The
unit and counit equations also have explicit map objects; these are annotations of
the original objects, with no new hypothesis or altered mathematical clause.
The scoped type-transparency setting follows the reused restriction API.

The final presentation bundles beta and lambda with the exact two displayed
coherence equations in `SheafOfModules.RingedSliceAdjunctionSquare`: `d.beta`
and `d.lambda` are the two natural isomorphisms, `d.counit` is the counit square,
and `d.unit` is the unit square. This helper is output data, existentially
produced by the theorem. Its abstract functor parameters avoid repeatedly
elaborating the same large derived categories. An exact-name search across
Mathlib, upstream and Sheaf found no existing structure with this name; the
adjunction-square search found no matching bundle of these clauses. No equation
is dropped, and the helper has no postponed proof or arbitrary construction.
The factorization also reuses `CategoryTheory.ringedSliceLocalizationIso` from
the same published module, with its target quotient's coefficient category explicit.

The resumed compiler check resolved the coefficient-universe error and reached
the final localization-unit equation. That last derived map now also has explicit
source and target objects; every Q is assigned the already chosen localization
universe w. The temporary 100000-heartbeat diagnostic cap was removed, restoring
the compiler default, with the prescribed 60-second file limit unchanged.


Repair self-check (2026-10-17 UTC), return at f06488db3fef: the prescribed first
dry run reproduced the 60-second derived-module timeout. The module's instance
search size cap is reduced from 2048 to 256; all declarations, hypotheses,
normalizations and conclusions remain verbatim. The original scoped transparency
setting and all required imports are retained. The two-file scompile check passed
with no warnings or errors: ordinary library module 21.1 seconds, derived library
module 55.0 seconds. Both files retain one named postponed theorem each, real
definition data, explicit universes and variables, and lines of at most 100 characters.
The saved node signatures were compared directly with both theorem signatures and
match exactly. Current-base comparison shows only the authorized lean repair on
the ordinary dependency and lean plus added statement dependencies on the item.
The self-check reread beta's complex normalization, lambda's unit/counit squares,
and the degree-zero localization generator equation, including zero and nilpotent
sections, t=1, arbitrary nonflat structural maps, and unbounded complexes.


Repair self-check (2026-10-18 UTC), returned immutable head f06488db3fef:
the required first dry run reproduced the timeout in the library rendering of
`RingedDerivedSliceLocalization`. The repair removes redundant direct proof-only
imports, retaining every public statement dependency and the used API imports.
There are no changes to declarations, hypotheses, conclusions, canonical equations,
node statements, or node signatures. The prescribed two-file scompile check now
passes cleanly (derived library 55.2 seconds), and deliver2 --no-push passes
preflight and all per-file compiles at dry-run commit 8fed983675. I compared the
complete declaration bodies and the two recorded Lean signatures with the saved
packet; they are unchanged. The imports removed duplicate transitive imports or
proof-only tools not needed to elaborate the statements. The small-site and
coefficient universes, unbounded-complex clauses, both adjunction squares, beta's
ordinary-complex normalization and the localization generator equation all remain
exactly those checked above. No dependency, new node or statement correction is
needed for this compilation repair.
