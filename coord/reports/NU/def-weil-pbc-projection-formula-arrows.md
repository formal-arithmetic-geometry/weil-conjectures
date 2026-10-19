## Worker report

The delivery states definition 1264 in `Sheaf.Paper.ProjectionFormulaArrows` and repairs
one recorded dependency under section 1(B). The main declaration is
`SheafOfModules.ringedProjectionFormulaArrows`. It returns the ordered pair `(pi,rho)`
with the source and target of both arrows written explicitly. No mathematical node
statement is changed, no new node is introduced, and no downstream theorem is used.
The previous WAITING report is superseded.

Source read: blueprint proper-base-change definition 1264, and the expanded DAG
statement specifying its chain representatives; Stacks Cohomology on Sites 07A4,
`lemma-pullback-tensor-product`, including the final comparison of total complexes;
0G7E, `lemma-pullback-K-flat`; and the recorded ordinary 03EL comparison interface.

Hypotheses and clauses, matched to Lean:

- Small sites and size convention: explicit universes `u,w`, `C,D : Type u`,
  `Category.{u}` structures, topologies `JC,JD`, coefficient sheaves in
  `CommRingCat.{u}`, module sheaves in universe `u`, and both
  `HasDerivedCategory.{w}` binders. This is the small-site presentation within the
  chosen module universe. There is no independent smaller test-algebra universe.
- The ringed-topos morphism: `uInv,uPush,adj`, finite-limit preservation, the existing
  `AlgebraicInverseImage I`, and `c : RI ⟶ S`. `uStar,hobj,hmap` identify module
  pullback on objects and maps with scalar extension of that inverse image.
  `V,am` present its module right adjoint and adjunction. These are presentations
  of the functors in the statement, not arbitrary maps substituted for them.
- Unbounded derived categories are Mathlib `DerivedCategory` of the same
  `SheafOfModules` categories. The recorded general `ringedSiteModules` is their
  transparent abbreviation; no alternate module or derived category is constructed.
- Derived pullback: `LF,epsilon,hLF,computeL`. The last binder states the specified
  computation on K-flat flat-term complexes. `PR,PS,hPR,hPS` are precisely those
  full subcategories. Tensor functors `TR,TS` and natural representative isomorphisms
  `rR,rS` identify tensor with the existing signed total tensor on those complexes.
- Derived pushforward: `RF,eta,hRF,computeR`. `hRF` is the same universal
  factorization bijection as the recorded K-injective total-derived theorem;
  `computeR` is its comparison on K-injectives, transported from `Qh` to `Q`.
- Canonical derived adjunction: `adjD,canonicalAdj`. The equation says that on every
  K-injective `K`, the derived counit composed with the right-derived comparison is
  the left-derived comparison followed by the localized ordinary chain counit.
  Since every derived object admits a K-injective representative, this fixes the
  counit and hence the adjunction from the ordinary module adjunction. The transport
  is explicit in `derivedPullbackComplexComparison` and
  `derivedPushforwardComplexComparison`, using `quotientCompQhIso` and
  `mapHomotopyCategoryFactors`.
- The object `E`, K-injective representative `K,hK,repE`, and bounded coefficient
  complex `F,P,hbounded` are exactly the chosen data in the node. `P` is the recorded
  `StrictPerfectCoefficientPackage`: its `N,i,p,splitting` give each finite rank,
  inclusion, projection and relation `i_r ≫ p_r = 1`. Neither map is assumed to be
  a chain map to a preassigned free complex.
- The canonical comparison is `ringedTopoiCanonicalDerivedTensorComparison`,
  selected from the unique representative characterization of the repaired
  dependency. Its ordinary input `k` is a `CanonicalRingedTensorComparison`, whose
  `q_one` and `pure` equations fix scalar insertion and generalized pure tensors.
  In particular this is not a bare choice of natural isomorphism.
- `pi` is `derivedProjectionFormulaMate LF RF adjD TR TS alpha E (Q.obj F)`.
  Its body is exactly `adjD.homEquiv` applied to `alpha.hom.app` followed by
  `TS.map (counit_E, identity)`. This matches both displayed arrows and their order.
- The ordinary arrow `t_{M,P}` is `tensorAdjunctionMate`, defined by the identical
  ordinary adjunction formula. The free inverse `q_{M,N}` is
  `tensorAdjunctionFreeInverse`: it inverts that specified mate, with its invertibility
  stated in `tensorAdjunctionMate_free_isIso`. The ordinary unit normalization is
  supplied by `canonicalRingedTensorComparison_unit`; it is needed in rank one.
  Additivity and right-adjoint finite-product preservation give every finite rank,
  including zero.
- The splitting formula for every ordinary term is the real definition
  `tensorAdjunctionRetractInverse`. Its body, in diagrammatic order, is
  `V.map (1 ⊗ L.map i) ≫ q ≫ (1 ⊗ p)`, exactly the node's formula. The corresponding derived definitions are `derivedProjectionFormulaFreeInverse`
  and `derivedProjectionFormulaRetractInverse`. The former inverts the specified
  free mate, with its finite-sum isomorphism instance; the latter composes
  `RF(1 tensor LF(i_r))`, that inverse, and `1 tensor p_r`. For degree-zero images of
  sheaf terms these are precisely `rho_N` and `rho_{F^r}`. Their chain representatives
  are the ordinary formulas used in the total construction. No arbitrary inverse
  family is a parameter.
- The complexes called `A,C,J,B` in the node are respectively the body term `A`,
  `CochainComplex.mapBifunctor A F (curriedTensor ...)`, the body term `J`, and
  `(V.mapHomologicalComplex ...).obj J`. `mapBifunctor` is the dependency's actual
  tensor total complex and includes differential `d_I tensor 1 + (-1)^a 1 tensor d_F`.
- `StrictPerfectCoefficientPackage.isKFlat_flat` states the flat-retract and bounded
  K-flat assertions for `F`. The repaired comparison's preservation clause gives
  the corresponding assertions for `pullF`. The helper
  `tensorAdjunctionTotal_target_isKInjective` states the K-injectivity of `J`, by the
  recorded bounded split-free tensor result; no boundedness of `K` is imposed.
- The canonical representatives of derived tensors with just one K-flat factor
  are `mixedTensorRepresentative`. Its existence theorem characterizes its square
  on *every* K-flat flat-term resolution of the other factor, and asserts uniqueness.
  Thus its chosen isomorphism is determined, rather than chosen from an unspecified
  existence. `eA,eF,eC,eB` in the body combine precisely these tensor comparisons,
  `repE`, `computeL` and the K-injective comparison `computeR`.
- `tensorAdjunctionTotal` constructs the forward chain mate from the explicit
  total pullback comparison and the termwise ordinary counit. Its inverse
  `tensorAdjunctionTotalInverse` has real data, using the uniquely determined inverse
  of that chain map. `tensorAdjunctionTotalInverse_summand` states, for every
  `a+r=n`, that precomposing its degree component by `V.map` of the tensor coprojection
  gives `s_{a,r}` followed by the target coprojection. These are exactly the
  coprojections of the node's canonical finite-sum identification. Their universal
  property identifies this inverse with the specified finite-total chain map.
  The proof docstrings give both differential compatibilities and their common sign.
- Finally `rho` is literally `eB.hom ≫ Q.map s ≫ eC.inv`. Thus its source is
  `Rh_*(E tensor Lh^*F)` and target is `Rh_*E tensor F`, under the displayed
  canonical identifications, as required. It is constructed at chain level, not
  by assuming the downstream derived projection formula.

Dependency declarations inspected and used (directly or through their public imports):

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `Qh`, `quotientCompQhIso`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Paper.StrictPerfectCoefficientPackage`:
  `SheafOfModules.StrictPerfectCoefficientPackage` and its `N,i,p,splitting` fields;
  the module's localized representative record was also read.
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`:
  `SheafOfModules.ringedTopoiDerivedTensorPullback` (old interface, retained as an import).
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`:
  `CategoryTheory.preDerivedAdjunctionGeneral`.
- `Mathlib.CategoryTheory.Adjunction.Limits`:
  `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `ιMapBifunctor`; `HomologicalComplex.mapBifunctorDesc`, `mapBifunctorMap` from Bifunctor.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`:
  `CochainComplex.isKFlat_of_boundedAbove_flat`.
- `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`:
  `CochainComplex.isKInjective_mapBifunctor_of_bounded_splitFree`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `CategoryTheory.Adjunction.mapHomologicalComplex` and `mapHomotopyCategory`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`:
  `SheafOfModules.module_pullback_tensor_iso`, including its final generalized pure-tensor
  equation, not merely the existence of the isomorphism.
- Supporting recorded interfaces read:
  `Sheaf.Paper.RingedTopoiDerivedPullback.ringedTopoiDerivedPullback` (declaration
  namespace `SheafOfModules`), `SheafOfModules.site_derived_tensor_descent`, and
  `SheafOfModules.AlgebraicInverseImage`. The monoidal preadditivity proof is obtained
  from the existing `SheafOfModules.tensorClosed`, not independently postponed.

Edge cases checked mathematically: rank zero uses empty products and zero maps;
rank one uses the ordinary unit normalization and detects a negative comparison;
zero coefficient complexes and the zero ring give the unique zero maps. Negative
and arbitrarily shifted bounded intervals are allowed. The representative `K` and
object `E` are unbounded. Differentials of `F` need not vanish. A nonflat coefficient
map such as integers to F_2 is permitted: only K-flat replacement and flat-term
preservation are used, never flatness of the ring map. Empty sites are allowed.
There is no characteristic restriction and no assumption of enough points.

Searches executed in this worker session:

- `msearch.py`, LeanFinder, "canonical derived projection formula counit mate finite perfect
  tensor ringed topoi": eight hits, including Mathlib derived-counit declarations and
  ordinary module pushforward counit formulas; none defines this finite-total pair.
- `msearch.py`, Loogle, `CategoryTheory.Adjunction.homEquiv`: twelve hits, including the
  generic hom equivalence and its unit/counit formulas. The construction uses that API.
- `msearch.py`, grep, `projectionFormula|projection_formula|mapBifunctor`, subdirectory
  `Algebra/Homology`: 25 hits on existing total-complex APIs; these are used.
- `msearch.py`, LeanSearch, "derived tensor projection formula canonical counit map":
  unavailable, Internal Server Error; recorded as unavailable, not a negative result.
- `rg` on project Lean and upstream WeilConjectures for `projectionFormula|projection_formula`:
  specialized scheme/etale/pro-etale interfaces, not this ringed-topos construction.
- Exact node-id grep on upstream WeilConjectures: no result.
- `rg` for the proposed names `tensorAdjunctionMate`, `ringedProjectionFormulaArrows`,
  `CanonicalRingedTensorComparison`, `mixedTensorRepresentative` across Mathlib,
  upstream and project Lean: no existing declaration with those names.
- Source searches for `mapBifunctor`, coprojections, total descent, monoidal additivity,
  product morphisms and `quotientCompQhIso` found the precise APIs used in the files.

Every new theorem proof is `sorry`; every definition contains real data. Existence
choices are only of an object uniquely determined by the displayed universal or
representative characterization, or a proof of a Prop. The helper statements all
belong to the canonical comparison and the explicit chain construction of the two
owning nodes, and are listed in their `lean.declarations` records with source and
blueprint docstrings. No proof or construction of the downstream
`lem-weil-pbc-ringed-projection-mate-exact` is assumed.

## Dependency modules

`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` receives
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback` and the primary theorem
`SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback`.
Only its `lean` field changes. The old `Nonempty (TR ⋙ LF ≅ (LF.prod LF) ⋙ TS)`
did not determine the canonical comparison: for an identity morphism over the
integers, both the identity and negative identity natural isomorphisms have that
bare type, but only the first has the ordinary pure-tensor normalization.
The repair retains K-flat flat-term preservation, and adds a unique comparison
whose square on all pairs of K-flat representatives is the image of the explicitly
constructed total chain comparison. Its ordinary comparison includes generalized
pure-tensor equations, scalar insertion of 1, and unit normalization. This is the
construction in Stacks 07A4, not a new downstream projection-mate hypothesis.
The old module is preserved and imported, so existing consumers can still use it.


## Second reading by NU

I independently read the item's full DAG statement and blueprint definition 1264,
the dependency node and both delivered modules, and Stacks `sites-cohomology.tex`
Tags 07A4 and 0G7E, together with `sites-modules.tex` Tag 03EL. In 07A4 the
hypotheses are an arbitrary morphism of ringed topoi and arbitrary unbounded
derived objects; 0G7E requires K-flat complexes with flat terms, not flatness of
the coefficient-ring map. The blueprint's terse last sentence is expanded in
the existing node by actual chain representatives. Neither node's mathematical
statement was changed by this delivery or by this reading.

My object/hypothesis/conclusion list, matched to the Lean:

1. Small sites in the chosen size convention: `C,D : Type u`,
   `Category.{u} C`, `Category.{u} D`, `JC,JD`; coefficient sheaves
   `R,S,RI : Sheaf ... CommRingCat.{u}`. `HasDerivedCategory.{w}` specifies
   the localization's morphism universe independently of the site universe.
   Verdict: the small-site presentation used by the recorded dependencies,
   with no lower bound imposed on ranks, support degrees, or characteristic.
2. The ringed-topos morphism: `uInv,uPush,adj`,
   `[PreservesFiniteLimits uInv]`, `I : AlgebraicInverseImage uInv R RI`,
   `c : RI ⟶ S`. I opened `AlgebraicInverseImage`: its underlying ring iso,
   generalized-element ring-operation equations, module functor, underlying
   natural iso and module-operation equations identify the algebraic lifts.
   Thus `RI` is the inverse image of R, not a separately arbitrary coefficient
   ring. Verdict: matches the morphism and ring-map hypotheses.
3. Module pullback and direct image: `uStar,hobj,hmap` specify scalar extension
   on objects AND morphisms; `V,am` specify its right adjoint. The additive
   instances are the automatic additivity of these adjoints between abelian
   categories. Verdict: exactly h-star and h-push, up to the given presentations.
4. The unbounded module derived categories: `DerivedCategory (SheafOfModules ...)`
   with `Q,Qh`. I read `ringedSiteModules` and its transparent Mathlib alias;
   it is this same sheaf-module category. Verdict: no alternate category.
5. Derived pullback and tensors: `LF,epsilon,hLF,computeL`, `PR,PS,hPR,hPS`,
   `TR,TS,rR,rS`. The two predicates are equivalent to K-flatness with flat
   terms, not stronger classes. I read the recorded derived-pullback and
   `site_derived_tensor_descent` signatures. `rR,rS` are the specified natural
   representative comparisons, transported from homotopy to complex Q.
   Verdict: the source's K-flat computation, not bounded derived categories.
6. Canonical comparison: `k : CanonicalRingedTensorComparison` fixes insertion
   of 1 (`q_one`) and generalized pure tensors (`pure`), as in 03EL.
   `ringedTopoiCanonicalDerivedTensorPullback` retains K-flat preservation and
   gives `∃! alpha` with the full displayed square on every K-flat flat-term
   pair. The square uses `epsilon`, `rR`, `rS` and the inverse of the explicit
   total ordinary comparison. `ringedTopoiCanonicalDerivedTensorComparison`
   chooses that unique object. Verdict: the repaired dependency fixes the
   canonical map, including its sign; a negative natural iso cannot pass.
7. Derived pushforward and adjunction: `RF,eta,hRF,computeR`, `adjD,canonicalAdj`.
   I opened the K-injective total-derived statement and the general
   pre-derived-adjunction statement. `hRF` is their factorization bijection;
   `computeR` is the K-injective comparison transported through
   `quotientCompQhIso` and `mapHomotopyCategoryFactors`. `canonicalAdj` fixes
   the derived counit by the ordinary chain counit on every K-injective K.
   Every derived object has such a representative, so this determines the
   canonical adjunction. Verdict: no arbitrary derived adjunction substituted.
8. Input object and coefficients: `E,K,hK,repE`, `F,P,hbounded`. I opened
   `StrictPerfectCoefficientPackage`: `N,i,p,splitting` are exactly the chosen
   finite-free retractions, with relation `i r ≫ p r = 1`. Boundedness is an
   arbitrary finite interval of integers. Verdict: K and E remain unbounded;
   no chain-map condition on the degreewise splitting has been introduced.
9. First arrow: the first component is `derivedProjectionFormulaMate ... alpha
   E (Q.obj F)`. Its comparison and counit are those of items 6 and 7, in that
   order. I found and opened upstream `Adjunction.rightAdjointProjectionMap`
   and its `rightAdjointProjectionMap_app_app` equation. I changed this helper
   to call that constructor, supplying only the curry/uncurry adapter and
   naturality from `alpha.hom.naturality`. Verdict: the same adjunct required
   by the node, now reusing the upstream generic construction.
10. Free inverse: ordinary `tensorAdjunctionFreeInverse` inverts precisely
    `tensorAdjunctionMate`; `tensorAdjunctionMate_free_isIso` requires
    simultaneous naturality and the ordinary unit normalization. I checked
    the latter's displayed right-unitor equation in
    `canonicalRingedTensorComparison_unit`. Finite sums are finite products;
    the imported adjunction limit-preservation API applies also to rank zero.
    The derived `derivedProjectionFormulaFreeInverse` likewise inverts the
    specified derived mate. Verdict: q and rho_N are fixed inverses.
11. Retract formula: `tensorAdjunctionRetractInverse` is literally
    `V.map (1 tensor L.map i) ≫ q ≫ (1 tensor p)`.
    `derivedProjectionFormulaRetractInverse` gives the corresponding displayed
    derived formula. Verdict: matches all maps, objects and composition order;
    there is no arbitrary inverse family parameter.
12. Chain representatives and signs: body `A` is termwise V(K), `pullF` is
    termwise uStar(F), `J` is `mapBifunctor K pullF`, and B is termwise V(J).
    C is `mapBifunctor A F`. I read the recorded `mapBifunctor` tensor node,
    bounded-above-flat K-flat theorem and split-perfect K-injective theorem.
    The package's K-flat/flat-term helper and the dependency preservation clause
    give the required two K-flat factors; `tensorAdjunctionTotal_target_isKInjective`
    applies the bounded split-free argument to J. Verdict: the required signed
    total differential, without assuming bounded K or zero d_F.
13. Finite total inverse: `tensorAdjunctionTotal` is the chain adjunction mate
    formed from the actual total pullback comparison and ordinary chain counit.
    `tensorAdjunctionTotalInverse` inverts that uniquely invertible chain map.
    Its `_summand` theorem asserts for EVERY `a,r,n,h : a+r=n` that the map
    after the V-image of the source coprojection is s_(a,r) followed by the
    target coprojection. Its proof docstring explains cancellation of t and
    compatibility with each differential with the same sign (-1)^a.
    Verdict: the finite-total map specified in the node, not an assumption of
    the downstream derived projection-mate theorem.
14. Representatives of the output: `mixedTensorRepresentative_existsUnique`
    fixes its iso on every K-flat flat-term resolution of the other factor.
    The defining square is typed in the right direction: `TR(Qp,1) ≫ z`
    equals `rR.inv ≫ Q(total(p,1))`. Therefore `eA,eF,eC,eB` are the required
    canonical identifications. The second component is exactly
    `eB.hom ≫ Q.map s ≫ eC.inv`, with the opposite source and target to pi.
    Verdict: both clauses of the ordered output pair match the node.

Edge cases: `Fin 0` is allowed and uses the empty finite product; rank one
checks the ordinary unit and rejects a sign-twisted tensor comparison. The zero
complex, zero ring and empty site are admitted. Finite support can be empty or
arbitrarily shifted through negative integers; d_F can be nonzero. E and K have
no bounds. There are no Noetherian, enough-points, nonzero-ring, characteristic,
or ring-map-flatness assumptions (in particular Z to F_2 is allowed). Sites are
small in u; their module sheaves and set-valued inverse images use that same
chosen bound, and the derived-category universe w is explicit. No variable or
universe is left unbound.

Independent searches in this reading:

- LeanFinder: `tensor projection morphism right adjoint perfect complex counit`
  returned eight hits (complex unitors, Grothendieck tensor adjunctions, and
  a condensed projectivity criterion); none gives this ringed-topos arrow pair.
- Loogle: `CategoryTheory.Adjunction, "tensor"` returned ten hits, including
  monoidal-adjunction identities and rigid tensor adjunctions. None states
  this representative construction.
- Search-service grep: `rightAdjointProjectionMap|tensorAdjunctionTotal|mixedTensorRepresentative`
  returned zero hits. This was not taken as evidence about upstream sources.
- LeanSearch: `canonical projection map from tensor of derived pushforward to
  derived pushforward of tensor` returned Internal Server Error; unavailable.
- Independent local rg through Mathlib CategoryTheory, project Sheaf and
  upstream WeilConjectures found `Adjunction/ProjectionMap.lean` and
  `ProjectionMapCompat.lean`. I read their actual definitions and types.
  The former supplies the generic right-adjoint mate, now used as described
  in item 9. Other hits concern specialized scheme/etale/pro-etale operations
  or assume projection isomorphisms; none supplies this general ringed-topos
  finite-total inverse. Existing Mathlib total-complex and localization APIs
  continue to be used.

Repair made: the derived generic mate helper now calls the existing upstream
projection-map constructor; the new import is used by that call. This removes
an avoidable independent implementation. The exported signatures and both node
statements are unchanged. The ordinary helper takes only objectwise comparisons
and is not the same interface as the upstream natural-bifunctor constructor;
its formula remains the ordinary adjunction hom equivalence. All postponed
helper theorems remain named, recorded in their owning node's `lean.declarations`,
and have source/blueprint and full proof docstrings. Definitions have actual
data, or choose only uniquely characterized objects/inverses. No target or
unit statement was changed, no new definition node was needed, and no wait on
the downstream projection-mate theorem was introduced.

Validation after the second-reader repair: the required server-only scompile
command compiled BOTH delivered files cleanly, with no errors or warnings.
`RingedTopoiCanonicalTensorPullback.lean` took 34.6 seconds and
`ProjectionFormulaArrows.lean` took 34.7 seconds; every invocation used nice 19,
two threads and the 60-second per-file limit. Imported side dependencies also
compiled cleanly. The project signature reader agrees with both recorded
`lean.statement` fields (it records declaration keywords without modifiers).
All Lean lines remain at most 100 characters.


## Independent maintainer correction

The immutable delivery at f79ab05d6969261a2beac7f40c54471b8b9eae45 was
independently reviewed against the full node, all fourteen statement dependencies,
the source passages, both modules, the exact dependency declarations, and the
pilot gates. The detailed review is recorded in the maintainer review.md.

One strict local-proof pilot issue (H6) was repaired in
`CategoryTheory.derivedProjectionFormulaMate`: replace the two inline naturality
proof scripts by the existing Mathlib constructions
`Functor.curry.map alpha.hom` and `(Functor.curryObjProdComp L L TS).hom`.
The upstream `Adjunction.rightAdjointProjectionMap` still supplies the mate.
The comparison has identity components, so this is the same mathematical arrow.
Every exported signature is unchanged; the recorded lean.statement remains
verbatim correct. All mathematical theorem proofs remain sorry and all
definitions contain actual constructions or uniquely characterized choices.

The canonical tensor dependency repair, counit mate, finite-free/retract formulas,
finite-total inverse and representative identifications agree with definition
1264. Zero ranks, empty support/sites, zero rings, negative shifts, nonzero
coefficient differentials, unbounded E, and nonflat coefficient maps remain
allowed. No statement correction, new node, universe restriction or downstream
wait is needed.

The maintainer reproduced the immutable server-only scompile with no errors or
warnings (34.2 seconds for RingedTopoiCanonicalTensorPullback and 34.8 seconds
for ProjectionFormulaArrows), then compiled the complete replacement against
the immutable sibling module. That second run passed without errors or warnings,
35.0 seconds per delivered module. Required side imports compiled in the private
overlay. Every invocation used nice 19, two threads, and 60 seconds per file.
No project clone, live Lean file, branch head or snapshot file was modified;
no local Lean compiler or global/lake build was used.
