## Worker report

The item states the normalized scalar-change direct-image counit mate, its identification
under internal/section reconstruction, the scalar-unit equation, and compatibility with
inverse integer multiplication. The item statement, statement dependencies, proof and
proof dependencies are unchanged. There is no statement dispute or statement correction.

This repairs returned delivery c6b132a83f98, point H13. The original item statement
and all its comparison formulas are retained. The witness structure and its Normalized
predicate now live in the item module. The packet no longer supplies a dependency node
or InternalSectionScalarData module, so the landed Q26 dependency record, its module,
its five declaration names and its authorship remain unchanged.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A morphism of commutative condensed rings a:R→S | R,S : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}, their MonObj and IsCommMonObj instances, a:R⟶S and IsMonHom a. These are the underlying sheaves and structures of Profinite.CondensedRing. |
| Any scheme morphism f:X→Y | X,Y : Scheme.{u}, f:X⟶Y; no property of f is assumed. |
| Small pro-etale sites in the module universe | Scheme.ProEt.topology T retains object universe u+1 and morphism universe u, with modules and derived morphisms in u+1. Explicit HasDerivedCategory binders are the existing section-realization convention; there is no equality of site object and morphism universes. |
| R_T=p_T*R, S_T=p_T*S, a_T=p_T*a | condensedRingObj and coefficientMap a T, through the existing scalar and geometric interfaces. |
| Coefficient isomorphisms c_R,c_S and their commuting square | The existing CondensedRing.pullIso and comapUpperStarIso use precisely condensedPullbackHom for each coefficient ring. map_coefficientMap_comp_condensedPullbackHom proves the square by naturality of upperStarFromPointComp. No unrelated coefficient identifications are parameters. |
| Extension of scalars is exact for T=X,Y | The two PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T)) binders. Extension already preserves finite colimits as a left adjoint. Exactness is not assumed on all schemes. |
| Termwise internal/section equivalences | ModuleRingedComparison.equivalence, derivedEquivalence and derivedFunctor; these are the fixed underlying-sheaf section equivalence and its localization. |
| Internal and section scalar extension, exact restriction and specified scalar adjunctions | dX,dY : ScalarData a T, with hX,hY : Normalized. The item-local witness structure repackages the existing dependency with every normalization. Their internalDerived/internalAdjunction and sectionPair.derived/adjunction are universal unbounded scalar pairs. derivedRestriction is localization of the ordinary identity-on-sections square; derivedExtension is normalized on every flat-term K-flat representative. These are the specified comparison data of the source, not additional mathematical assumptions: the dependency theorem asserts existence for every ring map without flatness. |
| Ordinary unbounded derived categories | Every complex is indexed by ℤ and every derived object is DerivedCategory; no bounded, complete or constructible subcategory appears. |
| Specified geometric adjunctions over R,S | normalizationInternalAdjunction and derivedAdjunction from the recorded section pushpull normalization and realization. |
| Canonical pullback/scalar tensor comparison | InternalPullNormalized and SectionPullNormalized pin the two isomorphisms by universal computation-counit equations using independently specified ordinary balancing. OrdinarySectionPullNormalized pins the ordinary balanced comparison on every object in the exact section-equivalence image; it is not defined from the derived internal isomorphism. Existence of both normalized comparisons is asserted, and the conclusions hold for every pair satisfying these equations, so these parameters are not arbitrary isomorphisms or potentially vacuous assumptions. |
| beta_C is the S-geometric adjunct of theta followed by L_X(epsilon_C) | internalBeta is exactly normalizationInternalAdjunction S f .homEquiv applied to b.hom at Rf_*C followed by dX.internalDerived.map of the R-counit. sectionBeta independently uses the same formula and the section-ring geometric adjunction. |
| Reconstruction sends beta_C to that section-ring map | The first equality in the concluding conjunction explicitly conjugates internalBeta by derivedExtension and derivedPushComparison and equates it to sectionBeta at bar C=(derivedEquivalence R X).functor.obj C. |
| Use the adjunction-compatible d of ring-sheaf change | OrdinarySectionRestrictionNormalized pins r to the actual identified-coefficient inverse-image comparison and identity-on-sections scalar comparisons on every equivalence image. Existence and uniqueness of both ordinary comparisons are asserted, and all remaining conclusions are quantified over their normalized realizations. sectionRestrictionPull localizes it. sectionRestrictionPush is its specified geometric adjunction mate, precisely the Hom-transpose characterization of proEtaleRingSheafChangeAdjunction, expressed in the fixed ModuleRingedComparison presentation. Its invertibility is explicitly asserted. Thus d is fixed independently of either scalar/pullback isomorphism and of beta, rather than being an arbitrary map or defined to force the unit identity. |
| t=d after U_Y(beta) | sectionT is scalarDerivedRestriction.map sectionBeta followed by sectionRestrictionPush.app at L_X(bar C). |
| t after eta_M equals Rf_*(eta_barC), M=Rf_*barC | The second equality in the concluding conjunction is sectionPair.adjunction.unit.app at Rf_*barC followed by sectionT, equal to derivedPushforward R f .map of the X-scalar unit. Lean composition reads left to right. |
| If s∈ℤ is invertible in S, t intertwines inverse multiplication | IsIso (s • 𝟙 S) expresses invertibility of integer multiplication on the condensed coefficient ring. This is equivalent to s being a unit: the inverse applied to 1 supplies its inverse section, and conversely multiplication by that inverse supplies the inverse morphism. The last clause supplies automorphisms v,w with v.inv and w.inv equal to multiplication by s on U_YL_YM and U_XL_XbarC. Thus v.hom,w.hom are the unique inverse multiplication maps, and the displayed equation is v.hom≫t=t≫Rf_*(w.hom). This includes the zero coefficient ring. |
| No boundedness, quasi-compactness, properness, constructibility or completeness | No such binder or restricted category is present. |

The main declaration docstring contains the full six-step node proof: normalize the
balanced map, transport its adjunct, use the restriction/geometric adjunction square,
compute the scalar-unit square before sheafification, compare both geometric adjuncts,
and invert the integer-multiplication square. No theorem is proved in the delivery.
All helper data are real composites, localization maps or adjunction transposes.
The ordinary comparison isomorphisms are asserted to exist uniquely with explicit
component formulas; no data are chosen from existence. Their formulas cover every
object in an essentially surjective equivalence image, so there is no freedom to
choose an unrelated comparison.

Dependency declarations used:

- Sheaf.Topology.ProfiniteCondensedRing: Profinite.CondensedRing (underlying sheaf and ring-object structures).
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: condensedRingObj, coefficientRing, condensedPullbackHom and upperStarFromPointComp.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients: coefficientMap, its coefficient-square naturality theorem, CondensedRing.pullIso and comapUpperStarIso.
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence: sectionRingSheaf and sectionModuleEquivalence.
- Sheaf.CategoryTheory.InternalSectionScalarAdjunction: sectionScalarMap, InternalSectionScalarAdjunction and internal_section_scalar_adjunction. Its existing existential witnesses are repackaged in the item module as described below.
- Sheaf.Algebra.Homology.ScalarInternalHomData: scalarModules, scalarRestriction, scalarDerivedRestriction, ScalarDerivedPair and scalarPairComplexComparison.
- Sheaf.Paper.SectionDerivedPushpullNormalization: normalizationInternalAdjunction and sectionDerivedPushpullNormalization, with the publicly imported fixed ordinary/derived operations, geometric comparisons and adjunctions of SectionModuleOperationsData and SectionDerivedRealization.
- Sheaf.Paper.SectionDerivedTensorNormalization: section_derived_tensor_normalization; it fixes the actual internal versus section-ring derived tensor/pullback comparison.
- Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction: proEtaleRingSheafChangeAdjunction; the specified d is identified by its exact adjunction-mate equation in the section realization, not by a choice of an isomorphism.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations reexports the full arbitrary-ring-sheaf operations of ProEtaleOperationsCanonicalAdjunction. The constant specialization in the primary record does not restrict those publicly imported operations.
- Mathlib DerivedCategory/Q and SheafOfModules.restrictScalars are the recorded localization and scalar-restriction definitions; the size and scheme-conventions nodes introduce no separate definienda.

The stated proof dependencies are imported without public when not already statement
imports. The proof dependency lem-sfb-internal-scalar-pullback-normalization has no Lean
record in the live tree, so no module import exists for it. Its exact-scalar special case
is the normalization of the comparisons stated here; this delivery does not add a proof
or wait for that node.

Edge cases checked against the definitions and statement: a=id and f=id retain the
actual adjunction units/counits and balancing maps; C=0 and the zero ring are permitted;
X or Y may be empty; s=±1 and s invertible in the zero ring are included; arbitrary
unbounded complexes are quantified throughout. The module-site object universe remains
u+1 and its morphism universe u. No all-schemes flatness assumption was used to satisfy
the older derivedComapLowerStarIso API. The section d instead uses the independent
identified-coefficient inverse-image square and its geometric mate.

Searches made before defining the helper interfaces:

- msearch leanfinder: "The extension of scalars comparison with derived direct image commutes with the scalar adjunction unit, using the pullback tensor comparison and geometric counit". Eight results, including ordinary ModuleCat scalar-adjunction formulas and sheaf pullback-unit transposes; no complete internal/section unbounded statement.
- msearch loogle: "CategoryTheory.Adjunction.homEquiv, CategoryTheory.Adjunction.unit". Twelve ordinary categorical identities; no complete target statement.
- msearch grep: "extendScalars|restrictScalars" in Algebra/Category/ModuleCat/Sheaf. Ten hits, including the actual restriction functor, which is reused.
- msearch leansearch: "derived extension restriction scalar unit direct image adjunct pullback tensor comparison". Eight ordinary module-scalar-adjunction results; no target statement.
- rg in lean/WeilConjectures and lean/Sheaf: scalar-change/direct-image names and scalar-unit/mate patterns. Found ChangeOfCoefficients, InternalDerivedScalarComparisons and the existing section scalar/geometric normalizations. Reused their operations; no declaration states this whole node.
- rg for the exact blueprint id in lean/WeilConjectures: no existing declaration.
- Additional msearch leanfinder query: "Canonical internal and section scalar pullback comparisons, their geometric counit mates, and the restricted direct-image comparison composite". Eight ordinary pullback results, no complete comparison-data interface.
- Additional msearch leansearch query: "canonical scalar geometric counit mates internal and section modules comparison data". Eight ordinary counit results, no complete interface.
- Additional msearch grep query: "scalar.*(Beta|beta|counit)|scalar.*RestrictionPush" in CategoryTheory. No hits.
- Read local Stacks sites-cohomology.tex at lemma-pullback-tensor-product, lemma-adjoint and lemma-derived-pushforward-composition (Tags 07A4, 07A6 and 0D6E). These are unbounded comparisons and adjunctions, with no geometric finiteness assumption.

## Repair of H13

The dependency lem-sfb-internal-section-scalar-adjunction remains bound to the landed
Sheaf.CategoryTheory.InternalSectionScalarAdjunction module and all five original
Q26 declarations: sectionScalarMap, internalScalarGenerator, scalarInternalModules,
InternalSectionScalarAdjunction, and internal_section_scalar_adjunction. No dependency
record or dependency module is delivered. Existing consumers retain their complete API.

InternalSectionScalarData and InternalSectionScalarData.Normalized are now helper
definitions in Sheaf.Paper.ScalarChangeDirectImageUnit, listed in the item's
lean.declarations and carrying the item's blueprint identifier. They expose the same
eight data witnesses and nine clauses of the existing existential proposition: section
restriction, balanced extension generators, ordinary transpose, the universal internal
derived pair, computation on K-flat inputs, the localized ordinary internal unit,
localized restriction, extension on flat-term K-flat inputs, and derived transpose.
ScalarDerivedPair retains its own ordinary and derived normalizations. The generic
site universes and absence of a flatness assumption are unchanged. The separate
exists_internalSectionScalarData theorem is removed: existence is already the content
of the imported internal_section_scalar_adjunction, and no data are chosen from it.

The original main theorem signature and every scalar/pullback/mate formula are
unchanged. Only the helper ownership and corresponding import are repaired.

## Validation

The saved packet passed its initial mechanical dry run, which did not detect the
independent review's dependency-rebinding fault. After the ownership repair,
scompile.py compiled the sole module against the live published build in both sandbox
and library modes (38.7 s and 39.0 s), with no errors or warnings. Explicit
coefficient/site universes and the target category of internal restriction preserve
the distinct site object and morphism universes. The file has no temporary diagnostic
commands and no line over 100 characters. Its only theorem is
scalar_change_direct_image_unit, whose sole proof is sorry.

Self-check: the main theorem signature is verbatim equal to lean.statement; all
non-lean fields of the sole node copy equal the live node. The two moved helper names
are included in lean.declarations. A fresh search in live Sheaf, WeilConjectures and
DAG sources found no existing InternalSectionScalarData declaration. The dependency
record is not part of the delivery; the Q26 module and all five names remain intact.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
