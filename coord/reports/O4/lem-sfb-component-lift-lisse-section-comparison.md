## Worker report

Item: `lem-sfb-component-lift-lisse-section-comparison`. Module:
`Sheaf.Paper.ComponentLiftLisseSectionComparison`. The public theorem is
`AlgebraicGeometry.ProEtale.CondensedRing.component_lift_lisse_section_comparison`.
Its proof is `sorry`. The other 20 declarations are explicit constructions or predicates
belonging to the same comparison notion, including term-defined structural instances.
No dependency node is rewritten and no statement correction is needed.

Sources read: Hemo--Richarz--Scholbach, the local arXiv:2305.18131 PDF, Definition 3.3,
Lemma 4.1, the paragraph defining the relative tests and (4.1), Proposition 4.3(3),
its proof and (4.2), PDF printed pages 7--9; Stacks `sites-cohomology.tex`,
`lemma-dual-perfect-complex` (Tag 08JJ), lines 13048 onwards. The component-lift
normalization is the explicit agent-formulated consequence specified by the node,
not a quotation falsely attributed to HRS. The theorem docstring carries all seven
node proof steps, including their named dependencies.

Hypotheses and clauses, matched to Lean:

* Arbitrary commutative condensed ring: `Λ : Profinite.CondensedRing.{u}` and
  `[IsCommMonObj Λ.X]`. This is the recorded general ring-object abbreviation,
  with no chosen underlying topological ring, discreteness, completeness or admissibility.
* Extremally disconnected profinite base: `S : Profinite.{u}` and
  `[ExtremallyDisconnected S]`. The common base is universally quantified once.
* Affine U and V with w-contractible coordinate rings: each quantifier binds
  `U V : Scheme.{u}`, `[IsAffine U]`, `[IsAffine V]`, and
  `[IsWContractibleRing Γ(U, ⊤)]`, `[IsWContractibleRing Γ(V, ⊤)]`.
  The third scheme in the composition clause has the same hypotheses.
* Specified quotient component homeomorphisms: `eU : affineComponentSpace U ≃ₜ S`
  and `eV : affineComponentSpace V ≃ₜ S`. `affineComponentSpace` is the recorded
  profinite bundling of `ConnectedComponents`, not a second component space.
* Arbitrary scheme morphism over the fixed components: `g : V ⟶ U` and
  `hg : IsComponentLiftMap eU eV g`, which is the pointwise equation
  `eU (ConnectedComponents.mk (g v)) = eV (ConnectedComponents.mk v)`.
  Since the quotient map is surjective this says exactly that the induced map is id_S.
* Actual small sites and coefficients: `Scheme.ProEt.topology T` and
  `condensedRingObj Λ.X T`. On the relative profinite site the expressions are
  `(coherentTopology Profinite.{u}).over S` and `profiniteCoefficient Λ.X S`.
  The topology is finite jointly surjective coverings; it is not an arbitrary topology.
* Internal modules and ordinary unbounded derived categories: `Mod (Sheaf ... Ab.{u+1}) ...`
  and `DerivedCategory`; `Evaluation.D` is the recorded transparent abbreviation.
  Scheme/site object size is u+1 and site morphism size u; abelian coefficients are u+1.
  No equality between object and morphism universes or extra universe restriction is imposed.
* Component tests: `componentLiftTests T S e` transports the recorded `componentTests T`
  by `Over.map e.symm`. The `projection`, `projection_over`, `projection_natural`, and
  `projection_universal` fields of `ComponentLiftCoefficient` specify the genuine
  relative test projections and their unique mapping property. These are conclusion data
  in the outer existential `d`, never extra assumptions of the theorem.
* Canonical inverse image: `inverse_eq` forces `d.inverse` to equal the existing
  sheafified left Kan extension along these tests. `adj_eq` likewise fixes its adjunction
  to the existing construction. The inverse-image field is not an arbitrary map.
  `point`, `point_monoidal`, and `coefficient_eq` require the factorization from the
  condensed point and the exact induced ring-object isomorphism.
* Module and derived component pullbacks: `componentLiftModules` is `mapMod` followed by
  restriction along the inverse of that coefficient isomorphism. `componentLiftDerived`
  is its exact `mapDerivedCategory`. The three named instances supply inherited finite
  limit/colimit preservation and additivity by explicit terms, with no postponed proof.
* Projection-preserving base-change isomorphisms, natural in E: the existential `k`
  is a natural isomorphism from the V tests to the base change of the U tests.
  Its second projection is preserved by being an isomorphism in `V.ProEt`; the displayed
  equation involving `pullback.fst` and `d.projection` preserves the profinite projection.
  These two projections uniquely characterize the isomorphism.
* The comparison is induced by k, rather than an arbitrary natural isomorphism:
  `ComponentLiftInducedComparison dU dV g k q` is the equality after precomposition
  with the component inverse-image unit and the scheme-module adjunction unit, on EVERY
  module and EVERY relative test E. The terminal leg is restriction along `k.hom`.
  Those units characterize the mate uniquely. The theorem then requires
  `c = componentLiftDerivedComparison dU dV g q`. This construction is exactly the
  termwise derived natural iso, composed with the canonical exact/left-derived comparison.
* Monoidality and coefficient units: `m` supplies the component monoidal structures;
  `ComponentLiftMonoidal` is `NatTrans.IsMonoidal c.hom` with these explicit structures
  and the upstream monoidal structure on `moduleObjectDerivedPullback`. This includes
  the tensor equation and the coefficient-unit equation.
* Compatibility with composition of g: the final universally quantified equation uses
  `leftDerivedUpperStarComp Λ.X h g` and states that successive components c_g and c_h
  equal c_(h≫g), at EVERY derived object N. Test naturality in E is already in `k`.
* Finite-rank lisse pullback: for every L satisfying the recorded
  `IsLisseCoefficientModule Λ.X L`, the first clause asserts that the actual
  `(upperStar Λ.X g).obj L` satisfies that same predicate. The predicate has a
  pro-etale covering and a finite free rank on each member; ranks need not be constant.
* Locally finite free module duals: `ComponentLiftLisseFacts Λ T L` quantifies a module
  P, asserts the recorded lisse predicate for P, and supplies `ExactPairing L P`.
  Thus P is an actual module dual, with evaluation and coevaluation and both triangle
  identities, not merely an independently lisse object. This is asserted for U,L and V,g*L.
* K-flatness: the same facts assert `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat`
  for the ordinary single complexes of BOTH L and P. This is the recorded general
  K-flat predicate specialized to quasi-isomorphisms; in an abelian tensor category it
  is equivalently tensoring acyclic complexes to acyclic complexes. The tensor here is
  the upstream total cochain tensor with Koszul signs, not an underived termwise product.
* Ordinary derived dualizability: `ExactPairing (singleFunctor ... L) (singleFunctor ... P)`
  supplies the required evaluation, coevaluation and BOTH identities for ordinary derived
  tensor. No solid/complete tensor is used. `ExactPairing` explicitly stores the two equations.
* Component equivalences on dualizable objects: `ComponentLiftEquivalence` states
  preservation of dualizability, bijectivity on Hom between any two dualizable objects,
  and essential surjectivity on the dualizable objects. These are exactly an equivalence
  of the full subcategories for the fixed `componentLiftDerived`, without choosing a
  second realization functor. This clause is asserted for every T,e over S.
* Identity on Hom from the coefficient unit: `ComponentLiftHomIdentity` quantifies
  every dualizable N, every lisse L, EVERY iso `a : F_U N ≅ L[0]`, and every
  `b : 𝟙_S ⟶ N`. It asserts the equality between the actual derived pullback of
  `ε_U b a` and the V realization of THE SAME b transported by `c_N.inv` and `g*.map a`.
  `leftDerivedUpperStarUnitIso.inv` is precomposed on the actual pullback side, fixing
  the coefficient unit. The derived unit is definitionally the regular module in degree zero.
* Evaluation on 1: `componentLiftHomSection` uses `singleFunctor.preimage` from the
  recorded fully faithful degree-zero embedding, evaluates at the terminal pro-etale
  object, and applies the module map to `sfbSectionOne`. Bijectivity of each of these
  maps is part of the theorem, giving the specified Hom/section identifications.
* Actual section map: `componentLiftSectionPullback` is an explicit abelian-group
  homomorphism, the module adjunction unit evaluated at U followed by terminal
  base-change restriction `overPullbackObjMkIdIso.inv.op`. It is not a chosen bijection.
  `ComponentLiftSectionIdentity` identifies the derived Hom pullback with this exact map,
  under `componentLiftHomSection`, using the upstream degree-zero/derived iso.
* Bijectivity and functoriality: `Function.Bijective (componentLiftSectionPullback Λ g L)`
  is asserted. `ComponentLiftSectionNaturality` is the square for every module morphism;
  `ComponentLiftSectionComposition` is the equation using `upperStarComp` for successive
  pulls. The T clause states the identity law with the canonical `upperStarId`.

Dependency declarations used (the sources and full signatures/docstrings were read):

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`.
* `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite` (used by the recorded component bundling).
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `condensedPullbackHom` and its isomorphism.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj`, `Mod.regular`.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPullback`, with the
  upstream `leftDerivedUpperStarIsoMapDerivedCategory`, `leftDerivedUpperStarComp`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `singleFunctor`.
  `def-weil-size-convention` is a convention and has no declaration; universes are explicit.
* `Sheaf.Paper.ComponentRelativeProfiniteSite`: `affineComponentSpace`,
  `component_relative_profinite_site`; `componentTests` is its universally characterized
  selection in the publicly re-exported `CondensedLisseEvaluationModel`.
* `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
* `Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation`:
  `condensed_wcontractible_lisse_evaluation`, with `Evaluation.D`, `profiniteCoefficient`
  and `componentTests` re-exported from its recorded model module.
* `Sheaf.Paper.CondensedQcqsPushforwardContinuity`: `condensedModuleSections`.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: public re-export of
  `CategoryTheory.MorphismProperty.kFlat`; no ringed-site-only predicate is misapplied
  to internal modules.
* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, specialized
  through the upstream monoidal cochain-complex structure to internal module tensor.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `upperStar`, `upperStarLowerStarAdjunction`, `upperStarComp`; its Coherence companion
  supplies `upperStarId`. The Monoidal/Derived companions supply the exact ordinary
  and derived tensor structures, unit comparison and monoidality used in the signature.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections`:
  `overPullbackObjMkIdIso`.
* `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`: `sfbSectionOne`.
* `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`: the full and faithful
  instances on `singleFunctor` used by `preimage`.
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso`.

The remaining stated proof dependencies are imported without `public`: ringed derived
monoidal comparisons, internal Hom, locally finite free tensor exactness, general site
tensor and descent, and flatness. Their role is the node's unchanged seven-step proof;
this stage does not prove them or replace their canonical constructions.

Edge checks: S empty forces U,V empty; all universal projection formulas remain meaningful,
section groups are zero, and the rank-zero exact pairing has both identity equations on
zero objects. No Nonempty instance is required anywhere. `Mod.IsFree` uses n : Nat, so
zero and varying ranks are included. Identity g is included through the explicit upperStarId
law; arbitrary g over S has no etale/flat/finiteness hypothesis. The comparison quantifies all
unbounded derived objects and all N,a, rather than choosing a single lift of L. Size u is
arbitrary and the small-site object/morphism distinction is retained.

Searches: the sandbox `searches.jsonl` records the actual msearch invocations. Earlier
interrupted work had completed LeanFinder, LeanSearch, Loogle and grep searches. The
LeanFinder query about pullback between weakly contractible affine schemes over the same
component space returned generic sheaf-section bijections, existence-of-morphisms, and
pullback-comparison declarations, not this statement. The LeanSearch query about finite
locally free condensed modules returned ordinary module/sheaf pullbacks and free-module
comparison facts, again no component equivalence with unit normalization. Loogle
`SheafOfModules.unitHomEquiv, SheafOfModules.pullbackObjUnitToUnit` returned zero hits.
Grep `(lisse|[Dd]ualizable).*(component|[Ss]ection)|component.*(lisse|[Dd]ualizable)` and the
later `ComponentLift|componentLift|component_lift_lisse` returned zero Mathlib hits.
The required direct rg searches of both `lean/WeilConjectures` and `lean/Sheaf` for
componentLift, component_lift_lisse and the item id found no declaration. Existing HRS
component equivalence, section evaluation, derived comparison and K-flat APIs were read
and reused. The CompactObject example is now a withdrawn module containing no declarations;
the current neighboring statement modules supply the same module/header/public conventions.

No STATEMENT-DISPUTED flag, missing dependency, new independent notion or node fault remains.
All nontrivial assertions are in the single named item theorem, whose entire proof is sorry.

## Second reading by O4

A second pass by the dispatched worker checked the node against the complete Lean file.
The brief prohibits starting another agent; the maintainer's independent reading follows
delivery. This section does not claim an independent agent reviewed the work.

The pass found and repaired three omissions in the draft: a mere existential comparison
needed normalization as the mate on actual test units; naturality/composition needed actual
equations; and evaluation at one needed a concrete map, its bijectivity, and its commuting
square. The final file contains all three. It also checks that component inverse image and
its adjunction are fixed by equalities to the upstream constructions, that d and m are
conclusion data rather than additional hypotheses, that k is a natural isomorphism of
relative tests preserving both projections, and that c is the localization of the normalized
ordinary module comparison. The public theorem's source/target Hom formula uses the actual
monoidal unit comparisons, and `ComponentLiftSectionIdentity` uses the actual derived
pullback, not an arbitrary inverse equivalence. The K-flat assertions apply to L[0] and its
module dual P[0] on both schemes. Both triangle identities are the fields of ExactPairing.

No statement change, new node, or dependency repair was necessary. The final clause audit
above is against the unchanged node text. The clean scompile runs check both sandbox and
library module names within the prescribed 60-second per-file limit, with explicit universes
and autoImplicit disabled. The delivery dry run will repeat compilation and server preflight.

Further searches: LeanFinder on canonical monoidal derived component pullback and
adjunction-unit section normalization returned eight scheme-normalization/pullback
results, none about this component comparison. Loogle on
`CategoryTheory.Functor.mapDerivedCategoryNatIso, CategoryTheory.ExactPairing`
reported zero hits and explicitly said the first identifier was unknown in its Mathlib
index; that identifier is an upstream WeilConjectures declaration, whose source was
read and reused. This is an index limitation, not evidence the upstream helper is absent.
