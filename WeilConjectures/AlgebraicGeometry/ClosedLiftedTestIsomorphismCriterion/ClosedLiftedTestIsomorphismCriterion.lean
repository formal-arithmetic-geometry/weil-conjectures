/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeModel
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWContractibleSectionsExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWContractibleSectionsDerived
import WeilConjectures.RingTheory.ProEtale.HenselianClosedLift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedHenselianLisseRigidity
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedSliceLocalization
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Closed lifted tests detect the specified derived exchange

Source: Stacks Project, Tags 09BK, 09BL, 098F and 098H; Hemo--Richarz--Scholbach,
Corollary 4.4 and Lemma 4.1; Bhatt--Scholze, Lemmas 6.1.1--6.1.2
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

The canonical maps are those of `ClosedTestDerivedExchangeModel`. All derived direct
images are ordinary unbounded K-injective derived functors. No integrality, lisseness,
flatness of coefficient extension, or invertibility of its direct comparison is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedLiftedTestIsomorphismCriterion

open ClosedTestDerivedExchangeModel

/-- The specified lifted w-contractible tests cover the affine ind-etale basis.
Source: Stacks 09BK and 098F; HRS Corollary 4.4(2)
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: Take an ind-etale faithfully flat w-contractible cover of the coordinate ring
[sk-thm-pe-wc-cover]. Composition remains ind-etale [lem-weil-pbc-ind-etale-stability].
The closed lift is henselian [lem-zl-henselian-indetale-closed-lift] and its quotient is
the original ring [lem-exc-closed-lift-reduction]. HRS Corollary 4.4(2), the geometric
clause of lem-zl-condensed-henselian-lisse-rigidity, makes the lift w-contractible too.
The cover thus belongs to the stated test family. -/
theorem closed_lifted_tests_cover (A : Type u) [CommRing A] (I : Ideal A)
    (V₀ : (Spec (.of (A ⧸ I))).AffineProEt) :
    ∃ R : Presieve V₀,
      Sieve.generate R ∈ Scheme.AffineProEt.topology (Spec (.of (A ⧸ I))) V₀ ∧
        ∀ (V : (Spec (.of (A ⧸ I))).AffineProEt) (r : V ⟶ V₀), R r →
          IsWContractibleRing Γ(V.left, ⊤) ∧
            IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤) := by
  sorry

/-- The specified closed fibre is the quotient by the extended ideal and is henselian.
Source: Stacks 09BK and 097P; Bhatt--Scholze, proof of Lemma 6.1.2
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: lem-weil-pbc-affine-closed-site-functor-properties gives the pullback for the
specified inclusion. lem-exc-closed-lift-reduction identifies its actual coordinate map
with reduction modulo the extended ideal. Transport lem-zl-henselian-indetale-closed-lift
along the canonical global-section isomorphism of Spec of the closed-lift algebra.
These arguments apply to every affine test, and hence to every w-contractible test. -/
theorem closed_lifted_test_geometry (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    IsPullback (Scheme.AffineProEt.closedSiteLiftInclusion A I V) V.hom
        ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom (closedMap A I) ∧
      HenselianRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)
        (I.map (((Scheme.ΓSpecIso (.of A)).inv ≫
          ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom.appTop).hom)) ∧
      ∃ e :
          Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤) ⧸
              I.map (((Scheme.ΓSpecIso (.of A)).inv ≫
                ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom.appTop).hom) ≃+*
            Γ(V.left, ⊤),
        ∀ c : Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤),
          e (Ideal.Quotient.mk _ c) =
            (Scheme.AffineProEt.closedSiteLiftInclusion A I V).appTop.hom c := by
  sorry

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Evaluation of internal modules at every lifted test is exact.
Source: Stacks 098H; HRS Lemma 4.1(1)
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: Use def-weil-pbc-internal-abelian-sheaf-module-equivalence, which preserves the
underlying abelian sheaf and its sections. det-pe-wc-sections-exact says evaluation at
this w-contractible affine preserves kernels and cokernels. Forgetting the module
structure preserves these operations, giving both finite-limit and finite-colimit
preservation for the displayed underlying-section evaluation. -/
theorem closed_lifted_test_evaluation_exact (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    PreservesFiniteLimits
        (Mod.forget (condensedRingObj Λ (Spec (.of (A ⧸ I)))) ⋙
          (sheafSections (Scheme.ProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1}).obj
            (op ((Scheme.AffineProEt.toProEt _).obj V))) ∧
      PreservesFiniteColimits
        (Mod.forget (condensedRingObj Λ (Spec (.of (A ⧸ I)))) ⋙
          (sheafSections (Scheme.ProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1}).obj
            (op ((Scheme.AffineProEt.toProEt _).obj V))) := by
  sorry

/-- Derived sections over the lifted tests jointly detect isomorphisms on the entire
unbounded derived category.
Source: Stacks 098H and the cone/sheaf-axiom argument; HRS Lemma 4.1(1)
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: det-pe-wc-sections-derived identifies derived sections with termwise sections.
By exact evaluation their cohomology is the sections of the cohomology sheaves. If
all test sections vanish, closed_lifted_tests_cover and the ind-etale basis comparison
make every section locally zero; sheaf separatedness makes it zero. Thus every
cohomology sheaf vanishes. For a map apply this to its cone; exact evaluation descends
to a triangulated derived functor [lem-weil-pbc-exact-functor-derived-factorization].
The cone is zero, and lem-kun-distinguished-cone-zero makes the map invertible. -/
theorem closed_lifted_tests_detect_isomorphisms (A : Type u) [CommRing A] (I : Ideal A)
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of (A ⧸ I)))))} (b : K ⟶ L)
    (hb : ∀ (V : (Spec (.of (A ⧸ I))).AffineProEt),
      IsWContractibleRing Γ(V.left, ⊤) →
      IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤) →
        IsIso ((sectionsOver Λ V.hom).map b)) :
    IsIso b := by
  sorry

/-- Invertibility of all specified unit-induced restrictions implies invertibility of
the specified counit-adjunct exchange.
Source: Stacks 09BL and the existing closed-test derived exchange model
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: Apply lem-sfb-closed-test-derived-exchange-model to each test. Its normalized
left and right comparison isomorphisms identify the evaluated canonical exchange
with testRestriction, the derived unit for the actual closed test-fibre inclusion,
followed by canonical composition. The hypothesis makes each evaluated exchange
invertible. closed_lifted_tests_detect_isomorphisms now makes the exchange invertible.
The only geometric hypothesis is affineness; the only cohomological bound is K in D+. -/
theorem closed_lifted_test_isomorphism_criterion
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (closedMap A I))
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : ∀ (V : (Spec (.of (A ⧸ I))).AffineProEt),
      IsWContractibleRing Γ(V.left, ⊤) →
      IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤) →
        IsIso ((testRestriction Λ A I w.toCommSq V).app K.obj)) :
    IsIso ((exchange Λ w.toCommSq).app K.obj) := by
  sorry

/-- Naturality in the bounded-below complex of the specified exchange.
Source: Stacks 07A7, adjunct formula
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: The transpose is h* of the counit after the canonical pullback comparison.
Naturality of that comparison and of the counit gives the equality of transposes.
Injectivity of the fZ adjunction bijection gives the displayed equality. -/
theorem closed_exchange_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : IsPullback h fZ f (closedMap A I))
    (K L : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (t : K.obj ⟶ L.obj) :
    (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A I)).map t ≫
        (exchange Λ w.toCommSq).app L.obj =
      (exchange Λ w.toCommSq).app K.obj ≫
        (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ).map t := by
  sorry

/-- The exchange commutes with pro-etale localization cubes and hence with isomorphisms
of the cartesian square. This formulation permits arbitrary localized bases, including
entire U[Q] and further parametrizations; it makes no choice of a point of Q.
Source: Stacks 07A7 and 0D6F
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: The two transposes are h* of the original counit transported through the same
pullback composition. lem-weil-pbc-ringed-derived-slice-localization preserves units
and counits. lem-sfb-derived-composition-adjunction-normalization identifies composite
adjunction constraints with the specified constraints, so both transposes coincide.
An isomorphism is pro-etale; transporting its counit gives the square-isomorphism case.
For v = U[Q] → U [def-sfb-profinite-test-objects] apply this to the whole object.
Apply it again for any further parameter object. The same composition normalization
identifies the iterated equations. -/
theorem closed_exchange_base_change_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ X' U' Z' XZ' : Scheme.{u}} [IsAffine X]
    {f : X ⟶ Spec (.of A)} {h : XZ ⟶ X}
    {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    {f' : X' ⟶ U'} {s' : Z' ⟶ U'} {h' : XZ' ⟶ X'} {fZ' : XZ' ⟶ Z'}
    (a : X' ⟶ X) (v : U' ⟶ Spec (.of A)) (t : XZ' ⟶ XZ)
    (k : Z' ⟶ Spec (.of (A ⧸ I))) [WeaklyEtale v]
    (w : IsPullback h fZ f (closedMap A I)) (w' : IsPullback h' fZ' f' s')
    (wf : IsPullback a f' f v) (ws : IsPullback k s' (closedMap A I) v)
    (wh : IsPullback t h' h a) (wZ : IsPullback t fZ' fZ k)
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (pull Λ k).map ((exchange Λ w.toCommSq).app K.obj) ≫
        (exchange Λ wZ.toCommSq).app ((pull Λ h).obj K.obj) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ').map
          ((square Λ wh.toCommSq).inv.app K.obj) =
      (square Λ ws.toCommSq).inv.app
          ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj) ≫
        (pull Λ s').map ((exchange Λ wf.toCommSq).app K.obj) ≫
        (exchange Λ w'.toCommSq).app ((pull Λ a).obj K.obj) := by
  sorry

section Coefficients

variable {Λ} {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (c : Λ ⟶ Λ') [IsMonHom c]

/-- The derived map induced by an actual degree-zero module map after scalar restriction.
Source: coefficient paragraph, Stacks 07A7
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion). -/
def degreeZeroCoefficientMap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (t : M ⟶ (Mod.comap (coefficientMap c X)).obj N) :
    (DerivedCategory.singleFunctor _ 0).obj M ⟶
      (restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj N) :=
  (DerivedCategory.singleFunctor _ 0).map t ≫
    ((Mod.comap (coefficientMap c X)).mapDerivedCategorySingleFunctor 0).inv.app N

/-- Scalar compatibility for actual degree-zero module maps, with the canonical
right-derived direct-image comparison in its natural, possibly noninvertible direction.
Source: Stacks 07A7, the ordinary scalar identity and adjunction transposes
(blueprint: lem-sfb-closed-lifted-test-isomorphism-criterion).

Proof: (1) Restriction is exact and the ordinary pushforward commutes with it on
sections [sk-def-sfb-change-of-scalars]. Its ordinary mate is that section identity.
(2) The universal right-derived comparison of this identity is restrictPush; it is
uniquely determined on K-injective models [def-sfb-right-derived-functor].
(3) The module categories are Grothendieck by the internal/section-module equivalence
and lem-weil-pbc-ring-sheaves-grothendieck; use functorial K-injectives from
lem-weil-pbc-kinjective-functorial-existence. Apply lem-pur-exact-derived-mate to exact
inverse images and scalar restrictions. Its normalization identifies the mate of the
pullback coefficient comparison with restrictPush. No preservation of K-injectives
by scalar restriction is required. Its counit equation holds on unbounded objects.
(4) Transpose the coefficient-exchange square under the fZ adjunction. On the left
substitute that counit equation for fZ, and on the right for f. Naturality of pullback
composition makes the transposes equal, proving the first displayed equation.
(5) Naturality of the exchange at the actual degree-zero map t proves the second
one. For N = ordinary extension of M and t the extension unit, this is precisely
x ↦ 1 tensor x: degreeZeroCoefficientMap is then the existing scalarUnit.
(6) All equalities restrict to the whole U[Q] and to further parametrizations by the
previous localization equation and its unit/counit composition normalization. -/
theorem closed_exchange_coefficient_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : IsPullback h fZ f (closedMap A I))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (t : M ⟶ (Mod.comap (coefficientMap c X)).obj N) :
    (CondensedRing.derivedComapUpperStarIso c (closedMap A I)).hom.app
          ((CondensedRing.moduleObjectDerivedPushforward Λ' f).obj
            ((DerivedCategory.singleFunctor _ 0).obj N)) ≫
        (pull Λ (closedMap A I)).map
          ((restrictPush c f).app ((DerivedCategory.singleFunctor _ 0).obj N)) ≫
        (exchange Λ w.toCommSq).app
          ((restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj N)) =
      (restrict c (Spec (.of (A ⧸ I)))).map
          ((exchange Λ' w.toCommSq).app ((DerivedCategory.singleFunctor _ 0).obj N)) ≫
        (restrictPush c fZ).app
          ((pull Λ' h).obj ((DerivedCategory.singleFunctor _ 0).obj N)) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
          ((CondensedRing.derivedComapUpperStarIso c h).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj N)) ∧
      (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A I)).map
          (degreeZeroCoefficientMap c X M N t) ≫
          (exchange Λ w.toCommSq).app
            ((restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj N)) =
        (exchange Λ w.toCommSq).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
            (degreeZeroCoefficientMap c X M N t) := by
  sorry

end Coefficients

end AlgebraicGeometry.ProEtale.ClosedLiftedTestIsomorphismCriterion
