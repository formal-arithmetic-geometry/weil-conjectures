/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Algebra.Homology.SuccessiveQuotientFlatTensorSequence
import all Sheaf.Paper.CompletedIntegralFiniteQuotientHomExt
import all Sheaf.Paper.DerivedNakayamaResolution
import all Sheaf.Paper.FiniteCoefficientModelComparison
import all Sheaf.Paper.IntegralCriterionReductions
import all Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.StrictDvrReductionTriangles
import Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation
import Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible

/-! # The successor step for constructible integral reductions

Source: the current blueprint, integral-criterion-reductions proof, second paragraph
(blueprint: lem-pe-successive-reduction-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

open Opposite WeilConjectures
open CategoryTheory.Pretriangulated

attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

private abbrev coefficientRestriction (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  Scheme.proEtaleRingRestrictScalars
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (R := ULift.{u + 1} A) (S := ULift.{u + 1} B)
          f.ulift.{u + 1, u + 1}))

private theorem coefficientRestriction_limits (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    PreservesFiniteLimits (coefficientRestriction X f) :=
  Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits _

private theorem coefficientRestriction_colimits (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    PreservesFiniteColimits (coefficientRestriction X f) :=
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits _

attribute [local instance] coefficientRestriction_limits coefficientRestriction_colimits

private def residueMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l E 1
  | 0 => RingHom.id _
  | n + 1 => (residueMap l E n).comp (Padic.coefficientExtensionTransition l E (n + 1))

private def finiteMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (R := ULift.{u + 1} A) (S := ULift.{u + 1} B)
          f.ulift.{u + 1, u + 1}))

private theorem projection_step (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X (n + 1)) ≫
      finiteMap l E X (Padic.coefficientExtensionTransition l E (n + 1)) =
    (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n) := by
  have h := limit.w (integralCoefficientSheafSystem.{u, u} l E X)
    (homOfLE (Nat.le_succ n)).op
  rw [show (integralCoefficientSheafSystem.{u, u} l E X).map
      (homOfLE (Nat.le_succ n)).op = integralCoefficientSheafTransition.{u, u} l E X n by
    exact Functor.ofOpSequence_map_homOfLE_succ _ n] at h
  exact h

private theorem residue_projection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n) ≫
      finiteMap l E X (residueMap l E n) =
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X 0) := by
  induction n with
  | zero =>
    have hid : finiteMap l E X (residueMap l E 0) = 𝟙 _ := by
      unfold finiteMap
      have h : CommRingCat.ofHom
          (R := ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))
          (S := ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))
          (residueMap l E 0).ulift.{u + 1, u + 1} = 𝟙 _ := by
        ext x
        rfl
      rw [h, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [hid]
    exact Category.comp_id _
  | succ n ih =>
    rw [show finiteMap l E X (residueMap l E (n + 1)) =
      finiteMap l E X (Padic.coefficientExtensionTransition l E (n + 1)) ≫
        finiteMap l E X (residueMap l E n) by
      change finiteMap l E X ((residueMap l E n).comp
        (Padic.coefficientExtensionTransition l E (n + 1))) = _
      unfold finiteMap
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 2]
    rw [← Category.assoc, projection_step l E X n]
    exact ih

private theorem projection_full (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) : (scalarReductionRestriction.{u, u} l E X n).Full := by
  let p := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)
  have hp (U : X.ProEtᵒᵖ) : Function.Surjective (p.hom.app U) := by
    intro b
    obtain ⟨a, ha⟩ := constantQuotient_surjective l E X n U b
    refine ⟨(integralConstantToCompletionOfUniverses l E X).hom.app U a, ?_⟩
    exact (congrArg (fun f ↦ f.hom.app U a)
      (limit.lift_π (integralConstantConeOfUniverses l E X) (op n))).trans ha
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) p.hom :=
    Presheaf.isLocallySurjective_of_surjective _ _ hp
  exact SheafOfModules.restriction_full p

private theorem ordinaryBC_iso (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : Scheme.proEtaleDerivedCategory X A} (e : K ≅ L)
    (hK : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X K) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X L := by
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun q ↦ FiniteDiscreteOrdinary.constructible_of_iso A X
      ((DerivedCategory.homologyFunctor _ q).mapIso e) (hK.2 q)⟩

private theorem ordinaryBC_extension (X : Scheme.{u}) [IsNoetherian X] (A : Type u)
    [CommRing A] [Finite A] (T : Triangle (Scheme.proEtaleDerivedCategory X A))
    (hT : T ∈ distTriang _)
    (h1 : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X T.obj₁)
    (h3 : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X T.obj₃) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X T.obj₂ := by
  let Q : ObjectProperty (Scheme.proEtaleDerivedCategory X A) := fun K ↦
    Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj K)} ∧
      ∀ q : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor _ q).obj K)
  have : Q.IsClosedUnderIsomorphisms :=
    (Scheme.proEtale_bounded_constructible_isTriangulated X A).1
  have : Q.IsTriangulated :=
    (Scheme.proEtale_bounded_constructible_isTriangulated X A).2
  have h := Q.ext_of_isTriangulatedClosed₂ T hT
    ⟨(Scheme.finite_homology_support_iff_bounded X A _).mpr h1.1, h1.2⟩
    ⟨(Scheme.finite_homology_support_iff_bounded X A _).mpr h3.1, h3.2⟩
  exact ⟨(Scheme.finite_homology_support_iff_bounded X A _).mp h.1, h.2⟩

private theorem finiteRestriction_BC (X : Scheme.{u}) [IsNoetherian X]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (K : Scheme.proEtaleDerivedCategory X B)
    (hK : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible B X K) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X
      ((coefficientRestriction X f).mapDerivedCategory.obj K) := by
  exact (Scheme.proEtaleFiniteScalarRestriction_constructible X A B f).2.2.2.2.2 K hK.1 hK.2

private theorem finiteRestriction_zero (X : Scheme.{u}) [IsNoetherian X]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (K : Scheme.proEtaleDerivedCategory X B) (q : ℤ)
    (hK : IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((coefficientRestriction X f).mapDerivedCategory.obj K)) := by
  exact ((Scheme.proEtaleFiniteScalarRestriction_constructible X A B f).2.2.2.2.1 K q).mpr hK

private theorem triangle_zero_middle {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (q : ℤ) (h1 : IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₁))
    (h3 : IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₃)) :
    IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₂) := by
  exact (DerivedCategory.HomologySequence.exact₂ T hT q).isZero_X₂
    (h1.eq_of_src _ _) (h3.eq_of_tgt _ _)

private theorem finite_quotient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)

attribute [local instance] finite_quotient

private theorem ordinary_successor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) (a b : ℤ)
    (hfirst : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible
      (Padic.coefficientExtensionRing l E 1) X
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K))
    (hprev : FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible
      (Padic.coefficientExtensionRing l E (n + 1)) X
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))
    (hfirstBounds : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)))
    (hprevBounds : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible
      (Padic.coefficientExtensionRing l E (n + 2)) X
        ((scalarReductionDerivedExtension.{u, u} l E X (n + 1)).obj K) ∧
      ∀ q : ℤ, q < a ∨ b < q → IsZero
        ((DerivedCategory.homologyFunctor _ q).obj
          ((scalarReductionDerivedExtension.{u, u} l E X (n + 1)).obj K)) := by
  let : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : Finite (Padic.coefficientExtensionRing l E (n + 2)) :=
    Padic.finite_coefficientExtensionRing l E (n + 2) (by omega)
  obtain ⟨P, e, hP, _, u, _, i, _, hseq⟩ := strictDvrReductionTriangles.{u, u} l E X K
  let R := scalarReductionRestriction.{u, u} l E X (n + 1)
  let Rprev := coefficientRestriction X (Padic.coefficientExtensionTransition l E (n + 1))
  let Rfirst := coefficientRestriction X (residueMap l E (n + 1))
  have : PreservesFiniteLimits R := scalarReductionRestrictionLimits.{u, u} l E X (n + 1)
  have : PreservesFiniteColimits R := scalarReductionRestrictionColimits.{u, u} l E X (n + 1)
  have : R.Full := projection_full l E X (n + 1)
  have : R.Faithful := SheafOfModules.restriction_faithful _
  have cprev : Rprev ⋙ R ≅ scalarReductionRestriction.{u, u} l E X n := by
    apply SheafOfModules.restrictionComp
    exact projection_step l E X n
  have cfirst : Rfirst ⋙ R ≅ scalarReductionRestriction.{u, u} l E X 0 :=
    SheafOfModules.restrictionComp _ _ _ (residue_projection l E X (n + 1))
  let Q (j : ℕ) := unrestrictedTowerFiniteComplex.{u, u} l E X j P
  let Qfirst := (Rfirst.mapHomologicalComplex (.up ℤ)).obj (Q 0)
  let Qprev := (Rprev.mapHomologicalComplex (.up ℤ)).obj (Q n)
  let V := R.mapHomologicalComplex (.up ℤ)
  let ef : V.obj Qfirst ≅ unrestrictedTowerComplex.{u, u} l E X 0 P :=
    (NatIso.mapHomologicalComplex cfirst (.up ℤ)).app (Q 0)
  let ep : V.obj Qprev ≅ unrestrictedTowerComplex.{u, u} l E X n P :=
    (NatIso.mapHomologicalComplex cprev (.up ℤ)).app (Q n)
  obtain ⟨hz, hs, _⟩ := hseq n
  let S := ShortComplex.mk (i n) (unrestrictedTowerTransition.{u, u} l E X P n) hz
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact _ hs
  let α : V.obj Qfirst ⟶ V.obj (Q (n + 1)) := ef.hom ≫ S.f
  let β : V.obj (Q (n + 1)) ⟶ V.obj Qprev := S.g ≫ ep.inv
  have hab : α ≫ β = 0 := by simp [α, β, Category.assoc]
  have hSES : (ShortComplex.mk α β hab).ShortExact := by
    let eS : S ≅ ShortComplex.mk α β hab :=
      ShortComplex.isoMk ef.symm (Iso.refl (V.obj (Q (n + 1)))) ep.symm
        (by exact (ef.inv_hom_id_assoc S.f).trans (Category.comp_id S.f).symm)
        (by exact Category.id_comp _)
    exact ShortComplex.shortExact_of_iso eS hS
  have vadd : V.Additive := inferInstance
  have vfull : V.Full := inferInstance
  have vfaithful : V.Faithful := inferInstance
  have : HasFiniteLimits (scalarReductionTarget.{u, u} l E X (n + 1)) :=
    Abelian.hasFiniteLimits
  have : HasFiniteColimits (scalarReductionTarget.{u, u} l E X (n + 1)) :=
    Abelian.hasFiniteColimits
  have vlimits : PreservesFiniteLimits V := inferInstance
  have vcolimits : PreservesFiniteColimits V := inferInstance
  obtain ⟨α', β', hz', hs', _, _⟩ := SheafOfModules.lift_shortExact
    (A := CochainComplex (scalarReductionTarget.{u, u} l E X (n + 1)) ℤ)
    (D := CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) V
    (X₁ := Qfirst) (X₂ := Q (n + 1)) (X₃ := Qprev) α β hab hSES
  let T : Triangle (Scheme.proEtaleDerivedCategory X
      (Padic.coefficientExtensionRing l E (n + 2))) := DerivedCategory.triangleOfSES hs'
  have hT := DerivedCategory.triangleOfSES_distinguished hs'
  let comp (j : ℕ) : DerivedCategory.Q.obj (Q j) ≅
      (scalarReductionDerivedExtension.{u, u} l E X j).obj K :=
    (unrestrictedTowerResolutionIso.{u, u} l E X j (𝟙 P) ⟨inferInstance, hP⟩).symm ≪≫
      (scalarReductionDerivedExtension.{u, u} l E X j).mapIso e
  let efirst : T.obj₁ ≅ Rfirst.mapDerivedCategory.obj
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) :=
    (Rfirst.mapDerivedCategoryFactors.app (Q 0)).symm ≪≫
      Rfirst.mapDerivedCategory.mapIso (comp 0)
  let eprev : T.obj₃ ≅ Rprev.mapDerivedCategory.obj
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) :=
    (Rprev.mapDerivedCategoryFactors.app (Q n)).symm ≪≫
      Rprev.mapDerivedCategory.mapIso (comp n)
  have hf := ordinaryBC_iso X _ efirst.symm
    (finiteRestriction_BC X (residueMap l E (n + 1)) _ hfirst)
  have hp := ordinaryBC_iso X _ eprev.symm
    (finiteRestriction_BC X (Padic.coefficientExtensionTransition l E (n + 1)) _ hprev)
  refine ⟨ordinaryBC_iso X _ (comp (n + 1)) (ordinaryBC_extension X _ T hT hf hp), ?_⟩
  intro q hq
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ q).mapIso (comp (n + 1))).symm
  exact triangle_zero_middle T hT q
    ((finiteRestriction_zero X (residueMap l E (n + 1)) _ q (hfirstBounds q hq)).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso efirst))
    ((finiteRestriction_zero X (Padic.coefficientExtensionTransition l E (n + 1)) _ q
      (hprevBounds q hq)).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso eprev))

/-- A single successor reduction is constructible and stays in the same interval.
Completeness of the original complex is unnecessary.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/sk-prop-integral-criterion-reductions.proof.md,
second paragraph (blueprint: lem-pe-successive-reduction-constructibility).

Proof: use a simultaneous flat-term K-flat representative and the residue-kernel sequence
0 -> O/pi -> O/pi^(n+2) -> O/pi^(n+1) -> 0. The first map multiplies by pi^(n+1).
The completed projection is surjective on sections, so its fully faithful restriction
lifts this sequence to complexes over O/pi^(n+2), retaining both outer quotient actions.
The finite coefficient model comparison identifies the continuous constant-model
constructibility predicates with the ordinary finite-stalk predicates. Restriction
of scalars along maps of these finite quotient rings preserves constructibility and
reflects zero cohomology. Thus the two outer objects over O/pi^(n+2) are bounded
constructible. Extension closure in the distinguished triangle gives the same for
the middle object. Outside [a,b], both outer cohomology objects vanish, and exactness
of the cohomology sequence forces the middle one to vanish. Transport back by the
finite coefficient equivalence, which preserves each vanishing degree. The argument
includes n=0, the zero complex, and the empty scheme; it uses no Tor bound on K. -/
theorem successiveReduction_constructible_interval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (n : ℕ) (a b : ℤ)
    (hfirst : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K))
    (hprev : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
      ((AdicCompletion.derivedReduction l E X n).obj K))
    (hfirstBounds : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X 0).obj K)))
    (hprevBounds : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K))) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1 + 1)) X
        ((AdicCompletion.derivedReduction l E X (n + 1)).obj K) ∧
      ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X (n + 1)).obj K)) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : ∀ j : ℕ, DiscreteTopology (Padic.coefficientExtensionRing l E (j + 1)) :=
    fun j ↦ DerivedNakayama.quotientDiscrete l E (j + 1)
  obtain ⟨A, es, squares, _, bs, _, _, _⟩ :=
    IntegralPresentation.integral_completion_reduction_comparisons l E X
  let L := A.derived.functor.obj K
  let c (j : ℕ) : (scalarReductionDerivedExtension.{u, u} l E X j).obj L ≅
      (es j).ordinaryDerived.functor.obj ((AdicCompletion.derivedReduction l E X j).obj K) :=
    (bs j).app K
  have hf := ordinaryBC_iso X _ (c 0).symm
    ((finiteEncoding_constructible _ X (es 0) _).mp hfirst)
  have hp := ordinaryBC_iso X _ (c n).symm
    ((finiteEncoding_constructible _ X (es n) _).mp hprev)
  have hfb : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L)) := by
    have h := (FiniteDiscreteOrdinary.derived_intervals _ X (es 0) _ a b).mp hfirstBounds
    intro q hq
    exact (h q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso (c 0))
  have hpb : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj L)) := by
    have h := (FiniteDiscreteOrdinary.derived_intervals _ X (es n) _ a b).mp hprevBounds
    intro q hq
    exact (h q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso (c n))
  obtain ⟨hc, hb⟩ := ordinary_successor l E X L n a b hf hp hfb hpb
  refine ⟨(finiteEncoding_constructible _ X (es (n + 1)) _).mpr
    (ordinaryBC_iso X _ (c (n + 1)) hc), ?_⟩
  apply (FiniteDiscreteOrdinary.derived_intervals _ X (es (n + 1)) _ a b).mpr
  intro q hq
  exact (hb q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso (c (n + 1))).symm

end AlgebraicGeometry.ProEtale
