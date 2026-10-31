/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension

import WeilConjectures.DeligneLaumon.GeometricProjectiveOpenProperties
import WeilConjectures.DeligneLaumon.CondensedScalarActionFaithful
import WeilConjectures.DeligneLaumon.CondensedLisseReductionFaithful
import WeilConjectures.DeligneLaumon.CondensedScalarCokernelPullback
import WeilConjectures.DeligneLaumon.FiniteCoverOfAbelianPullback
import WeilConjectures.DeligneLaumon.CondensedFiniteCoverKernel
import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic

/-! # Extension implies trivial action on the normalized boundary kernel -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

private theorem free_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) (e : M ≅ N) : Mod.IsFree R N := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ i⟩⟩

private theorem free_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (h : Mod.IsFree T M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫ ?_⟩⟩
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular T) ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

private theorem free_of_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree T M := by
  exact free_of_iso (free_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

private theorem lisse_iff_locallyFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLisseCoefficientModule Λ M ↔ CondensedRing.LocallyFree (condensedRingObj Λ X) M := by
  constructor
  · rintro ⟨V, hV⟩
    refine ⟨V, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (V.f i)
    apply free_of_comap (inv φ)
    exact free_of_iso (hV i) ((Mod.extendScalarsIsoComapInv φ).app _)
  · rintro ⟨V, hV⟩
    refine ⟨V, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (V.f i)
    exact free_of_iso (free_comap (inv φ) (hV i))
      ((Mod.extendScalarsIsoComapInv φ).app _).symm

private theorem rep_action_eq_one_of_iso
    {A : Type*} [CommRing A] {G : Type*} [Group G] {V W : Rep.{u + 1} A G}
    (e : V ≅ W) (g : G) (h : V.ρ g = 1) : W.ρ g = 1 := by
  ext w
  change W.ρ g w = w
  obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 w
  rw [← Rep.hom_comm_apply, h]
  rfl

private theorem isIso_adjunction_identity
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) :
    IsIso ((adj.homEquiv X (F.obj X)).symm
      ((adj.homEquiv X (F.obj X)) (𝟙 (F.obj X)))) := by
  rw [Equiv.symm_apply_apply]
  infer_instance

private theorem functor_action_eq_one_of_iso
    {A : Type*} [CommRing A] {G : Type*} [Group G]
    {C : Type*} [Category C] (P : ObjectProperty C)
    (F : P.FullSubcategory ⥤ Rep.{u + 1} A G)
    (X Y : P.FullSubcategory) (e : X.obj ≅ Y.obj)
    (g : G) (h : (F.obj X).ρ g = 1) : (F.obj Y).ρ g = 1 := by
  let eFull : X ≅ Y := ObjectProperty.isoMk P (X := X) (Y := Y) e
  let eRep : F.obj X ≅ F.obj Y := F.mapIso eFull
  exact rep_action_eq_one_of_iso (V := F.obj X) (W := F.obj Y) eRep g h


set_option maxHeartbeats 0 in
-- Keep finite-cover transport independent of the uniformizer quotient presentation.
private theorem finite_action_eq_one_of_abelian_pullback
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (d : Scheme.GaloisLisseFiniteCorrespondence b G)
    (H : ProfiniteGrp.{u}) [∀ P, MulAction H ((fiber (b ≫ j)).obj P)]
    (dC : Scheme.GaloisLisseFiniteCorrespondence (b ≫ j) H)
    (A : Type (u + 1)) [Ring A] [Finite A]
    (FC : Scheme.LisseModuleSheafCategory C A)
    (FU : Scheme.LisseModuleSheafCategory U A)
    (e : LisseQlbar.underlyingAb A FU.obj ≅
      (Etale.upperStar Ab.{u + 1} j).obj (LisseQlbar.underlyingAb A FC.obj))
    (g : G) (hg : pullbackPathHom j b (eG g) = 1) :
    (((d.e A).functor.obj FU).obj.ρ g) = 1 := by
  have hFC : Scheme.IsLisseEtaleSheafOfSets
      (Scheme.galoisUnderlyingSetSheaf A FC.obj) :=
    (dC.finiteEvaluationAction A FC).1
  obtain ⟨P, ⟨eP⟩⟩ := finite_cover_of_abelian_pullback j b G d A FC.obj FU.obj hFC e
  exact finite_action_eq_one_of_pullback_cover j b G eG haction d A FU P eP g hg

set_option maxHeartbeats 0 in
-- The finite-reduction records carry canonical coefficient and fibre comparisons.
private theorem pullback_integral_action_eq_one
    (l : ℕ) [Fact l.Prime] {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G)
    (H : ProfiniteGrp.{u}) [∀ P, MulAction H ((fiber (b ≫ j)).obj P)]
    (S : LisseQlbar.Correspondence l (b ≫ j) H)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (N : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (LisseQlbar.integerRing l E) C))
    (hN : CondensedRing.LocallyFree (condensedRingObj (LisseQlbar.integerRing l E) C) N)
    (g : G) (hg : pullbackPathHom j b (eG g) = 1) :
    ((R.integral E).functor.obj
      ⟨(CondensedRing.upperStar (LisseQlbar.integerRing l E) j).obj N,
        CondensedRing.locallyFree_upperStar _ j hN⟩).ρ g = 1 := by
  classical
  let nU : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
      (condensedRingObj (LisseQlbar.integerRing l E) U)) :=
    ⟨(CondensedRing.upperStar (LisseQlbar.integerRing l E) j).obj N,
      CondensedRing.locallyFree_upperStar _ j hN⟩
  obtain ⟨r, hr⟩ := R.reductions E nU
  let nC : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
      (condensedRingObj (LisseQlbar.integerRing l E) C)) := ⟨N, hN⟩
  obtain ⟨s, _⟩ := S.reductions E nC
  apply LisseQlbar.integral_action_eq_one_of_reductions l b G R E nU r hr g
  intro n
  let := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let FC : Sheaf C.smallEtaleTopology Ab.{u + 1} :=
    LisseQlbar.underlyingAb A (s n).etale.obj
  let FU : Sheaf U.smallEtaleTopology Ab.{u + 1} :=
    LisseQlbar.underlyingAb A (r n).etale.obj
  let qC : N.X ⟶ (comparisonUpperStar Ab.{u + 1} C).obj FC := (s n).quotient
  let qU : ((CondensedRing.upperStar (LisseQlbar.integerRing l E) j).obj N).X ⟶
      (comparisonUpperStar Ab.{u + 1} U).obj FU := (r n).quotient
  let a := LisseQlbar.integerScalar l E
    ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1))
  have zC : LisseQlbar.scalarEnd (LisseQlbar.integerRing l E) C a N ≫ qC = 0 :=
    (s n).zero
  have zU : LisseQlbar.scalarEnd (LisseQlbar.integerRing l E) U a
      ((CondensedRing.upperStar (LisseQlbar.integerRing l E) j).obj N) ≫ qU = 0 :=
    (r n).zero
  have cC : IsColimit (CokernelCofork.ofπ qC zC) := (s n).cokernel
  have cU : IsColimit (CokernelCofork.ofπ qU zU) := (r n).cokernel
  have hc : Nonempty (FU ≅ (Etale.upperStar Ab.{u + 1} j).obj FC) :=
    LisseQlbar.scalar_cokernel_pullback_iso (LisseQlbar.integerRing l E) j a N
      FC FU qC qU zC zU cC cU
  obtain ⟨ec⟩ := hc
  exact finite_action_eq_one_of_abelian_pullback j b G eG _haction R.finite H S.finite A
    (s n).etale (r n).etale ec g hg

set_option maxHeartbeats 1000000 in
-- Scalar models are checked with their lattice and comparison isomorphism abstract.
private theorem pulled_lattice_kernel
    (l : ℕ) [Fact l.Prime] {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G)
    (H : ProfiniteGrp.{u}) [∀ P, MulAction H ((fiber (b ≫ j)).obj P)]
    (S : LisseQlbar.Correspondence l (b ≫ j) H)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (N : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (LisseQlbar.integerRing l E) C))
    (hN : CondensedRing.LocallyFree (condensedRingObj (LisseQlbar.integerRing l E) C) N)
    (Q : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (LisseQlbar.fieldRing l E) C))
    (eN : (Mod.extendScalars
      (coefficientMap (LisseQlbar.integerInclusion l E) C)).obj N ≅ Q)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (eM : (Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) U)).obj
        ((CondensedRing.upperStar (LisseQlbar.fieldRing l E) j).obj Q) ≅ M) :
    ∃ h : LisseQlbar.integralClosure l U M,
      ∀ g : G, (pullbackPathHom j b) (eG g) = 1 →
        (R.algebraic.functor.obj ⟨M, h⟩).ρ g = 1 := by
  classical
  let NU := (CondensedRing.upperStar (LisseQlbar.integerRing l E) j).obj N
  let nU : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
      (condensedRingObj (LisseQlbar.integerRing l E) U)) :=
    ⟨NU, CondensedRing.locallyFree_upperStar _ j hN⟩
  let qU : (LisseQlbar.integralField l E U).FullSubcategory :=
    ⟨(Mod.extendScalars (coefficientMap (LisseQlbar.integerInclusion l E) U)).obj NU,
      (R.localization E).closed nU⟩
  let aU : (LisseQlbar.integralClosure l U).FullSubcategory :=
    ⟨(Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) U)).obj qU.obj,
      (R.algebraicExtension E).closed qU⟩
  let eQu : qU.obj ≅ (CondensedRing.upperStar (LisseQlbar.fieldRing l E) j).obj Q :=
    (CondensedRing.pullIso (LisseQlbar.integerInclusion l E) j).app N ≪≫
      (CondensedRing.upperStar (LisseQlbar.fieldRing l E) j).mapIso eN
  let ep : aU.obj ≅ M :=
    (Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) U)).mapIso eQu ≪≫
    eM
  let h : LisseQlbar.integralClosure l U M :=
    ⟨CondensedRing.locallyFree_of_iso ep aU.property.1, E, qU.obj, qU.property, ⟨ep⟩⟩
  refine ⟨h, fun g hg ↦ ?_⟩
  have hNU : ((R.integral E).functor.obj nU).ρ g = 1 :=
    pullback_integral_action_eq_one l j b G eG _haction R H S E N hN g hg
  have hqU : ((R.rational E).functor.obj qU).ρ g = 1 := by
    let adj := Mod.extendRestrictAdjunction
      (coefficientMap (LisseQlbar.integerInclusion l E) U)
    let iq := (adj.homEquiv nU.obj qU.obj) (𝟙 _)
    have hiq : IsIso ((adj.homEquiv nU.obj qU.obj).symm iq) :=
      isIso_adjunction_identity adj nU.obj
    exact (R.localization E).action_eq_one nU qU iq hiq g hNU
  have haU : (R.algebraic.functor.obj aU).ρ g = 1 := by
    let adj := Mod.extendRestrictAdjunction
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) U)
    let ia := (adj.homEquiv qU.obj aU.obj) (𝟙 _)
    have hia : IsIso ((adj.homEquiv qU.obj aU.obj).symm ia) :=
      isIso_adjunction_identity adj qU.obj
    exact (R.algebraicExtension E).action_eq_one qU aU ia hia g hqU
  exact functor_action_eq_one_of_iso (A := PadicAlgCl l) (G := G)
    (LisseQlbar.integralClosure l U) R.algebraic.functor aU ⟨M, h⟩ ep g haU


private theorem nonempty_source_of_pullback
    {X Y Z T : Scheme.{u}} (f : Y ⟶ Z) (a : T ⟶ Z)
    (e : X ≅ pullback f a) (x : X) : Nonempty Y :=
  ⟨pullback.fst f a (e.hom x)⟩

private theorem lattice_localization_iso
    (Λ B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj B] [IsCommMonObj B]
    (a : Λ ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hQ : LisseQlbar.hasLattice Λ B a X Q) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      CondensedRing.LocallyFree (condensedRingObj Λ X) N ∧
      Nonempty ((Mod.extendScalars (coefficientMap a X)).obj N ≅ Q) := by
  obtain ⟨N, hN, i, _, hi⟩ := hQ
  let := hi
  exact ⟨N, hN, ⟨asIso (((Mod.extendRestrictAdjunction
    (coefficientMap a X)).homEquiv N Q).symm i)⟩⟩

private theorem scalar_model_pullback_iso
    (Λ B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj B] [IsCommMonObj B]
    (a : Λ ⟶ B) [IsMonHom a] {U C : Scheme.{u}} (j : U ⟶ C)
    (Q : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C))
    (L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj B C))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj B U))
    (eQ : (Mod.extendScalars (coefficientMap a C)).obj Q ≅ L)
    (eLM : (CondensedRing.upperStar B j).obj L ≅ M) :
    Nonempty ((Mod.extendScalars (coefficientMap a U)).obj
      ((CondensedRing.upperStar Λ j).obj Q) ≅ M) :=
  ⟨(CondensedRing.pullIso a j).app Q ≪≫ (CondensedRing.upperStar B j).mapIso eQ ≪≫ eLM⟩

private theorem integral_field_lattice_iso
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) (C : Scheme.{u})
    (Q : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (LisseQlbar.fieldRing l E) C))
    (hQ : LisseQlbar.integralField l E C Q) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
        (condensedRingObj (LisseQlbar.integerRing l E) C),
      CondensedRing.LocallyFree (condensedRingObj (LisseQlbar.integerRing l E) C) N ∧
      Nonempty ((Mod.extendScalars
        (coefficientMap (LisseQlbar.integerInclusion l E) C)).obj N ≅ Q) :=
  lattice_localization_iso (LisseQlbar.integerRing l E) (LisseQlbar.fieldRing l E)
    (LisseQlbar.integerInclusion l E) C Q hQ.2

set_option maxHeartbeats 1000000 in
-- Specializing the coefficient and representation records unfolds large sheaf functors.
private theorem integral_model_extension_kernel
    (l : ℕ) [Fact l.Prime] {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G)
    (H : ProfiniteGrp.{u}) [∀ P, MulAction H ((fiber (b ≫ j)).obj P)]
    (S : LisseQlbar.Correspondence l (b ≫ j) H)
    (L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) C))
    (hL : LisseQlbar.integralClosure l C L)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (eLM : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).obj L ≅ M) :
    ∃ h : LisseQlbar.integralClosure l U M,
      ∀ g : G, (pullbackPathHom j b) (eG g) = 1 →
        (R.algebraic.functor.obj ⟨M, h⟩).ρ g = 1 := by
  classical
  obtain ⟨E, Q, hQ, ⟨eQ⟩⟩ := hL.2
  obtain ⟨N, hN, ⟨eN⟩⟩ := integral_field_lattice_iso l E C Q hQ
  obtain ⟨eM⟩ := scalar_model_pullback_iso (LisseQlbar.fieldRing l E)
    (Profinite.padicAlgClRingObj l) (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
    j Q L M eQ eLM
  exact pulled_lattice_kernel l j b G eG _haction R H S E N hN Q eN M eM

set_option maxHeartbeats 1000000 in
-- The normalized correspondence has large coefficient and fibre comparison records.
private theorem regular_extension_kernel
    (l : ℕ) [Fact l.Prime] {U C : Scheme.{u}} (j : U ⟶ C)
    [IsLocallyNoetherian C] [CompactSpace C] [ConnectedSpace C] [IsRegular C]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G)
    (L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) C))
    (hL : CondensedRing.LocallyFree (condensedRingObj (Profinite.padicAlgClRingObj l) C) L)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (eLM : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).obj L ≅ M) :
    ∃ h : LisseQlbar.integralClosure l U M,
      ∀ g : G, (pullbackPathHom j b) (eG g) = 1 →
        (R.algebraic.functor.obj ⟨M, h⟩).ρ g = 1 := by
  classical
  obtain ⟨H, aH, hH⟩ := exists_isFundamentalGroup (b ≫ j)
  let := aH
  let := hH
  obtain ⟨S⟩ := LisseQlbar.lisse_qlbar_representations l C Ω (b ≫ j) H
  have hnormal (p : C) : IsDomain (C.presheaf.stalk p) ∧
      IsIntegrallyClosed (C.presheaf.stalk p) :=
    ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk p⟩
  exact integral_model_extension_kernel l j b G eG _haction R H S L
    (S.normalAlgebraic hnormal L hL) M eLM


set_option maxHeartbeats 1000000 in
-- The proof uses normalized finite-reduction and scalar-extension comparison records.
/-- Forward half of the normalized extension-kernel criterion: if `M` is the pullback
of a lisse module on `C`, some integral witness `h` makes `R.algebraic(M, h)` kill
every `g` with `pullbackPathHom j b (eG g) = 1`.

Source: rem-dl-a1-conventions, the unramified-at-infinity equivalence (proof steps
of lem-dl-a1-condensed-lisse-extension-inertia); steps 1-2 and the forward half of
step 3 of lem-dl-a1-condensed-lisse-extension-kernel.
(blueprint: lem-dl-a1-condensed-lisse-extension-kernel-forward).

Proof: the geometric point maps into `C`, so its original projective-line open
is nonempty. Its field base change is connected, compact, locally Noetherian and
regular. The coefficient pullback isomorphism identifies the two definitions of
lisse modules. A correspondence on `C` therefore supplies an integral finite-field
model of the extension and a locally free integral lattice `N`.

Pull `N` back to `U`. At every uniformizer-power level, scalar multiplication
commutes with pullback through the coefficient isomorphism. Inverse image preserves
the cokernel; full faithfulness of the étale/pro-étale comparison identifies its
étale origin with the inverse image of the reduction on `C`. After forgetting to
sets this is represented by a pulled-back finite étale cover. A kernel element of
`pullbackPathHom` fixes all points of such a cover. Naturality and the normalized
finite-evaluation clauses transfer this equality to its finite module action.
No identification of different choices of fibre comparison is needed.

Uniqueness in `ReductionComplete` now makes the integral action trivial. Present
the rational and algebraic models on `U` by extending this pulled lattice; the
`localization` and `algebraicExtension` clauses make their actions trivial, by
induction on pure tensors. The coefficient pullback comparison isomorphisms give
an isomorphism from the resulting algebraic model to `M`. Transporting its integral
witness and its representation through this isomorphism proves the assertion.
-/
theorem condensed_lisse_extension_kernel_forward
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hl : l ≠ D.p)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (hUC : U₀ ≤ C₀) (U C : Scheme.{u})
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))
    (_hj₀ : j₀.left = (ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (_hj : j = eU.hom ≫ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫ eC.inv)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (_hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (_hb : IsGenericPoint (b (IsLocalRing.closedPoint Ω)) Set.univ)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G) :
    (∃ L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) C),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L ∧
        Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).obj L ≅ M)) →
    ∃ h : LisseQlbar.integralClosure l U M,
      ∀ g : G, (pullbackPathHom j b) (eG g) = 1 →
        (R.algebraic.functor.obj ⟨M, h⟩).ρ g = 1 := by
  classical
  intro ⟨L, hL, ⟨eLM⟩⟩
  let a := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let f := C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)
  have : Nonempty C₀ :=
    nonempty_source_of_pullback f a eC (j (b (IsLocalRing.closedPoint Ω)))
  obtain ⟨hNoeth, hCompact, hConn, hReg⟩ :=
    geometric_projective_open_properties D.k₀ D.k C₀ C eC
  let := hNoeth
  let := hCompact
  let := hConn
  let := hReg
  exact regular_extension_kernel l j b G eG _haction R L
    ((lisse_iff_locallyFree _ L).mp hL) M eLM

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
