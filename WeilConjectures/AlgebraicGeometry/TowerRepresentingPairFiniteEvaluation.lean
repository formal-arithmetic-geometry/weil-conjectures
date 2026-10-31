/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.EtaleLocalNormalForm

import WeilConjectures.CategoryTheory.SystemSingleDerivedEvaluation
import WeilConjectures.CategoryTheory.SystemDerivedEvaluation
import all WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
import all WeilConjectures.AlgebraicGeometry.FiniteCtfTriangulated
import all WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.CoefficientTowerCompactSupportStrictTransition
import WeilConjectures.SecSmoothPurity.ProperScalarCounitSquare
import WeilConjectures.AlgebraicGeometry.OpenScalarCounitSquare
import all WeilConjectures.AlgebraicGeometry.TowerRepresentingPairScalarChange
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Finite evaluation of a tower representing pair
Source: latest blueprint, tower-geometric Levels paragraph.
(blueprint: lem-dla1-tower-representing-pair-finite-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

section LocalDerivedSquare

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]

-- The supplied comparison on a complex, with its terminal evaluation factor exposed.
private theorem local_comparison_rep (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso s).hom.app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategoryFactors.hom.app P =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F G P]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact Category.assoc _ _ _


-- A square of exact functors descends from its equations on complex representatives.
private theorem local_represented_square
    (F : A ⥤ B) (N : B ⥤ C) (M : B ⥤ D)
    (N' : A ⥤ C) (M' : A ⥤ D) (R : D ⥤ C)
    [F.Additive] [N.Additive] [M.Additive] [N'.Additive] [M'.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits N'] [PreservesFiniteColimits N']
    [PreservesFiniteLimits M'] [PreservesFiniteColimits M']
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (t : N ⟶ M ⋙ R) (t' : N' ⟶ M' ⋙ R)
    (td : N.mapDerivedCategory ⟶ M.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (td' : N'.mapDerivedCategory ⟶ M'.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (ht : ∀ P : CochainComplex B ℤ,
      td.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) =
      N.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app P))
    (ht' : ∀ P : CochainComplex A ℤ,
      td'.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map (M'.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((M'.mapHomologicalComplex (.up ℤ)).obj P) =
      N'.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t' (.up ℤ)).app P))
    (sn : F ⋙ N ≅ N') (sm : F ⋙ M ≅ M')
    (hs : ∀ X : A, t.app (F.obj X) ≫ R.map (sm.hom.app X) =
      sn.hom.app X ≫ t'.app X) (K : DerivedCategory A) :
    td.app (F.mapDerivedCategory.obj K) ≫
      R.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso F M).symm ≪≫
          Functor.mapDerivedCategoryNatIso sm).hom.app K) =
    ((Functor.mapDerivedCategoryCompIso F N).symm ≪≫
      Functor.mapDerivedCategoryNatIso sn).hom.app K ≫ td'.app K := by
  let cn := ((Functor.mapDerivedCategoryCompIso F N).symm ≪≫
    Functor.mapDerivedCategoryNatIso sn).hom
  let cm := ((Functor.mapDerivedCategoryCompIso F M).symm ≪≫
    Functor.mapDerivedCategoryNatIso sm).hom
  let a := Functor.whiskerLeft F.mapDerivedCategory td ≫
    Functor.whiskerRight cm R.mapDerivedCategory
  let b := cn ≫ td'
  have hab : a = b := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro P
    dsimp only [a, b, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply (cancel_mono
      (R.mapDerivedCategory.map (M'.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((M'.mapHomologicalComplex (.up ℤ)).obj P))).mp
    simp only [Category.assoc]
    rw [ht' P]
    have hc := local_comparison_rep F N N' sn P
    change cn.app (DerivedCategory.Q.obj P) ≫
      N'.mapDerivedCategoryFactors.hom.app P = _ at hc
    rw [reassoc_of% hc]
    have hm := local_comparison_rep F M M' sm P
    change cm.app (DerivedCategory.Q.obj P) ≫
      M'.mapDerivedCategoryFactors.hom.app P = _ at hm
    rw [← R.mapDerivedCategory.map_comp_assoc, hm]
    simp only [Functor.map_comp, Category.assoc]
    erw [← td.naturality_assoc]
    erw [R.mapDerivedCategoryFactors.hom.naturality]
    erw [reassoc_of% (ht ((F.mapHomologicalComplex (.up ℤ)).obj P))]
    simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp]
    congr 2
    congr 1
    ext i
    exact hs (P.X i)
  exact NatTrans.congr_app hab K

end LocalDerivedSquare

private theorem evaluation_hom_bijective_component
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (LX : A ⥤ C) (EX : C ⥤ A) (ax : LX ⊣ EX)
    (LY : B ⥤ D) (EY : D ⥤ B) (ay : LY ⊣ EY)
    (F : C ⥤ D) (G : A ⥤ B) (v : F ⋙ EY ≅ EX ⋙ G)
    (H : C) (K : D) (eps : F.obj H ⟶ K) (M : A)
    (hiso : IsIso ((((mateEquiv ax ay).symm
      (TwoSquare.mk EX F G EY v.inv)).natTrans).app M))
    (hglobal : Function.Bijective (fun z : LX.obj M ⟶ H ↦ F.map z ≫ eps)) :
    Function.Bijective (fun z : M ⟶ EX.obj H ↦
      G.map z ≫ v.inv.app H ≫ EY.map eps) := by
  let t : G ⋙ LY ⟶ LX ⋙ F :=
    ((mateEquiv ax ay).symm (TwoSquare.mk EX F G EY v.inv)).natTrans
  let : IsIso (t.app M) := hiso
  let a := (ax.homEquiv M H).symm
  let b := Equiv.ofBijective _ hglobal
  let c := Iso.homCongr (asIso (t.app M)).symm (Iso.refl K)
  let d := ay.homEquiv (G.obj M) K
  let h := ((a.trans b).trans c).trans d
  have hm := mateEquiv_counit_symm ax ay (TwoSquare.mk EX F G EY v.inv) H
  change LY.map (v.inv.app H) ≫ ay.counit.app (F.obj H) =
    t.app (EX.obj H) ≫ F.map (ax.counit.app H) at hm
  have hc : (ay.homEquiv _ K)
      (t.app (EX.obj H) ≫ F.map (ax.counit.app H) ≫ eps) =
      v.inv.app H ≫ EY.map eps := by
    rw [← Category.assoc, ← hm, Category.assoc,
      ay.homEquiv_naturality_left, ay.homEquiv_naturality_right]
    have hh := congrArg (ay.homEquiv _ (F.obj H)) (ay.homEquiv_symm_id (F.obj H))
    simp only [Equiv.apply_symm_apply] at hh
    dsimp only [Functor.comp_obj, Functor.id_obj]
    rw [← hh, Category.id_comp]
  have hh : (fun z : M ⟶ EX.obj H ↦
      G.map z ≫ v.inv.app H ≫ EY.map eps) = h := by
    funext z
    dsimp [h, a, b, c, d, Iso.homCongr]
    rw [← hc, ← ay.homEquiv_naturality_left]
    apply congrArg (ay.homEquiv (G.obj M) K)
    simp only [Category.comp_id, ax.homEquiv_counit, F.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      t.naturality_assoc z (F.map (ax.counit.app H) ≫ eps)
  rw [hh]
  exact h.bijective

private theorem finite_scalar_ctf {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (f : A →+* B) (T : Scheme.{u})
    (M : spFiniteConstructibleTorCategory T A) :
    spFiniteConstructibleTor T B ((scalarExtensionFunctor f T).obj M.obj) := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := M.property
  have hf : Set.Finite {i : ℤ | ¬ IsZero
      ((DerivedCategory.homologyFunctor _ i).obj M.obj)} := by
    apply (Set.finite_Icc a b).subset
    intro i hi
    constructor <;> by_contra! h
    · exact hi (hv i (Or.inl h))
    · exact hi (hv i (Or.inr h))
  have hs := ProEtale.scalarExtension_tor f T M.obj s t ht
  have hbound := ProEtale.scalarExtension_bounded_of_tor T B _ s t hs
  obtain ⟨c, hc'⟩ := hbound.bddBelow
  obtain ⟨d, hd⟩ := hbound.bddAbove
  refine ⟨⟨min c d, d, min_le_right _ _, ?_⟩,
    ProEtale.scalarExtension_constructible f T M.obj hf hc, s, t, hs⟩
  intro i hi
  by_contra h
  rcases hi with hi | hi
  · exact (not_lt_of_ge (hc' h)) (hi.trans_le (min_le_left _ _))
  · exact (not_lt_of_ge (hd h)) hi

private theorem zero_tor (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (hK : IsZero K)
    (a b : ℤ) (hab : a ≤ b) : HasProEtaleTorAmplitude T A K a b := by
  refine ⟨hab, ?_⟩
  intro L P hL f hf hP M i _hi
  obtain ⟨F, c, htri, hcomp⟩ := Scheme.tensor_functor T A M
  obtain ⟨e⟩ := hL
  obtain ⟨q⟩ := hcomp L P f hf hP
  have hz := F.map_isZero (hK.of_iso e)
  exact ((DerivedCategory.homologyFunctor _ i).map_isZero hz).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso q.symm)


private theorem finite_ctf_iso {T : Scheme.{u}} {A : Type u}
    [CommRing A] [Finite A] {K L : proEtaleDerivedCategory T A}
    (e : K ≅ L) (h : spFiniteConstructibleTor T A K) :
    spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a, b, hab, ?_⟩, ?_, s, t, ?_⟩
  · intro i hi
    exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    apply (proEtaleModuleRestriction_constructible_iff T A _).mpr
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e))
      ((proEtaleModuleRestriction_constructible_iff T A _).mp (hc i))
  · exact Scheme.amplitude_iso T A e s t ht

private theorem finite_zero_ctf (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) (hK : IsZero K) :
    spFiniteConstructibleTor T A K := by
  refine ⟨⟨0, 0, le_rfl, fun i _ ↦ (DerivedCategory.homologyFunctor _ i).map_isZero hK⟩,
    ?_, 0, 0, zero_tor T A K hK 0 0 le_rfl⟩
  intro i
  exact Scheme.constructibleProEtale_of_isZero T A _
    ((DerivedCategory.homologyFunctor _ i).map_isZero hK)


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem finite_support_uniform (T : Scheme.{u}) (n : ℕ)
    (K : spDerivedCoefficientTowers l E T (q.abelian T))
    (hf : ∀ m, spFiniteConstructibleTor T (SpTowerShriek.R l E m)
      ((spDerivedCoefficientEvaluation l E T (q.abelian T) m).obj K))
    (hz : ∀ m, n < m → IsZero
      ((spDerivedCoefficientEvaluation l E T (q.abelian T) m).obj K)) :
    spConstructibleTorTowers l E T (q.abelian T) K := by
  classical
  have hi (m : ℕ) : ∃ a d s t : ℤ, a ≤ d ∧
      (∀ i : ℤ, i < a ∨ d < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) m).obj K))) ∧
      HasProEtaleTorAmplitude T (SpTowerShriek.R l E m)
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) m).obj K) s t := by
    obtain ⟨⟨a, d, had, hv⟩, _, s, t, ht⟩ := hf m
    exact ⟨a, d, s, t, had, hv, ht⟩
  choose a d s t had hv ht using hi
  obtain ⟨A, hA⟩ := (Set.finite_range (fun m : Fin (n + 1) ↦ a m)).bddBelow
  obtain ⟨D, hD⟩ := (Set.finite_range (fun m : Fin (n + 1) ↦ d m)).bddAbove
  obtain ⟨S, hS⟩ := (Set.finite_range (fun m : Fin (n + 1) ↦ s m)).bddBelow
  obtain ⟨T', hT⟩ := (Set.finite_range (fun m : Fin (n + 1) ↦ t m)).bddAbove
  have ha (m : Fin (n + 1)) : A ≤ a m := hA (Set.mem_range_self m)
  have hd (m : Fin (n + 1)) : d m ≤ D := hD (Set.mem_range_self m)
  have hs (m : Fin (n + 1)) : S ≤ s m := hS (Set.mem_range_self m)
  have ht' (m : Fin (n + 1)) : t m ≤ T' := hT (Set.mem_range_self m)
  have had' : A ≤ D := (ha 0).trans ((had 0).trans (hd 0))
  have hst : S ≤ T' := (hs 0).trans ((ht 0).1.trans (ht' 0))
  refine ⟨hf, A, D, S, T', had', hst, ?_⟩
  intro m
  by_cases hm : m ≤ n
  · let m' : Fin (n + 1) := ⟨m, by omega⟩
    refine ⟨?_, Scheme.amplitude_mono T _ (ht m) (hs m') (ht' m')⟩
    intro i hi
    apply hv m i
    rcases hi with hi | hi
    · exact Or.inl (hi.trans_le (ha m'))
    · exact Or.inr ((hd m').trans_lt hi)
  · have hzero := hz m (Nat.lt_of_not_ge hm)
    exact ⟨fun i _ ↦ (DerivedCategory.homologyFunctor _ i).map_isZero hzero,
      zero_tor T _ _ hzero S T' hst⟩

private def evaluationExtension (T : Scheme.{u}) (n : ℕ) :
    proEtaleDerivedCategory T (SpTowerShriek.R l E n) ⥤
      spDerivedCoefficientTowers l E T (q.abelian T) := by
  let A := q.abelian T
  let := A.hasDerived
  let := A.equivalenceAdditive
  let B := spCoefficientCommRings l E T
  let := HasDerivedCategory.standard (StrictRingSystem.{u + 1, u, u + 1} B)
  exact (systemSingleDerivedExtension B n A.scalar A.tensor).derived ⋙
    A.equivalence.mapDerivedCategory.inverse

private def evaluationExtensionAdjunction (T : Scheme.{u}) (n : ℕ) :
    evaluationExtension l E b q T n ⊣
      spDerivedCoefficientEvaluation l E T (q.abelian T) n := by
  let A := q.abelian T
  let := A.hasDerived
  let := A.equivalenceAdditive
  let B := spCoefficientCommRings l E T
  let := HasDerivedCategory.standard (StrictRingSystem.{u + 1, u, u + 1} B)
  let d := systemSingleDerivedExtension B n A.scalar A.tensor
  let D := A.equivalence.mapDerivedCategory
  let a := d.adjunction.comp D.symm.toAdjunction
  let e : D.functor ⋙ derivedSystemEvaluation B n ≅
      spDerivedCoefficientEvaluation l E T A n :=
    (Functor.mapDerivedCategoryCompIso A.equivalence.functor
      (systemEvaluation B n)).symm
  exact a.ofNatIsoRight e

private def evaluationExtensionLevelIso (T : Scheme.{u}) (n m : ℕ)
    (P : proEtaleDerivedCategory T (SpTowerShriek.R l E n)) := by
  let A := q.abelian T
  let := A.hasDerived
  let := A.equivalenceAdditive
  let B := spCoefficientCommRings l E T
  let := HasDerivedCategory.standard (StrictRingSystem.{u + 1, u, u + 1} B)
  let d := systemSingleDerivedExtension B n A.scalar A.tensor
  let D := A.equivalence.mapDerivedCategory
  exact ((Functor.mapDerivedCategoryCompIso A.equivalence.functor (systemEvaluation B m)).app
    (D.inverse.obj (d.derived.obj P))) ≪≫
      (derivedSystemEvaluation B m).mapIso (D.counitIso.app (d.derived.obj P))

private theorem evaluationExtension_above (T : Scheme.{u}) (n m : ℕ) (hm : n < m)
    (P : proEtaleDerivedCategory T (SpTowerShriek.R l E n)) :
    IsZero ((spDerivedCoefficientEvaluation l E T (q.abelian T) m).obj
      ((evaluationExtension l E b q T n).obj P)) := by
  let A := q.abelian T
  let := A.hasDerived
  let := HasDerivedCategory.standard
    (StrictRingSystem.{u + 1, u, u + 1} (spCoefficientCommRings l E T))
  exact (systemSingleDerivedAbove A.scalar A.tensor
    (spCoefficientCommRings l E T) m n hm P).of_iso
      (evaluationExtensionLevelIso l E b q T n m P)

-- Transpose the recorded reduction before cancelling its localization factors.
set_option maxHeartbeats 4000000 in
-- Unfolding the coefficient presentations requires a larger elaboration budget.
private theorem local_system_transpose_rep (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) {m n : ℕ} (h : m ≤ n)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) :
    let _ := a.hasDerived
    let _ := a.equivalenceAdditive
    let _ := a.evaluationLimits
    let _ := a.evaluationColimits
    (SheafOfModules.systemDerivedTensorAdj a.scalar
      (spCoefficientCommRings l E T) h).homEquiv _ _
        ((a.reduction h).app (DerivedCategory.Q.obj P)) ≫
      (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategory.map
        ((spCoefficientEvaluation l E T a.equivalence m).mapDerivedCategoryFactors.hom.app P) ≫
      (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategoryFactors.hom.app
        (((spCoefficientEvaluation l E T a.equivalence m).mapHomologicalComplex (.up ℤ)).obj P) =
    (spCoefficientEvaluation l E T a.equivalence n).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft a.equivalence.functor
            (SheafOfModules.strictSystemTransition (spCoefficientCommRings l E T) h))
          (.up ℤ)).app P) := by
  let _ := a.hasDerived
  let _ := a.equivalenceAdditive
  let _ := a.evaluationLimits
  let _ := a.evaluationColimits
  let D := a.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)
  let en := spCoefficientEvaluation l E T a.equivalence n
  let em := spCoefficientEvaluation l E T a.equivalence m
  let r := (NatTrans.mapHomologicalComplex (a.ordinaryReduction h) (.up ℤ)).app P
  let t := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft a.equivalence.functor
      (SheafOfModules.strictSystemTransition (spCoefficientCommRings l E T) h))
    (.up ℤ)).app P
  have ht : (D.ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv
      ((en.mapHomologicalComplex (.up ℤ)).obj P)
      ((em.mapHomologicalComplex (.up ℤ)).obj P) r = t := by
    ext i : 1
    change D.ordinaryAdj.unit.app _ ≫ _ = _
    change (D.ordinaryAdj.homEquiv _ _ ((a.ordinaryReduction h).app (P.X i))) = _
    rw [a.ordinaryReduction_eq]
    exact (D.ordinaryAdj.homEquiv _ _).apply_symm_apply _
  have htrans := D.transpose ((en.mapHomologicalComplex (.up ℤ)).obj P)
    ((em.mapHomologicalComplex (.up ℤ)).obj P) r
  rw [ht] at htrans
  have hr : D.adjunction.homEquiv _ _ ((a.reduction h).app (DerivedCategory.Q.obj P)) =
      en.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map t ≫
        (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategoryFactors.inv.app
          ((em.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategory.map
          (em.mapDerivedCategoryFactors.inv.app P) := by
    rw [a.reduction_rep]
    change D.adjunction.homEquiv _ _
      (D.model.T.map (en.mapDerivedCategoryFactors.hom.app P) ≫
        D.model.ε.app _ ≫ DerivedCategory.Q.map r ≫
          em.mapDerivedCategoryFactors.inv.app P) = _
    calc
      _ = en.mapDerivedCategoryFactors.hom.app P ≫
          D.adjunction.homEquiv _ _
            ((D.model.ε.app _ ≫ DerivedCategory.Q.map r) ≫
              em.mapDerivedCategoryFactors.inv.app P) := by
        simpa only [Category.assoc] using D.adjunction.homEquiv_naturality_left
          (en.mapDerivedCategoryFactors.hom.app P)
          ((D.model.ε.app _ ≫ DerivedCategory.Q.map r) ≫
            em.mapDerivedCategoryFactors.inv.app P)
      _ = _ := by
        rw [D.adjunction.homEquiv_naturality_right]
        erw [htrans]
        simp only [Category.assoc]
  rw [hr]
  simp only [Category.assoc]
  change en.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map t ≫
    (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategoryFactors.inv.app
      ((em.mapHomologicalComplex (.up ℤ)).obj P) ≫
    (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategory.map
      (em.mapDerivedCategoryFactors.inv.app P) ≫
    (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategory.map
      (em.mapDerivedCategoryFactors.hom.app P) ≫
    (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategoryFactors.hom.app
      ((em.mapHomologicalComplex (.up ℤ)).obj P) =
    en.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map t
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategory.map_id,
    Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

private def local_systemDerivedTranspose (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) {m n : ℕ} (h : m ≤ n) :
    spDerivedCoefficientEvaluation l E T a n ⟶
      spDerivedCoefficientEvaluation l E T a m ⋙
        (systemRestriction (spCoefficientCommRings l E T) h).mapDerivedCategory where
  app K := (SheafOfModules.systemDerivedTensorAdj a.scalar
    (spCoefficientCommRings l E T) h).homEquiv _ _ ((a.reduction h).app K)
  naturality {K L} f :=
    (SheafOfModules.systemDerivedTensorAdj a.scalar
      (spCoefficientCommRings l E T) h).homEquiv_naturality_left_square
      ((spDerivedCoefficientEvaluation l E T a n).map f) ((a.reduction h).app L)
      ((a.reduction h).app K) ((spDerivedCoefficientEvaluation l E T a m).map f)
      ((a.reduction h).naturality f)


set_option maxHeartbeats 2000000 in
-- Transport the normalized scalar transpose across the exact derived equivalence.
private theorem singleton_reduction_intrinsic_below (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n)
    (P : proEtaleDerivedCategory T (SpTowerShriek.R l E n)) :
    IsIso ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) T).map
        ((evaluationExtensionAdjunction l E b q T n).unit.app P) ≫
      SpTowerCalculus.reduction l E T (q.abelian T) h (q.scalar T h)
        ((evaluationExtension l E b q T n).obj P)) := by
  let A := q.abelian T
  let := A.hasDerived
  let := A.equivalenceAdditive
  let := A.evaluationLimits
  let := A.evaluationColimits
  let B := spCoefficientCommRings l E T
  let := HasDerivedCategory.standard (StrictRingSystem.{u + 1, u, u + 1} B)
  let D := A.equivalence.mapDerivedCategory
  let d := systemSingleDerivedExtension B n A.scalar A.tensor
  let en := spDerivedCoefficientEvaluation l E T A n
  let em := spDerivedCoefficientEvaluation l E T A m
  let cn := (Functor.mapDerivedCategoryCompIso A.equivalence.functor
    (systemEvaluation B n)).symm
  let cm := (Functor.mapDerivedCategoryCompIso A.equivalence.functor
    (systemEvaluation B m)).symm
  let a := evaluationExtensionAdjunction l E b q T n
  let ax := systemDerivedTensorAdj A.scalar B h
  let N := (evaluationExtension l E b q T n).obj P
  have hs (K : spDerivedCoefficientTowers l E T A) :
      (systemDerivedTransition B h).app (D.functor.obj K) ≫
          (systemRestriction B h).mapDerivedCategory.map (cm.hom.app K) =
        cn.hom.app K ≫ ax.homEquiv _ _ ((A.reduction h).app K) := by
    have hh := local_represented_square A.equivalence.functor
      (systemEvaluation B n) (systemEvaluation B m)
      (spCoefficientEvaluation l E T A.equivalence n)
      (spCoefficientEvaluation l E T A.equivalence m) (systemRestriction B h)
      (strictSystemTransition B h)
      (Functor.whiskerLeft A.equivalence.functor (strictSystemTransition B h))
      (systemDerivedTransition B h) (local_systemDerivedTranspose l E T A h)
      (systemDerivedTransition_rep B h)
      (local_system_transpose_rep l E T A h)
      (Iso.refl _) (Iso.refl _) (by intro M; simp) K
    simp only [Iso.trans_hom, Functor.mapDerivedCategoryNatIso_refl, Category.comp_id,
      local_systemDerivedTranspose, spDerivedCoefficientEvaluation,
      spCoefficientEvaluation] at hh
    convert hh using 1
    rfl
  have hu : a.unit.app P ≫ cn.inv.app N =
      d.adjunction.unit.app P ≫
        (derivedSystemEvaluation B n).map (D.counitIso.inv.app (d.derived.obj P)) := by
    change ((d.adjunction.comp D.symm.toAdjunction).unit.app P ≫ cn.hom.app N) ≫
      cn.inv.app N = _
    rw [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id, Adjunction.comp_unit_app]
    rfl
  have he : (systemDerivedTensor A.scalar B h).map (a.unit.app P) ≫
      (A.reduction h).app N =
      (systemSingleDerivedBelow B h A.scalar A.tensor).inv.app P ≫
        (derivedSystemEvaluation B m).map
          (D.counitIso.inv.app (d.derived.obj P)) ≫ cm.hom.app N := by
    apply ax.homEquiv P (em.obj N) |>.injective
    rw [ax.homEquiv_naturality_left, ax.homEquiv_naturality_right]
    have ht := systemSingleDerivedTranspose A.scalar A.tensor B h P
      (d.derived.obj P) (𝟙 _)
    erw [(derivedSystemEvaluation B m).map_id, Category.comp_id,
      d.adjunction.homEquiv_id] at ht
    erw [ht]
    rw [Functor.map_comp]
    have hsn := hs N
    have hsn' : ax.homEquiv (en.obj N) (em.obj N) ((A.reduction h).app N) =
        cn.inv.app N ≫ (systemDerivedTransition B h).app (D.functor.obj N) ≫
          (systemRestriction B h).mapDerivedCategory.map (cm.hom.app N) := by
      erw [hsn]
      simp
      rfl
    erw [hsn']
    rw [← Category.assoc (a.unit.app P), hu]
    have hn := (systemDerivedTransition B h).naturality
      (D.counitIso.inv.app (d.derived.obj P))
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc]
    erw [reassoc_of% hn]
    simp only [Category.assoc]
  have hi : IsIso ((systemDerivedTensor A.scalar B h).map (a.unit.app P) ≫
      (A.reduction h).app N) := by
    rw [he]
    infer_instance
  change IsIso ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) T).map
    (a.unit.app P) ≫ (q.scalar T h).scalar.inv.app (en.obj N) ≫ (A.reduction h).app N)
  erw [(q.scalar T h).scalar.inv.naturality_assoc]
  exact IsIso.comp_isIso' (by infer_instance) hi

private theorem evaluationExtension_ctf (T : Scheme.{u}) (n : ℕ)
    (P : spFiniteConstructibleTorCategory T (SpTowerShriek.R l E n)) :
    spConstructibleTorTowers l E T (q.abelian T)
      ((evaluationExtension l E b q T n).obj P.obj) := by
  let A := q.abelian T
  let := A.hasDerived
  let := A.equivalenceAdditive
  let B := spCoefficientCommRings l E T
  let := HasDerivedCategory.standard (StrictRingSystem.{u + 1, u, u + 1} B)
  let d := systemSingleDerivedExtension B n A.scalar A.tensor
  let e := fun m ↦ evaluationExtensionLevelIso l E b q T n m P.obj
  have hz (m : ℕ) (hm : n < m) : IsZero
      ((spDerivedCoefficientEvaluation l E T A m).obj
        ((evaluationExtension l E b q T n).obj P.obj)) :=
    evaluationExtension_above l E b q T n m hm P.obj
  apply finite_support_uniform l E b q T n _ _ hz
  intro m
  by_cases hm : m ≤ n
  · let c := (e m) ≪≫ (systemSingleDerivedBelow B hm A.scalar A.tensor).app P.obj ≪≫
      (q.scalar T hm).scalar.app P.obj
    exact finite_ctf_iso c.symm (finite_scalar_ctf (SpTowerCalculus.quotient l E hm) T P)
  · exact finite_zero_ctf T _ _ (hz m (Nat.lt_of_not_ge hm))


private def normalizedEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) : SpTowerCalculus.Evaluation l E b o q c n := by
  let := (q.abelian X).hasDerived
  let := (q.abelian Y).hasDerived
  refine ⟨Functor.isoWhiskerLeft _ (SpTowerCalculus.levelComparison l E b q Y n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SpTowerCalculus.realization l E b X (q.abelian X)).functor ⋙
          SpTowerShriek.F l E b o c)
        (SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso ≪≫
          Functor.rightUnitor _) (SpTowerShriek.Ev l E Y n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (SpTowerShriek.Fcomparison l E b o c n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SpTowerCalculus.levelComparison l E b q X n) _, ?_⟩
  intro M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Category.id_comp]
  erw [Category.comp_id]

private def evaluationMate {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) (v : SpTowerCalculus.Evaluation l E b o q c n) :
    reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g ⋙
        evaluationExtension l E b q Y n ⟶
      evaluationExtension l E b q X n ⋙ SpTowerCalculus.F l E b o q c :=
  ((mateEquiv (evaluationExtensionAdjunction l E b q X n)
    (evaluationExtensionAdjunction l E b q Y n)).symm
      (TwoSquare.mk _ _ _ _ v.comparison.inv)).natTrans

private theorem local_coefficientSquare
    {XA XB YA YB : Type*} [Category XA] [Category XB] [Category YA] [Category YB]
    {TX : XA ⥤ XB} {RX : XB ⥤ XA} {TY : YA ⥤ YB} {RY : YB ⥤ YA}
    (ax : TX ⊣ RX) (ay : TY ⊣ RY) (FA : XA ⥤ YA) (FB : XB ⥤ YB)
    (d : RX ⋙ FA ≅ FB ⋙ RY) (b : FA ⋙ TY ⟶ TX ⋙ FB)
    (hc : ∀ L, TY.map (d.hom.app L) ≫ ay.counit.app (FB.obj L) =
      b.app (RX.obj L) ≫ FB.map (ax.counit.app L))
    {Pn : XA} {Pm : XB} {Qn : YA} {Qm : YB}
    (tP : Pn ⟶ RX.obj Pm) (tQ : Qn ⟶ RY.obj Qm)
    (θn : Qn ⟶ FA.obj Pn) (θm : Qm ⟶ FB.obj Pm)
    (rx : TX.obj Pn ⟶ Pm) (ry : TY.obj Qn ⟶ Qm)
    (hx : ax.homEquiv _ _ rx = tP) (hy : ay.homEquiv _ _ ry = tQ)
    (ht : tQ ≫ RY.map θm = θn ≫ FA.map tP ≫ d.hom.app Pm) :
    TY.map θn ≫ b.app Pn ≫ FB.map rx = ry ≫ θm := by
  have hrx : TX.map tP ≫ ax.counit.app Pm = rx := by
    calc
      _ = (ax.homEquiv Pn Pm).symm tP := (ax.homEquiv_counit _ _ _).symm
      _ = rx := by rw [← hx]; exact (ax.homEquiv _ _).symm_apply_apply rx
  have hry : TY.map tQ ≫ ay.counit.app Qm = ry := by
    calc
      _ = (ay.homEquiv Qn Qm).symm tQ := (ay.homEquiv_counit _ _ _).symm
      _ = ry := by rw [← hy]; exact (ay.homEquiv _ _).symm_apply_apply ry
  have hh := congrArg (fun t ↦ TY.map t ≫ ay.counit.app (FB.obj Pm)) ht
  simp only [Functor.map_comp, Category.assoc] at hh
  have hn : TY.map (RY.map θm) ≫ ay.counit.app (FB.obj Pm) =
      ay.counit.app Qm ≫ θm := by
    simpa only [Functor.comp_map, Functor.id_map] using ay.counit.naturality θm
  rw [hn, ← Category.assoc, hry] at hh
  rw [hc] at hh
  have hb := b.naturality tP
  dsimp only [Functor.comp_map] at hb
  rw [reassoc_of% hb] at hh
  rw [← FB.map_comp, hrx] at hh
  exact hh.symm


set_option maxHeartbeats 2000000 in
-- The derived counit comparisons require a larger elaboration budget.
private theorem local_supportScalarCounit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (h : Z ⟶ Y) (H : proEtaleDerivedCategory X B) :
    (scalarExtensionFunctor φ Y).map
        ((intrinsicCompactSupportRestriction φ j h).hom.app H) ≫
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := Y) φ)).counit.app
          ((reductionCompactSupport B j h).obj H) =
    (reductionDirectImageComparison φ j h).app ((scalarRestriction φ X).obj H) ≫
      (reductionCompactSupport B j h).map
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) φ)).counit.app H) := by
  have hp := ((properScalarCounitSquare φ h).2.2.1
    ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj H)).2
  have ho := congr_app (openScalarCounitSquare φ j) H
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ho
  change (scalarExtensionFunctor φ Y).map
      ((directImageConstantPush A h).map ((sfOpenRestrictionDerived j φ).hom.app H) ≫
        (directImageScalarRestrictionIso φ h).hom.app _) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  erw [hp]
  have hn := (directImageScalarComparison φ h).naturality
    ((sfOpenRestrictionDerived j φ).hom.app H)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← (directImageConstantPush B h).map_comp]
  erw [ho]
  rw [Functor.map_comp]
  exact (Category.assoc _ _ _).symm



private theorem support_reduction_square {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e : ∀ n, SpTowerCalculus.Evaluation l E b o q c n)
    (K : spDerivedCoefficientTowers l E X (q.abelian X))
    {m n : ℕ} (h : m ≤ n) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).map
        ((e n).comparison.hom.app K) ≫
      (reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g).app
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) K) =
    SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h)
        ((SpTowerCalculus.F l E b o q c).obj K) ≫
      (e m).comparison.hom.app K := by
  exact local_coefficientSquare
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := X) (SpTowerCalculus.quotient l E h)))
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := Y) (SpTowerCalculus.quotient l E h)))
    (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g)
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g)
    (intrinsicCompactSupportRestriction (SpTowerCalculus.quotient l E h) c.i c.g)
    (reductionDirectImageComparison (SpTowerCalculus.quotient l E h) c.i c.g)
    (local_supportScalarCounit (SpTowerCalculus.quotient l E h) c.i c.g)
    (SpTowerCalculus.intrinsicTransition l E X (q.abelian X) h (q.scalar X h) K)
    (SpTowerCalculus.intrinsicTransition l E Y (q.abelian Y) h (q.scalar Y h)
      ((SpTowerCalculus.F l E b o q c).obj K))
    ((e n).comparison.hom.app K) ((e m).comparison.hom.app K)
    (SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) K)
    (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h)
      ((SpTowerCalculus.F l E b o q c).obj K))
    (SpTowerCalculus.reduction_homEquiv_intrinsicTransition l E X (q.abelian X) h
      (q.scalar X h) K)
    (SpTowerCalculus.reduction_homEquiv_intrinsicTransition l E Y (q.abelian Y) h
      (q.scalar Y h) ((SpTowerCalculus.F l E b o q c).obj K))
    (SpTowerCalculus.compactSupport_intrinsicTransition l E b o q c e K h)

set_option maxHeartbeats 2000000 in
-- Paste the singleton units with the actual finite coefficient comparison.
private theorem evaluationMate_below {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n m : ℕ) (hm : m ≤ n)
    (v : SpTowerCalculus.Evaluation l E b o q c n)
    (P : proEtaleDerivedCategory X (SpTowerShriek.R l E n))
    (hcomp : IsIso ((reductionDirectImageComparison
      (SpTowerCalculus.quotient l E hm) c.i c.g).app P)) :
    IsIso ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) m).map
      ((evaluationMate l E b o q c n v).app P)) := by
  let ax := evaluationExtensionAdjunction l E b q X n
  let ay := evaluationExtensionAdjunction l E b q Y n
  let N := (evaluationExtension l E b q X n).obj P
  let Fn := reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g
  let Fm := reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g
  let EY := spDerivedCoefficientEvaluation l E Y (q.abelian Y) m
  let SY := scalarExtensionFunctor (SpTowerCalculus.quotient l E hm) Y
  let SX := scalarExtensionFunctor (SpTowerCalculus.quotient l E hm) X
  let t := (evaluationMate l E b o q c n v).app P
  let e := fun i ↦ normalizedEvaluation l E b o q c i
  let redY : spDerivedCoefficientEvaluation l E Y (q.abelian Y) n ⋙ SY ⟶ EY :=
    Functor.whiskerLeft _ (q.scalar Y hm).scalar.inv ≫ (q.abelian Y).reduction hm
  let redX := SpTowerCalculus.reduction l E X (q.abelian X) hm (q.scalar X hm) N
  let beta := reductionDirectImageComparison (SpTowerCalculus.quotient l E hm) c.i c.g
  let ux := SX.map (ax.unit.app P) ≫ redX
  let uy := SY.map (ay.unit.app (Fn.obj P)) ≫
    redY.app ((evaluationExtension l E b q Y n).obj (Fn.obj P))
  have hx : IsIso ux := singleton_reduction_intrinsic_below l E b q X hm P
  have hy : IsIso uy := singleton_reduction_intrinsic_below l E b q Y hm (Fn.obj P)
  have hv : (e n).comparison = v.comparison := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact ((e n).normalization K).trans (v.normalization K).symm
  have hs := support_reduction_square l E b o q c e N hm
  rw [hv] at hs
  change SY.map (v.comparison.hom.app N) ≫
    beta.app ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj N) ≫
      Fm.map redX =
    redY.app ((SpTowerCalculus.F l E b o q c).obj N) ≫
      (e m).comparison.hom.app N at hs
  have ht := (unit_mateEquiv_symm ax ay
    (TwoSquare.mk _ _ _ _ v.comparison.inv) P).symm
  change ay.unit.app (Fn.obj P) ≫
      (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map t =
    Fn.map (ax.unit.app P) ≫ v.comparison.inv.app N at ht
  have he : uy ≫ EY.map t ≫ (e m).comparison.hom.app N =
      beta.app P ≫ Fm.map ux := by
    dsimp only [uy]
    rw [Category.assoc, ← redY.naturality_assoc]
    dsimp only [Functor.comp_map]
    rw [← SY.map_comp_assoc, ht, SY.map_comp, Category.assoc]
    have hs' : SY.map (v.comparison.inv.app N) ≫
        redY.app ((SpTowerCalculus.F l E b o q c).obj N) ≫
          (e m).comparison.hom.app N =
        beta.app ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj N) ≫
          Fm.map redX := by
      rw [← hs]
      simp only [← SY.map_comp_assoc, Iso.inv_hom_id_app, SY.map_id, Category.id_comp]
    change SY.map (Fn.map (ax.unit.app P)) ≫ SY.map (v.comparison.inv.app N) ≫
      redY.app ((SpTowerCalculus.F l E b o q c).obj N) ≫
        (e m).comparison.hom.app N = _
    rw [hs']
    have hb := beta.naturality (ax.unit.app P)
    change SY.map (Fn.map (ax.unit.app P)) ≫
      beta.app ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj N) =
      beta.app P ≫ Fm.map (SX.map (ax.unit.app P)) at hb
    rw [← Category.assoc, hb, Category.assoc, ← Fm.map_comp]
  have hi : IsIso (uy ≫ EY.map t ≫ (e m).comparison.hom.app N) := by
    rw [he]
    exact IsIso.comp_isIso' hcomp (by infer_instance)
  have hj : IsIso (EY.map t ≫ (e m).comparison.hom.app N) :=
    IsIso.of_isIso_comp_left uy _
  exact IsIso.of_isIso_comp_right _ ((e m).comparison.hom.app N)

private theorem compactSupportExtension_above {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n m : ℕ) (hm : n < m)
    (v : SpTowerCalculus.Evaluation l E b o q c m)
    (P : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    IsZero ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) m).obj
      ((SpTowerCalculus.F l E b o q c).obj
        ((evaluationExtension l E b q X n).obj P))) := by
  exact ((reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map_isZero
    (evaluationExtension_above l E b q X n m hm P)).of_iso (v.comparison.app _)

private theorem evaluationMate_above {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n m : ℕ) (hm : n < m)
    (v : SpTowerCalculus.Evaluation l E b o q c n)
    (w : SpTowerCalculus.Evaluation l E b o q c m)
    (P : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    IsIso ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) m).map
      ((evaluationMate l E b o q c n v).app P)) := by
  have hs := evaluationExtension_above l E b q Y n m hm
    ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj P)
  have ht := compactSupportExtension_above l E b o q c n m hm w P
  exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩

private theorem coefficientEvaluation_isIso_iff (T : Scheme.{u})
    {M N : spDerivedCoefficientTowers l E T (q.abelian T)} (z : M ⟶ N) :
    IsIso z ↔ ∀ m, IsIso
      ((spDerivedCoefficientEvaluation l E T (q.abelian T) m).map z) := by
  let A := q.abelian T
  let := A.hasDerived
  let := A.equivalenceAdditive
  let B := spCoefficientCommRings l E T
  let := HasDerivedCategory.standard (StrictRingSystem.{u + 1, u, u + 1} B)
  let D := A.equivalence.mapDerivedCategory
  constructor
  · intro hz m
    infer_instance
  · intro hz
    have : IsIso (D.functor.map z) := by
      apply (systemDerivedEvaluation_isIso_iff B _).2
      intro m
      exact (NatIso.isIso_map_iff
        (Functor.mapDerivedCategoryCompIso A.equivalence.functor (systemEvaluation B m)) z).1
          (hz m)
    exact isIso_of_reflects_iso z D.functor

private theorem evaluationMate_isIso_of_below {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) (v : SpTowerCalculus.Evaluation l E b o q c n)
    (P : proEtaleDerivedCategory X (SpTowerShriek.R l E n))
    (hbelow : ∀ m, m ≤ n → IsIso
      ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) m).map
        ((evaluationMate l E b o q c n v).app P))) :
    IsIso ((evaluationMate l E b o q c n v).app P) := by
  apply (coefficientEvaluation_isIso_iff l E b q Y _).2
  intro m
  by_cases hm : m ≤ n
  · exact hbelow m hm
  · exact evaluationMate_above l E b o q c n m (Nat.lt_of_not_ge hm) v
      (normalizedEvaluation l E b o q c m) P

private theorem finite_evaluation_of_isIso_mate
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerCalculus.C l E b q Y) (H : SpTowerCalculus.C l E b q X)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (hglobal : ∀ M : SpTowerCalculus.C l E b q X,
      Function.Bijective (fun z : M.obj ⟶ H.obj ↦
        (SpTowerCalculus.F l E b o q c).map z ≫ eps))
    (n : ℕ) (v : SpTowerCalculus.Evaluation l E b o q c n)
    (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n))
    (hmate : IsIso ((evaluationMate l E b o q c n v).app M.obj)) :
    Function.Bijective (fun z : M.obj ⟶
        (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj H.obj ↦
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map z ≫
        (v.comparison.inv.app H.obj ≫
          (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map eps)) := by
  let N : SpTowerCalculus.C l E b q X :=
    ⟨(evaluationExtension l E b q X n).obj M.obj,
      evaluationExtension_ctf l E b q X n M⟩
  exact evaluation_hom_bijective_component
    (evaluationExtension l E b q X n)
    (spDerivedCoefficientEvaluation l E X (q.abelian X) n)
    (evaluationExtensionAdjunction l E b q X n)
    (evaluationExtension l E b q Y n)
    (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n)
    (evaluationExtensionAdjunction l E b q Y n)
    (SpTowerCalculus.F l E b o q c)
    (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g)
    v.comparison H.obj K.obj eps M.obj hmate (hglobal N)

/-- Finite coefficient evaluation of the specified tower representing pair.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Levels paragraph;
Zheng, Construction 4.1.
(blueprint: lem-dla1-tower-representing-pair-finite-evaluation).

Proof: take the normalized derived singleton left adjoint to evaluation. At
levels m at most n it is derived scalar extension of the input from R_n to R_m;
at levels above n it is zero. Scalar extension preserves finite-Tor
constructibility. Taking common bounds over the finitely many lower levels
makes this singleton an admissible uniformly constructible finite-Tor tower.
The strict-system transpose formula and the exact equivalence show that its
unit followed by intrinsic scalar reduction is invertible. Paste these maps
with the actual compact-support reduction square and the mate-unit identity.
The resulting square identifies the lower evaluation of the mate, up to the
invertible singleton maps, with the finite-Tor coefficient comparison. Thus
the mate is invertible below n; above n both endpoints are zero. Coefficient
evaluation detects that the mate itself is invertible. Apply hglobal to the
singleton extension of M and transpose under the two singleton adjunctions.
The mate-counit identity and naturality identify the four Hom equivalences
with exactly the displayed finite evaluation map. The argument includes n=0,
the zero test and empty schemes.
-/
theorem tower_representing_pair_finite_evaluation
    (k : Type u) [Field k] [PerfectField k] (_hell : IsUnit (l : k))
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (r : ℕ) [SmoothOfRelativeDimension r f.left]
    (c : Compactification f.left)
    (K : SpTowerCalculus.C l E b q Y.left)
    (H : SpTowerCalculus.C l E b q X.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (hglobal : ∀ M : SpTowerCalculus.C l E b q X.left,
      Function.Bijective (fun z : M.obj ⟶ H.obj ↦
        (SpTowerCalculus.F l E b o q c).map z ≫ eps)) :
    ∀ (n : ℕ) (v : SpTowerCalculus.Evaluation l E b o q c n)
      (M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E n)),
      Function.Bijective (fun z : M.obj ⟶
          (spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj ↦
        (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map z ≫
          (v.comparison.inv.app H.obj ≫
            (spDerivedCoefficientEvaluation l E Y.left (q.abelian Y.left) n).map eps)) := by
  intro n v M
  let hmate : IsIso ((evaluationMate l E b o q c n v).app M.obj) := by
    apply evaluationMate_isIso_of_below l E b o q c n v M.obj
    intro m hm
    apply evaluationMate_below l E b o q c n m hm v M.obj
    let : Y.left.Over (Spec (.of k)) := OverClass.ofHom Y.hom
    let : c.Z.Over (Spec (.of k)) := OverClass.ofHom (c.g ≫ Y.hom)
    let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType Y.hom)
    let : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
    let : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.hom))
    let : QuasiCompact (c.Z ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (c.g ≫ Y.hom))
    let : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
    exact finite_comparison_isIso l (SpTowerCalculus.quotient l E hm)
      ⟨n + 1, tower_level_annihilated l E n⟩
      ⟨m + 1, tower_level_annihilated l E m⟩ k c.i c.g M.obj M.property
  exact finite_evaluation_of_isIso_mate l E b o q c K H eps hglobal n v M hmate

end AlgebraicGeometry.ProEtale.SpTowerGluing
