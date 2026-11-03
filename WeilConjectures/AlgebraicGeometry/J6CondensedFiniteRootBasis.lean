/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots

import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
import all WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatibleIntegralRootBases
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Finite and integral coefficient bases from a compatible root diagram

Source: current blueprint, sk-def-sp-tate-twist-locally-free, clauses (2)--(3).
(blueprint: lem-sp-condensed-finite-root-basis)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w u' v'

section

open CategoryTheory Limits MonoidalCategory Preadditive Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem freeConstantResidue_isIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (N : ℕ) (hN : N • 𝟙 (Mod.regular R) = 0) :
    IsIso ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      Mod.freeFunctor R).map (AddCommGrpCat.intResidue N)) := by
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ Mod.freeFunctor R
  have : (Mod.freeFunctor R).IsLeftAdjoint := ⟨_, ⟨Mod.freeForgetAdjunction R⟩⟩
  let c := CokernelCofork.ofπ (AddCommGrpCat.intResidue.{u} N)
    (AddCommGrpCat.intResidue_condition N)
  let e := freeConstantUnitIso X R
  have hf : F.map (N • 𝟙 (𝟙_ Ab.{u + 1})) = 0 := by
    apply (cancel_mono e.hom).mp
    rw [zero_comp]
    calc
      _ = e.hom ≫ (N • 𝟙 (Mod.regular R)) := by
        rw [Functor.map_nsmul, CategoryTheory.Functor.map_id,
          Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp, Category.comp_id]
      _ = 0 := by rw [hN, comp_zero]
  exact CokernelCofork.IsColimit.isIso_π (c.map F)
    (c.mapIsColimit (AddCommGrpCat.intResidueCokernel N) F) hf

private noncomputable def freeConstantResidueUnitIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (N : ℕ) (hN : N • 𝟙 (Mod.regular R) = 0) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      Mod.freeFunctor R).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅
        Mod.regular R := by
  have := freeConstantResidue_isIso X R N hN
  exact (asIso ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    Mod.freeFunctor R).map (AddCommGrpCat.intResidue N))).symm ≪≫
    freeConstantUnitIso X R

private theorem continuousCoefficient_nsmul_id_zero
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (N : ℕ) (hN : (N : A) = 0) :
    N • 𝟙 (Profinite.continuousCoefficientRingObj A) = 0 := by
  apply (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  ext S a
  apply ULift.ext
  ext s
  change N • a.down s = 0
  rw [nsmul_eq_mul, hN, zero_mul]

private theorem coefficientRegular_nsmul_id_zero (X : Scheme.{u})
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (N : ℕ) (hN : (N : A) = 0) :
    N • 𝟙 (Mod.regular (condensedRingObj
      (Profinite.continuousCoefficientRingObj A) X)) = 0 := by
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
      AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
    dsimp [pointUpperStar, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  apply (Mod.forget _).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  dsimp only [Mod.forget, Mod.regular, condensedRingObj]
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
    congrArg (upperStarFromPoint X).map (continuousCoefficient_nsmul_id_zero A N hN)

private theorem finiteLocalBasis_from_rootDiagram (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hRoots : ∀ i : 𝒰.I₀, Nonempty
      (tateRootsSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i) ≅
        constantTateResidueSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i)))
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (r : ℕ) (hr : (ℓ : A) ^ (r + 1) = 0) :
    ∀ i : 𝒰.I₀, Nonempty
      (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
        (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)).obj
          ((Mod.freeFunctor (condensedRingObj
            (Profinite.continuousCoefficientRingObj A) X)).obj
              (rootsOfUnitySheaf X (ℓ ^ (r + 1)))) ≅ 𝟙_ _) := by
  intro i
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj A) X
  let F := upperStar Ab.{u + 1} (𝒰.f i)
  let Φ := F.mapMod R
  let Q := Mod.freeFunctor (F.obj R)
  let c := (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))))
  let : F.Braided := CondensedRing.braided_sheafUpperStar _
  have hz : ((ℓ ^ (r + 1) : ℕ) : A) = 0 := by simpa only [Nat.cast_pow] using hr
  have hR := coefficientRegular_nsmul_id_zero X A (ℓ ^ (r + 1)) hz
  let e := (hRoots i).some.app (op (r + 1))
  exact ⟨(freePullIso (𝒰.f i) R).app _ ≪≫ Q.mapIso e ≪≫
    ((freePullIso (𝒰.f i) R).app c).symm ≪≫
    Φ.mapIso (freeConstantResidueUnitIso X R (ℓ ^ (r + 1)) hR) ≪≫
    F.mapModUnitIso.symm⟩

end AlgebraicGeometry.ProEtale

end

section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private noncomputable def integerResidueCone (ℓ : ℕ) :
    (Functor.const ℕᵒᵖ).obj (𝟙_ Ab.{u + 1}) ⟶
      Functor.ofOpSequence
        (X := fun n ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
        (integralResidueAbTransition.{u} ℓ) :=
  NatTrans.ofOpSequence (fun n ↦ AddCommGrpCat.intResidue (ℓ ^ n)) (fun n ↦ by
    simp only [Functor.const_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
    exact (intResidue_transition ℓ n).symm)

private theorem mappedResidueTransition_isIso
    {C : Type v} [Category.{w} C] (F : Ab.{u + 1} ⥤ C) (ℓ : ℕ)
    (a b : ℕ) (hab : a ≤ b)
    [IsIso (F.map (AddCommGrpCat.intResidue (ℓ ^ a)))]
    [IsIso (F.map (AddCommGrpCat.intResidue (ℓ ^ b)))] :
    IsIso (F.map ((Functor.ofOpSequence
      (X := fun n ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
      (integralResidueAbTransition.{u} ℓ)).map (homOfLE hab).op)) := by
  let p := AddCommGrpCat.intResidue.{u} (ℓ ^ b)
  let q := AddCommGrpCat.intResidue.{u} (ℓ ^ a)
  let g := (Functor.ofOpSequence
    (X := fun n ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
    (integralResidueAbTransition.{u} ℓ)).map (homOfLE hab).op
  have hn := (integerResidueCone ℓ).naturality (homOfLE hab).op
  change 𝟙 _ ≫ q = p ≫ g at hn
  have h : p ≫ g = q := by
    simpa only [Category.id_comp] using hn.symm
  have hm : F.map p ≫ F.map g = F.map q :=
    (F.map_comp p g).symm.trans (congrArg F.map h)
  have he : F.map g = inv (F.map p) ≫ F.map q := by
    calc
      _ = inv (F.map p) ≫ (F.map p ≫ F.map g) := by simp
      _ = _ := congrArg (fun t ↦ inv (F.map p) ≫ t) hm
  rw [he]
  infer_instance

end AlgebraicGeometry.ProEtale

end

section

open CategoryTheory Opposite
namespace CommRingCat

private theorem rootsFunctor_eqToHom_val {a b : ℕ} (h : a = b)
    (R : CommRingCat.{u}) (x : (rootsOfUnityFunctor a).obj R) :
    (((eqToHom (congrArg rootsOfUnityFunctor h)).app R x).down.toMul : Rˣ).val =
      (x.down.toMul : Rˣ).val := by
  subst h
  rfl

private noncomputable def rawRootPower (ℓ n k : ℕ) :
    rootsOfUnityFunctor.{u} (ℓ ^ (n + k)) ⟶ rootsOfUnityFunctor.{u} (ℓ ^ n) :=
  eqToHom (congrArg rootsOfUnityFunctor (by rw [Nat.add_comm n k, pow_add])) ≫
    rootsOfUnityPow (ℓ ^ n) (ℓ ^ k)

private theorem rawRootPower_val (ℓ n k : ℕ) (R : CommRingCat.{u})
    (x : (rootsOfUnityFunctor (ℓ ^ (n + k))).obj R) :
    (((rawRootPower ℓ n k).app R x).down.toMul : Rˣ).val =
      (x.down.toMul : Rˣ).val ^ (ℓ ^ k) := by
  change (((eqToHom (congrArg rootsOfUnityFunctor
    (by rw [Nat.add_comm n k, pow_add]))).app R x).down.toMul : Rˣ).val ^ (ℓ ^ k) = _
  rw [rootsFunctor_eqToHom_val]
  all_goals rw [Nat.add_comm n k, pow_add]

private theorem rawRootPower_zero (ℓ n : ℕ) :
    rawRootPower.{u} ℓ n 0 = 𝟙 _ := by
  ext R x
  apply ULift.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (((rawRootPower ℓ n 0).app R x).down.toMul : Rˣ).val = _
  rw [rawRootPower_val, pow_zero, pow_one]
  rfl

private theorem rawRootPower_comp (ℓ n k : ℕ) :
    rawRootPower.{u} ℓ (n + k) 1 ≫ rawRootPower ℓ n k =
      rawRootPower ℓ n (k + 1) := by
  ext R x
  apply ULift.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (((rawRootPower ℓ n k).app R
    ((rawRootPower ℓ (n + k) 1).app R x)).down.toMul : Rˣ).val =
      (((rawRootPower ℓ n (k + 1)).app R x).down.toMul : Rˣ).val
  calc
    _ = ((x.down.toMul : Rˣ).val ^ (ℓ ^ 1)) ^ (ℓ ^ k) := by
      rw [rawRootPower_val, rawRootPower_val]
    _ = (x.down.toMul : Rˣ).val ^ (ℓ ^ (k + 1)) := by
      rw [pow_one, ← pow_mul, ← pow_succ']
    _ = _ := (rawRootPower_val ℓ n (k + 1) R x).symm

private theorem rawRootSequence_map (ℓ n k : ℕ) :
    (Functor.ofOpSequence
      (X := fun n ↦ rootsOfUnityFunctor.{u} (ℓ ^ n))
      (fun n ↦ rawRootPower ℓ n 1)).map
        (homOfLE (show n ≤ n + k by omega)).op = rawRootPower ℓ n k := by
  induction k with
  | zero =>
    calc
      _ = 𝟙 (rootsOfUnityFunctor (ℓ ^ n)) :=
        (Functor.ofOpSequence
          (X := fun n ↦ rootsOfUnityFunctor.{u} (ℓ ^ n))
          (fun n ↦ rawRootPower ℓ n 1)).map_id (op n)
      _ = _ := (rawRootPower_zero ℓ n).symm
  | succ k ih =>
    have ht : (homOfLE (show n ≤ n + (k + 1) by omega)).op =
        (homOfLE (Nat.le_add_right (n + k) 1)).op ≫
          (homOfLE (show n ≤ n + k by omega)).op := Subsingleton.elim _ _
    rw [ht, Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ, ih,
      rawRootPower_comp]

end CommRingCat

namespace AlgebraicGeometry.ProEtale

private theorem rootsPower_whiskerCast {X : Scheme.{u}} {a b : ℕ} (h : a = b) :
    Functor.whiskerLeft ((Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (eqToHom (congrArg CommRingCat.rootsOfUnityFunctor h)) =
      eqToHom (congrArg (rootsOfUnityPresheaf X) h) := by
  subst h
  rfl

private noncomputable def rootSheafification (X : Scheme.{u}) :
    (CommRingCat.{u} ⥤ Ab.{u + 1}) ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} where
  obj F := (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
    (((Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ) ⋙ F)
  map t := (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
    (Functor.whiskerLeft ((Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ) t)
  map_id F := by
    change (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map (𝟙 _) = _
    exact (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map_id _
  map_comp f g := by
    rw [Functor.whiskerLeft_comp, Functor.map_comp]

private theorem rootSheafification_rawRootPower (X : Scheme.{u}) (ℓ n k : ℕ) :
    (rootSheafification X).map (CommRingCat.rawRootPower ℓ n k) =
      eqToHom (congrArg (rootsOfUnitySheaf X)
        (by rw [Nat.add_comm n k, pow_add])) ≫
          rootsOfUnitySheafPow X (ℓ ^ n) (ℓ ^ k) := by
  change (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
    (Functor.whiskerLeft ((Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rawRootPower ℓ n k)) = _
  rw [CommRingCat.rawRootPower, Functor.whiskerLeft_comp, Functor.map_comp,
    rootsPower_whiskerCast, eqToHom_map]
  · rfl
  · rw [Nat.add_comm n k, pow_add]

private theorem rootsSheafPower_cast_congr (X : Scheme.{u})
    {a n m m' : ℕ} (h : m = m') (ha : a = m * n) (ha' : a = m' * n) :
    eqToHom (congrArg (rootsOfUnitySheaf X) ha) ≫ rootsOfUnitySheafPow X n m =
      eqToHom (congrArg (rootsOfUnitySheaf X) ha') ≫ rootsOfUnitySheafPow X n m' := by
  cases h
  rfl

private noncomputable def rawRootSheafSequenceMap (X : Scheme.{u}) (ℓ : ℕ) :
    Functor.ofOpSequence
      (X := fun n ↦ CommRingCat.rootsOfUnityFunctor.{u} (ℓ ^ n))
      (fun n ↦ CommRingCat.rawRootPower ℓ n 1) ⋙ rootSheafification X ⟶
        tateRootsSystem X ℓ :=
  NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
    simp only [Functor.comp_map, tateRootsSystem,
      Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp, Category.comp_id]
    rw [rootSheafification_rawRootPower]
    change (eqToHom (congrArg (rootsOfUnitySheaf X)
      (by rw [Nat.add_comm n 1, pow_add])) ≫
        rootsOfUnitySheafPow X (ℓ ^ n) (ℓ ^ 1)) =
      (eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ℓ ^ n) ℓ)
    exact rootsSheafPower_cast_congr X (a := ℓ ^ (n + 1)) (n := ℓ ^ n)
      (pow_one ℓ) (by rw [pow_one, pow_succ']) (by rw [pow_succ']))

private theorem tateRootsSystem_map_power (X : Scheme.{u}) (ℓ n k : ℕ) :
    (tateRootsSystem X ℓ).map (homOfLE (show n ≤ n + k by omega)).op =
      eqToHom (congrArg (rootsOfUnitySheaf X)
        (by rw [Nat.add_comm n k, pow_add])) ≫
          rootsOfUnitySheafPow X (ℓ ^ n) (ℓ ^ k) := by
  have hn := (rawRootSheafSequenceMap X ℓ).naturality
    (homOfLE (show n ≤ n + k by omega)).op
  simp only [rawRootSheafSequenceMap, NatTrans.ofOpSequence_app,
    Category.id_comp, Category.comp_id, Functor.comp_map] at hn
  rw [CommRingCat.rawRootSequence_map, rootSheafification_rawRootPower] at hn
  exact hn.symm

end AlgebraicGeometry.ProEtale

end

section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem rootSystemMap_isIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hRoots : ∀ i : 𝒰.I₀, Nonempty
      (tateRootsSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i) ≅
        constantTateResidueSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i)))
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (r k : ℕ) (hr : (ℓ : A) ^ (r + 1) = 0) :
    IsIso ((Mod.freeFunctor (condensedRingObj
      (Profinite.continuousCoefficientRingObj A) X)).map
        ((tateRootsSystem X ℓ).map
          (homOfLE (show r + 1 ≤ r + k + 1 by omega)).op)) := by
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj A) X
  let P := Mod.freeFunctor R
  let g := (homOfLE (show r + 1 ≤ r + k + 1 by omega)).op
  have ha : ((ℓ ^ (r + 1) : ℕ) : A) = 0 := by
    simpa only [Nat.cast_pow] using hr
  have hb : ((ℓ ^ (r + k + 1) : ℕ) : A) = 0 := by
    rw [Nat.cast_pow, show r + k + 1 = (r + 1) + k by omega, pow_add, hr, zero_mul]
  have hRa := coefficientRegular_nsmul_id_zero X A (ℓ ^ (r + 1)) ha
  have hRb := coefficientRegular_nsmul_id_zero X A (ℓ ^ (r + k + 1)) hb
  have hres : IsIso ((constantTateResidueSystem X ℓ ⋙ P).map g) := by
    let H := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ P
    have : IsIso (H.map (AddCommGrpCat.intResidue (ℓ ^ (r + 1)))) :=
      freeConstantResidue_isIso X R (ℓ ^ (r + 1)) hRa
    have : IsIso (H.map (AddCommGrpCat.intResidue (ℓ ^ (r + k + 1)))) :=
      freeConstantResidue_isIso X R (ℓ ^ (r + k + 1)) hRb
    exact mappedResidueTransition_isIso H ℓ (r + 1) (r + k + 1) (by omega)
  let f := P.map ((tateRootsSystem X ℓ).map g)
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have hlocal (i : 𝒰.I₀) :
      IsIso (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).map f) := by
    let F := upperStar Ab.{u + 1} (𝒰.f i)
    let Φ := F.mapMod R
    let Q := Mod.freeFunctor (F.obj R)
    let e := freePullIso (𝒰.f i) R
    obtain ⟨eRoots⟩ := hRoots i
    let eTower : (tateRootsSystem X ℓ ⋙ P) ⋙ Φ ≅
        (constantTateResidueSystem X ℓ ⋙ P) ⋙ Φ :=
      Functor.associator (tateRootsSystem X ℓ) P Φ ≪≫
      Functor.isoWhiskerLeft (tateRootsSystem X ℓ) e ≪≫
      (Functor.associator (tateRootsSystem X ℓ) F Q).symm ≪≫
      Functor.isoWhiskerRight eRoots Q ≪≫
      Functor.associator (constantTateResidueSystem X ℓ) F Q ≪≫
      Functor.isoWhiskerLeft (constantTateResidueSystem X ℓ) e.symm ≪≫
      (Functor.associator (constantTateResidueSystem X ℓ) P Φ).symm
    have : IsIso (((constantTateResidueSystem X ℓ ⋙ P) ⋙ Φ).map g) := by
      change IsIso (Φ.map ((constantTateResidueSystem X ℓ ⋙ P).map g))
      infer_instance
    exact (NatIso.isIso_map_iff eTower g).2 this
  suffices IsIso ((Mod.forget R).map f) from isIso_of_reflects_iso f (Mod.forget R)
  refine isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom 𝒰.f 𝒰.mem₀ ?_
  intro i
  have := hlocal i
  have : IsIso ((upperStar Ab.{u + 1} (𝒰.f i)).map f.hom) :=
    inferInstanceAs (IsIso ((Mod.forget _).map
      (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).map f)))
  exact (NatIso.isIso_map_iff
    (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) _).1 this

end AlgebraicGeometry.ProEtale

end

section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem tateRootsSystem_map_power_of_eq (X : Scheme.{u}) (ℓ m n k : ℕ)
    (hm : m = n + k) (h : n ≤ m) :
    (tateRootsSystem X ℓ).map (CategoryTheory.homOfLE h).op =
      eqToHom (congrArg (rootsOfUnitySheaf X)
        (by rw [hm, Nat.add_comm n k, pow_add])) ≫
          rootsOfUnitySheafPow X (ℓ ^ n) (ℓ ^ k) := by
  subst m
  exact tateRootsSystem_map_power X ℓ n k

/-- The pulled-back discrete finite coefficient ring.
Source: clause (2) (blueprint: lem-sp-condensed-finite-root-basis). -/
abbrev finiteRootCoefficient (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  let : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  condensedRingObj (Profinite.continuousCoefficientRingObj A) X

/-- The balanced finite coefficient root line, written as a free internal module.
Source: clause (2) (blueprint: lem-sp-condensed-finite-root-basis). -/
def finiteRootLine (X : Scheme.{u}) (ℓ : ℕ) (A : Type u) [CommRing A] (r : ℕ) :=
  (Mod.freeFunctor (finiteRootCoefficient X A)).obj (rootsOfUnitySheaf X (ℓ ^ (r + 1)))

/-- The canonical Kummer power map after extension to A coefficients.
Source: clause (2) (blueprint: lem-sp-condensed-finite-root-basis). -/
def finiteRootComparison (X : Scheme.{u}) (ℓ : ℕ) (A : Type u) [CommRing A]
    (r k : ℕ) : finiteRootLine X ℓ A (r + k) ⟶ finiteRootLine X ℓ A r :=
  (Mod.freeFunctor (finiteRootCoefficient X A)).map
    (eqToHom (by rw [show r + k + 1 = k + (r + 1) by omega, pow_add]) ≫
      rootsOfUnitySheafPow X (ℓ ^ (r + 1)) (ℓ ^ k))

/-- Kummer power maps are coefficient-independent isomorphisms and give local A-bases.

Source: current blueprint sk-def-sp-tate-twist-locally-free.proof, paragraphs (1)--(2).
Proof: commute inverse image with the free-module functor by uniqueness of the
free-module left adjoint. Apply this to the supplied abelian diagram basis. The
free A-module on the constant Z/l^(r+1) is the regular A-module when l^(r+1)
annihilates A: apply free modules to the cokernel of multiplication by l^(r+1)
on the constant integer sheaf. Equivalently, tensor locally with Z/l^(r+1),
using integer representatives; the annihilator makes their choice irrelevant.
This yields a basis sending 1 to the primitive root tensored with 1. Naturality
of the root-diagram basis makes the Kummer map the identity between these
regular A-modules, for every larger exponent. Covering inverse images jointly
reflect isomorphisms, hence the specified Kummer map is an isomorphism globally.
The construction includes the zero coefficient ring and an empty covering.
(blueprint: lem-sp-condensed-finite-root-basis) -/
theorem condensedFiniteRoot_basis (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hRoots : ∀ i : 𝒰.I₀, Nonempty
      (tateRootsSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i) ≅
        constantTateResidueSystem X ℓ ⋙ upperStar Ab.{u + 1} (𝒰.f i)))
    (A : Type u) [CommRing A] [Finite A] (r : ℕ) (hr : (ℓ : A) ^ (r + 1) = 0) :
    (∀ k : ℕ, IsIso (finiteRootComparison X ℓ A r k)) ∧
    ∀ i : 𝒰.I₀, Nonempty
      (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod (finiteRootCoefficient X A)).obj
        (finiteRootLine X ℓ A r) ≅ 𝟙_ _) := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  refine ⟨?_, finiteLocalBasis_from_rootDiagram X ℓ 𝒰 hRoots A r hr⟩
  intro k
  have h := rootSystemMap_isIso X ℓ 𝒰 hRoots A r k hr
  rw [tateRootsSystem_map_power_of_eq X ℓ (r + k + 1) (r + 1) k
    (by omega) (by omega)] at h
  exact h

end AlgebraicGeometry.ProEtale

end
