/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sp.SpEllCoefficientTower

import WeilConjectures.AlgebraicGeometry.Sp.SpRootBasisLevel

/-! # Compatible finite-level bases on one prescribed slice -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.ProEtale

/-- The prescribed compatible root generators identify the finite-level integral
Tate tower with the coefficient quotient tower on the same slice. -/
theorem spRootBasisTowerComparison
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n))
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty (spIntegralTwistSystem X ℓ E ⋙ spRootBasisSliceSections X
        (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W ≅
      spEllCoefficientSystem X ℓ E ⋙ spRootBasisSliceSections X
        (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W) := by
  classical
  let R := condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
  let S := spRootBasisSliceSections X R W
  let C := spEllCoefficientSystem X ℓ E ⋙ S
  let T := spIntegralTwistSystem X ℓ E ⋙ S
  choose i hi using fun n ↦ spRootBasisLevel X ℓ W n (ζ n) (e n) (he n) E
  let t : C ⟶ T := NatTrans.ofOpSequence (F := C) (G := T) (fun n ↦ (i n).hom) (by
    intro n
    dsimp only [C, T]
    simp only [Functor.comp_map, spEllCoefficientSystem, spIntegralTwistSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (i n).hom.val.app V
        ((coefficientMap.{u} (spEllPointTransition ℓ E n) X).hom.app
          (op V.unop.left) b) =
      (spIntegralLevelTransition X ℓ E n).hom.hom.app (op V.unop.left)
        ((i (n + 1)).hom.val.app V b)
    rw [hi n, hi (n + 1)]
    have ht := (spIntegralLevelTransition_existsUnique X ℓ E n).exists.choose_spec
    change (spIntegralLevelTransition X ℓ E n).hom = _ at ht
    rw [ht]
    let B₁ := condensedRingObj.{u} (spEllPointRingObj ℓ E (n + 1)) X
    let B₀ := condensedRingObj.{u} (spEllPointRingObj ℓ E n) X
    let M₁ := Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 2))
    let M₀ := Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))
    let r : B₁ ⟶ B₀ := coefficientMap.{u} (spEllPointTransition ℓ E n) X
    let q : M₁ ⟶ M₀ := Scheme.proEtaleRootsOfUnityTransition X
      (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
    have hq := NatTrans.naturality_apply q.hom V.unop.hom.op (ζ (n + 1))
    change q.hom.app (op V.unop.left)
        ((Scheme.purTwistRootsModule X ℓ (n + 1)).val.map V.unop.hom.op (ζ (n + 1))) =
      (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op
        (q.hom.app (op W) (ζ (n + 1))) at hq
    rw [hζ n] at hq
    have hμ := Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) r q
    have hh := congrArg (fun f ↦ f.app (op V.unop.left)
      (b ⊗ₜ[ℤ] (Scheme.purTwistRootsModule X ℓ (n + 1)).val.map
        V.unop.hom.op (ζ (n + 1)))) hμ
    change _ = (r ⊗ₘ q).hom.app (op V.unop.left) _
    change (Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) B₀ M₀).app
        (op V.unop.left)
        (r.hom.app (op V.unop.left) b ⊗ₜ[ℤ]
          q.hom.app (op V.unop.left)
            ((Scheme.purTwistRootsModule X ℓ (n + 1)).val.map
              V.unop.hom.op (ζ (n + 1)))) = _ at hh
    rw [hq] at hh
    exact hh)
  have (n : ℕᵒᵖ) : IsIso (t.app n) := by
    change IsIso (i n.unop).hom
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨(asIso t).symm⟩

end AlgebraicGeometry.ProEtale
