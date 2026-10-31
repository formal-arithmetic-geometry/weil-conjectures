/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedHomShiftEvaluationModel
import all WeilConjectures.Algebra.Homology.RingedHomShiftEvaluationModel

/-! # Unsigned target shifts commute with ordinary chain uncurrying

Source: Stacks 0A8X. This chain-level calculation uses no derived evaluation equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace CategoryTheory.RingedHomShift

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- The unsigned total-tensor first-factor reindexing, with its coefficient instances explicit.
Source: Stacks 0A8X (blueprint: lem-sf-ringed-hom-shift-uncurry). -/
def shift₁ (A P : RingedHomUniverses.Complex.{c, v, u} J R) (n : ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj (A⟦n⟧, P) ≅
      ((coefficientTotalTensor.{u, c, v} J R).obj (A, P))⟦n⟧ :=
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  CochainComplex.mapBifunctorShift₁Iso A P (MonoidalCategory.curriedTensor _) n

/-- Step 5: ordinary evaluation commutes with the unsigned first-factor tensor shift.
Source: Stacks 0A8X
(blueprint: lem-sf-ringed-hom-shift-uncurry).

Proof: in degree k, precompose with each total-coproduct inclusion for p+q=k and then
with the presheaf pure-tensor map before sheafification. RightFormula says that u sends
the (q,p+n+q) Hom projection to that same projection with no coefficient. The formula
for shift₁ also reindexes without a coefficient. Thus both sides send x tensor y to
(a^(p+n)(x))^q(y). The universal properties of sheafification, tensor products and the
total coproduct prove equality of each component and hence equality of chain maps.
No global generation claim for sheaf sections and no tensor/product interchange is used. -/
theorem uncurry_shift
    (A P I : RingedHomUniverses.Complex.{c, v, u} J R) (n : ℤ)
    (u : (RingedHomUniverses.complexHom.{c, v, u} J R P I)⟦n⟧ ≅
      RingedHomUniverses.complexHom.{c, v, u} J R P (I⟦n⟧))
    (hu : RingedHomUniverses.RightFormula.{c, v, u} J R P I n u)
    (a : A ⟶ RingedHomUniverses.complexHom.{c, v, u} J R P I)
    (ψ : (coefficientTotalTensor.{u, c, v} J R).obj (A, P) ⟶ I)
    (ψn : (coefficientTotalTensor.{u, c, v} J R).obj (A⟦n⟧, P) ⟶ I⟦n⟧)
    (hψ : Uncurries.{c, v, u} J R A P I a ψ)
    (hψn : Uncurries.{c, v, u} J R (A⟦n⟧) P (I⟦n⟧) (a⟦n⟧' ≫ u.hom) ψn) :
    ψn = (shift₁.{c, v, u} J R A P n).hom ≫ ψ⟦n⟧' := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  apply total_hom_ext.{c, v, u} J R (A⟦n⟧) P (I⟦n⟧)
  intro p q k hpq U x y
  have hπ := hu p q k (by omega)
  have haπ : (a⟦n⟧' ≫ u.hom).f p ≫
      coefficientHomComponent.{u, c, v} J R P (I⟦n⟧) p q k (by omega) =
      a.f (p + n) ≫ coefficientHomComponent.{u, c, v} J R P I
        (p + n) q (k + n) (by omega) := by
    rw [HomologicalComplex.comp_f, Category.assoc]
    exact congrArg (fun f ↦ a.f (p + n) ≫ f) hπ
  have hs := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f A P
    (MonoidalCategory.curriedTensor _) n p q k hpq (p + n) (k + n) rfl rfl
  have hs' : HomologicalComplex.ιMapBifunctor (A⟦n⟧) P
      (MonoidalCategory.curriedTensor _) (.up ℤ) p q k hpq ≫
        (shift₁.{c, v, u} J R A P n).hom.f k =
      HomologicalComplex.ιMapBifunctor A P
        (MonoidalCategory.curriedTensor _) (.up ℤ) (p + n) q (k + n)
          (by change p + n + q = k + n; omega) := by
    have hid : ((MonoidalCategory.curriedTensor (RingedHomUniverses.Modules.{c, v, u} J R)).map
        (𝟙 (A.X (p + n)))).app (P.X q) = 𝟙 _ :=
      NatTrans.congr_app ((MonoidalCategory.curriedTensor _).map_id _) _
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Iso.refl_inv, hid, Category.comp_id] at hs
    exact hs
  rw [hψn p q k hpq (by omega) U x y]
  calc
    _ = ((((coefficientHomComponent.{u, c, v} J R P I (p + n) q (k + n)
        (by omega)).val.app U) ((a.f (p + n)).val.app U x)).app
        (op (Over.mk (𝟙 U.unop)))).hom y := by
      exact congrArg (fun f ↦ ((f.val.app U x).app
        (op (Over.mk (𝟙 U.unop)))).hom y) haπ
    _ = (ψ.f (k + n)).val.app U
        (coefficientTensorGenerator.{u, c, v} J R A P (p + n) q (k + n)
          (by omega) U x y) :=
      (hψ (p + n) q (k + n) (by omega) (by omega) U x y).symm
    _ = (((shift₁.{c, v, u} J R A P n).hom ≫ ψ⟦n⟧').f k).val.app U
        (coefficientTensorGenerator.{u, c, v} J R (A⟦n⟧) P p q k hpq U x y) := by
      have ht := congrArg (fun f ↦ (f ≫ ψ.f (k + n)).val.app U
        (pure.{c, v, u} J R (A.X (p + n)) (P.X q) U x y)) hs'
      exact ht.symm

end CategoryTheory.RingedHomShift
