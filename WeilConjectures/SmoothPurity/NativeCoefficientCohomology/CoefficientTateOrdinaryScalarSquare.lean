/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientTatePowerScalar

/-! # The scalar square in a normalized completed root basis -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeCoefficientCohomology
open FrobeniusCoefficientTwists

/-- A completed basis with constant finite root coordinates turns the generator
scalar law into an equality of ordinary completed-module morphisms.

Source: Weil I (2.2), coefficient normalization, before passage to derived categories.
(blueprint: lem-sf-coefficient-tate-ordinary-scalar-square).

Proof: transpose the two morphisms by the module inverse-image adjunction.
Naturality of its unit expresses the pulled-back basis on a scalar section as
insertion of that section's basis vector. The prescribed basis formula identifies
this vector with the ordered pure root tensor. Apply the frame power scalar law,
using constant coordinate one in every factor. The exponent-zero comparison
sends a scalar section to its coefficient pullback. The target basis formula
therefore identifies the result with the other transposed morphism. Equality on
all sections gives equality of morphisms, and the adjunction is injective. -/
theorem coefficient_tate_ordinary_scalar_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (g : S ⟶ S) [IsIso g]
    (q : ℕ) (A : CoefficientTateRootFrames S l q g)
    (hpower : CoefficientTateFramePowerScalarLaw l E g q A)
    (d : ℕ)
    (z : ∀ U : S.ProEtᵒᵖ, (purTwistZlOne S l).obj.obj U)
    (hz : ∀ U n,
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
          (z U) =
        (A.basis (n + 1)).hom.hom.app U
          (coefficientRootSection S (l ^ (n + 1)) U 1))
    (b : positiveLine l E S 0 ≅ positiveLine l E S d)
    (hb : ∀ U (a : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U),
      b.hom.val.app U a = generator l E S U a d (fun _ ↦ z U)) :
    q ^ d • ((modulePull l E g).map b.hom ≫ (positiveLineMaps l E g d).hom) =
      (positiveLineMaps l E g 0).hom ≫ b.hom := by
  let adj := proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring S)
    ((PurCompactSupport.completed l E).ring S)
    ((PurCompactSupport.completed l E).pull g)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_nsmul, Functor.map_comp, Preadditive.comp_nsmul]
  have hn := adj.unit.naturality b.hom
  change b.hom ≫ adj.unit.app _ = adj.unit.app _ ≫
    (proEtaleRingModuleDirectImage g
      ((PurCompactSupport.completed l E).ring S)
      ((PurCompactSupport.completed l E).ring S)
      ((PurCompactSupport.completed l E).pull g)).map
        ((modulePull l E g).map b.hom) at hn
  erw [← Category.assoc, ← hn, Category.assoc]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro a
  have heval (N : integralTowerModules l E S)
      (f : positiveLine l E S 0 ⟶ N) (n : ℕ) :
      (n • f).val.app U a = n • f.val.app U a := by
    let ev := SheafOfModules.forget
      (completedIntegralCoefficientSheafUnrestricted l E S) ⋙
      PresheafOfModules.evaluation _ U
    change (ev.map (n • f)) a = _
    rw [Functor.map_nsmul]
    rfl
  rw [heval]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change q ^ d • ((positiveLineMaps l E g d).hom.val.app
      (op ((proEtaleBaseChange g).obj U.unop))
        (moduleSection l E g (positiveLine l E S d) U.unop (b.hom.val.app U a))) =
    b.hom.val.app (op ((proEtaleBaseChange g).obj U.unop))
      ((positiveLineMaps l E g 0).hom.val.app
        (op ((proEtaleBaseChange g).obj U.unop))
        (moduleSection l E g (positiveLine l E S 0) U.unop a))
  rw [hb]
  have h := hpower d U.unop a (fun _ ↦ z U)
    (fun _ ↦ z (op ((proEtaleBaseChange g).obj U.unop))) (fun _ _ ↦ 1)
    (fun _ n ↦ hz U n) (fun _ n ↦ hz _ n)
  rw [h, hb]
  have hzero := (existsUnique_positiveLineMaps l E g).exists.choose_spec 0 U.unop a
    (fun i ↦ Fin.elim0 i)
  change (positiveLineMaps l E g 0).hom.val.app _
    (moduleSection l E g (positiveLine l E S 0) U.unop a) =
      (sfCompletedCoefficientMap l E g).hom.app U a at hzero
  rw [hzero]

end WeilConjectures.NativeCoefficientCohomology
