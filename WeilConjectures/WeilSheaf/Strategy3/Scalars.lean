/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.Coefficient

/-! # Independent coefficient/pullback infrastructure: Scalars -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

omit [DiscreteTopology T] [Finite T] in
/-- **The comparison `T_X ⟶ Λ_X` on constant global sections**: it sends the constant global
section `t` of the constant ring sheaf `T_X` to the image under `p_X^*` of the constant global
section `t` of the condensed ring `T̲ = C(-, T)`. -/
lemma constRingSheafSection_comp_constRingSheafToCondensedRingObj (t : T) :
    Sheaf.constRingSheafSection (Scheme.ProEt.topology X) (ULift.up t : coeffType.{u} T) ≫
        constRingSheafToCondensedRingObj X T =
      ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom := by
  let tab := AddCommGrpCat.unitHom (M := AddCommGrpCat.of (coeffType.{u} T)) (ULift.up t)
  let π := (toSpecZ X)^*[Ab.{u + 1}]
  let cS := constantSheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1}
  let cP := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  have h₁ := NatTrans.IsMonoidal.ε_comp_map_comp_app (constantSheafToUpperStarToSpecZ X) tab
  have h₂ := NatTrans.IsMonoidal.ε_comp_map_comp_app constantSheafToPointUpperStar.{u} tab
  have h₃ := Profinite.constRingSheafSection_comp_constRingSheafToContinuousMapRingObj.{u} T t
  have e₁ : ε (cS ⋙ π) = ε π ≫ π.map (ε cS) := rfl
  have e₂ : ε (cP ⋙ pointUpperStar.{u}) = ε pointUpperStar.{u} ≫ pointUpperStar.map (ε cP) := rfl
  have e₃ : ε (upperStarFromPoint X) = ε π ≫ π.map (ε pointUpperStar.{u}) := rfl
  rw [Sheaf.constRingSheafSection, constRingSheafToCondensedRingObj, Category.assoc,
    reassoc_of% h₁, e₁, e₃]
  simp only [Category.assoc]
  refine congrArg (fun g ↦ ε π ≫ g) ?_
  change π.map (ε cS) ≫ π.map (cS.map tab) ≫ π.map (constantSheafToPointUpperStar.app _) ≫
      π.map (pointUpperStar.map (Profinite.constRingSheafToContinuousMapRingObj T)) =
    π.map (ε pointUpperStar.{u}) ≫
      π.map (pointUpperStar.map (Profinite.continuousMapConstRingHom.{u} T t).hom)
  rw [← π.map_comp, ← π.map_comp, ← π.map_comp, ← π.map_comp, reassoc_of% h₂, e₂, Category.assoc,
    ← pointUpperStar.map_comp, ← pointUpperStar.map_comp, ← Category.assoc (ε cP), ← h₃]
  rfl

/-- **The scalars of `finiteCoefficientModEquivalence`**: for a module object `M` over
`Λ_X = p_X^* T̲`, the action of `t ∈ T` on the sections of the sheaf of `T`-modules
corresponding to `M` is the action on `M` of the constant global section `t` of `Λ_X`. -/
lemma finiteCoefficientModEquivalence_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coeffRing T) X))
    (U : X.ProEtᵒᵖ) (t : T) (y : ((finiteCoefficientModEquivalence X T).functor.obj M).obj.obj U) :
    (ULift.up t : coeffType.{u} T) • y =
      (Mod.globalSmul (ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom.{u} T t).hom) M).hom.app
          U y := by
  refine (Sheaf.modSmul_modToPresheafMod
    ((Mod.comap (constRingSheafToCondensedRingObj X T)).obj M) U _ y).trans ?_
  rw [Mod.globalSmul_comap, constRingSheafSection_comp_constRingSheafToCondensedRingObj]
  rfl


end AlgebraicGeometry.ProEtale.Strategy3
