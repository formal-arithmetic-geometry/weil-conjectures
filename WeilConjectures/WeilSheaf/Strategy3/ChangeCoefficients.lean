/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.Pullback
public import WeilConjectures.WeilSheaf.SmoothPurityFreeCoefficientPull

/-! # Independent coefficient/pullback infrastructure: ChangeCoefficients -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme


section CoefficientMap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [MonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The coefficient change `a_X = p_X^* a : Λ_X ⟶ Λ'_X` on `X_proét` induced by a morphism
`a : Λ ⟶ Λ'` of condensed rings. It is a morphism of ring objects, `p_X^*` being monoidal. -/
noncomputable abbrev coefficientMap (X : Scheme.{u}) :
    condensedRingObj Λ X ⟶ condensedRingObj Λ' X :=
  (upperStarFromPoint X).map a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_id (X : Scheme.{u}) : coefficientMap (𝟙 Λ) X = 𝟙 _ :=
  (upperStarFromPoint X).map_id Λ

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_comp {Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    coefficientMap (a ≫ b) X = coefficientMap a X ≫ coefficientMap b X :=
  (upperStarFromPoint X).map_comp a b

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `α_f : f^* Λ_Y ⟶ Λ_X` are natural in the condensed ring:
`f^* a_Y ≫ α_f = α_f ≫ a_X`. This is the naturality in `Λ` of the comparison
`f^* ∘ p_Y^* ≅ p_X^*`. -/
@[reassoc]
lemma map_coefficientMap_comp_condensedPullbackHom :
    (f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ condensedPullbackHom Λ' f =
      condensedPullbackHom Λ f ≫ coefficientMap a X :=
  (upperStarFromPointComp f).hom.naturality a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `η_f : Λ_Y ⟶ f_* Λ_X` are natural in the condensed ring:
`η_f ≫ f_* a_X = a_Y ≫ η_f`. This follows from the naturality of `α_f` and of the unit of
`f^* ⊣ f_*`. -/
@[reassoc]
lemma condensedPushforwardHom_comp_map_coefficientMap :
    condensedPushforwardHom Λ f ≫ (f)_*[Ab.{u + 1}].map (coefficientMap a X) =
      coefficientMap a Y ≫ condensedPushforwardHom Λ' f := by
  rw [← unitAlgHom_comp_map_condensedPullbackHom, ← unitAlgHom_comp_map_condensedPullbackHom,
    Category.assoc, ← Functor.map_comp, ← map_coefficientMap_comp_condensedPullbackHom,
    Functor.map_comp]
  exact ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality_assoc _ _).symm

end CoefficientMap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-! ### Pushforward and pullback -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with the pushforward:
`f_*^Λ' ⋙ Res_{a_Y} ≅ Res_{a_X} ⋙ f_*^Λ`, both being `mapMod(f_*)` followed by the restriction
of scalars along the common composite of the square `a_Y ≫ η_f = η_f ≫ f_* a_X`. -/
noncomputable def comapLowerStarIso :
    (Strategy3.lowerStar Λ' (f)) ⋙ Mod.comap (coefficientMap a Y) ≅ Mod.comap (coefficientMap a X) ⋙ (Strategy3.lowerStar Λ (f)) :=
  Mod.comapMapModComapIso (f)_*[Ab.{u + 1}] (coefficientMap a X) (coefficientMap a Y)
    (condensedPushforwardHom Λ f) (condensedPushforwardHom Λ' f)
    (condensedPushforwardHom_comp_map_coefficientMap a f).symm

/-- **(Pull)**, underived: `f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'`, the conjugate of
`comapLowerStarIso` along `f^* ⊣ f_*` and `Ext ⊣ Res`. -/
noncomputable def pullIso :
    (Strategy3.upperStar Λ (f)) ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a Y) ⋙ (Strategy3.upperStar Λ' (f)) :=
  Adjunction.pullIsoOfComapIso (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ' f)
    (comapLowerStarIso a f)


end UpperLowerStar
noncomputable def freeFunctorCompUpperStarIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod.freeFunctor (condensedRingObj Λ Y) ⋙ Strategy3.upperStar Λ f ≅
      (f)^*[Ab.{u + 1}] ⋙ Mod.freeFunctor (condensedRingObj Λ X) :=
  (conjugateIsoEquiv ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).comp
      (Mod.freeForgetAdjunction _))
    ((Mod.freeForgetAdjunction _).comp (Strategy3.upperStarLowerStarAdjunction Λ f))).symm
    (Iso.refl _)


end AlgebraicGeometry.ProEtale.Strategy3
