/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.ChangeCoefficients
public import WeilConjectures.TateTwist.TateModuleUpperStar

/-! # Independent coefficient/pullback infrastructure: Tower -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

section FreeTower

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- If the pullback `g^*` of abelian sheaves preserves the limit of the underlying diagram, then
the pullback of module objects over `Λ` preserves the limit of the diagram: the pullback of module
objects is `mapMod(g^*)`, whose limits are computed on underlying objects, followed by the
extension of scalars along the isomorphism `α_g`, an equivalence. -/
lemma preservesLimit_upperStar
    (K : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    [PreservesLimit (K ⋙ Mod.forget _) (g)^*[Ab.{u + 1}]] :
    PreservesLimit K (Strategy3.upperStar Λ g) := by
  have : PreservesLimit K ((g)^*[Ab.{u + 1}].mapMod _ ⋙ Mod.forget _) :=
    inferInstanceAs (PreservesLimit _ (Mod.forget _ ⋙ (g)^*[Ab.{u + 1}]))
  have : PreservesLimit K ((g)^*[Ab.{u + 1}].mapMod _) :=
    preservesLimit_of_reflects_of_preserves _ (Mod.forget _)
  exact inferInstanceAs (PreservesLimit _ ((g)^*[Ab.{u + 1}].mapMod _ ⋙ Mod.extendScalars _))

variable {F : ℕ → Sheaf (ProEt.topology X) Ab.{u + 1}} (t : ∀ n, F (n + 1) ⟶ F n)
  {F' : ℕ → Sheaf (ProEt.topology X') Ab.{u + 1}} (t' : ∀ n, F' (n + 1) ⟶ F' n)
  (e : ∀ n, (g)^*[Ab.{u + 1}].obj (F n) ≅ F' n)

/-- The components `g^*(Λ_X ⊗ Fₙ) ≅ Λ_X' ⊗ F'ₙ` of the pullback of a tower of free modules. -/
noncomputable def upperStarFreeTowerIsoApp (n : ℕ) :
    (Strategy3.upperStar Λ g).obj ((Mod.freeFunctor (condensedRingObj Λ X)).obj (F n)) ≅
      (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n) :=
  (Strategy3.freeFunctorCompUpperStarIso Λ g).app (F n) ≪≫
    (Mod.freeFunctor (condensedRingObj Λ X')).mapIso (e n)

variable {t t' e} in
lemma upperStarFreeTowerIsoApp_naturality
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) (n : ℕ) :
    (Strategy3.upperStar Λ g).map ((Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ≫
        (upperStarFreeTowerIsoApp Λ g e n).hom =
      (upperStarFreeTowerIsoApp Λ g e (n + 1)).hom ≫
        (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n) := by
  have h := (Strategy3.freeFunctorCompUpperStarIso Λ g).hom.naturality (t n)
  rw [Functor.comp_map, Functor.comp_map] at h
  rw [upperStarFreeTowerIsoApp, upperStarFreeTowerIsoApp, Iso.trans_hom, Iso.trans_hom,
    Iso.app_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_hom, reassoc_of% h,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, he]

/-- The comparison from the pullback of the tower of free modules `n ↦ Λ_X ⊗ Fₙ` to the tower of
free modules `n ↦ Λ_X' ⊗ F'ₙ`, given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarFreeTowerHom
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) :
    Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙
        Strategy3.upperStar Λ g ⟶
      Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n)) :=
  NatTrans.ofOpSequence (fun n ↦ (upperStarFreeTowerIsoApp Λ g e n).hom) (fun n ↦ by
    simpa using upperStarFreeTowerIsoApp_naturality Λ g he n)

instance (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) :
    IsIso (upperStarFreeTowerHom Λ g t t' e he) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  exact inferInstanceAs (IsIso (upperStarFreeTowerIsoApp Λ g e n.unop).hom)

/-- The pullback of the tower of free modules `n ↦ Λ_X ⊗ Fₙ` is the tower of free modules
`n ↦ Λ_X' ⊗ F'ₙ`, given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarFreeTowerIso
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n) :
    Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙
        Strategy3.upperStar Λ g ≅
      Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n)) :=
  asIso (upperStarFreeTowerHom Λ g t t' e he)

/-- **The pullback of the limit of a tower of free modules**: if `g^*` preserves the limit of
the tower `n ↦ Λ_X ⊗ Fₙ` of abelian sheaves, then `g^* lim_n (Λ_X ⊗ Fₙ) ≅ lim_n (Λ_X' ⊗ F'ₙ)`,
given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarLimitFreeTowerIso
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n)
    (hK : PreservesLimit (Functor.ofOpSequence
      (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
      (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙ Mod.forget _)
      (g)^*[Ab.{u + 1}]) :
    (Strategy3.upperStar Λ g).obj (limit (Functor.ofOpSequence
      (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
      (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)))) ≅
      limit (Functor.ofOpSequence
        (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n))) :=
  have := hK
  have := Strategy3.preservesLimit_upperStar Λ g (Functor.ofOpSequence
    (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
    (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)))
  preservesLimitIso _ _ ≪≫ HasLimit.isoOfNatIso (upperStarFreeTowerIso Λ g t t' e he)

/-- **The pullback of the extension of scalars of the limit of a tower of free modules**: for a
morphism `a : Λ ⟶ Λ'` of commutative condensed rings, if `g^*` preserves the limit of the tower
`n ↦ Λ_X ⊗ Fₙ` of abelian sheaves, then `g^*(Λ'_X ⊗_{Λ_X} lim_n (Λ_X ⊗ Fₙ)) ≅
Λ'_X' ⊗_{Λ_X'} lim_n (Λ_X' ⊗ F'ₙ)`, given compatible isomorphisms `g^* Fₙ ≅ F'ₙ`. -/
noncomputable def upperStarExtendScalarsLimitFreeTowerIso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (he : ∀ n, (g)^*[Ab.{u + 1}].map (t n) ≫ (e n).hom = (e (n + 1)).hom ≫ t' n)
    (hK : PreservesLimit (Functor.ofOpSequence
      (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
      (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n)) ⋙ Mod.forget _)
      (g)^*[Ab.{u + 1}]) :
    (Strategy3.upperStar Λ' g).obj ((Mod.extendScalars (coefficientMap a X)).obj
      (limit (Functor.ofOpSequence
        (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).obj (F n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X)).map (t n))))) ≅
      (Mod.extendScalars (coefficientMap a X')).obj (limit (Functor.ofOpSequence
        (X := fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).obj (F' n))
        (fun n ↦ (Mod.freeFunctor (condensedRingObj Λ X')).map (t' n)))) :=
  ((Strategy3.pullIso a g).app _).symm ≪≫
    (Mod.extendScalars (coefficientMap a X')).mapIso (upperStarLimitFreeTowerIso Λ g t t' e he hK)

end FreeTower
end AlgebraicGeometry.ProEtale.Strategy3
