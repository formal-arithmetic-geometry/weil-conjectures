/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import Sheaf.AlgebraicGeometry.ClosedCoefficientSourceTransitionIso
import Sheaf.AlgebraicGeometry.ClosedCoefficientTargetTransitionIso
import WeilConjectures.AlgebraicGeometry.BaseChangeTargetCoefficientNaturality

/-! # Closed coefficient range comparison

Source: Stacks Project, Tag 0F07, closed–open part of the proof.
(blueprint: lem-sbc-closed-coefficient-range)
-/

@[expose] public section

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryPlus
  CategoryTheory.Functor.rightDerivedFunctorPlus

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
private lemma mapped_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C₁ D₁ : C} (a : A ⟶ B) (b : B ⟶ D₁) (c : A ⟶ C₁) (d : C₁ ⟶ D₁)
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

private lemma map_inv_hom_comp
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {K L M : C} (e : K ≅ L) (v : L ⟶ M) :
    F.map e.inv ≫ F.map (e.hom ≫ v) = F.map v := by
  rw [← F.map_comp, ← Category.assoc, e.inv_hom_id, Category.id_comp]

namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
private lemma injective_iso {M N : ModuleCat.{u + 1} Λ} (v : M ⟶ N) [IsIso v] :
    Function.Injective v.hom := by
  exact (ModuleCat.mono_iff_injective v).mp inferInstance

private lemma range_transport
    {A A₀ A₁ B B₀ B₁ C : ModuleCat.{u + 1} Λ}
    (b : A ⟶ B) (d : A₀ ⟶ B₀) (s : A ⟶ A₁) (t : B ⟶ B₁)
    [IsIso s] [IsIso t] (bZ : A₁ ⟶ B₁) (r : C ⟶ B₀) (v : C ⟶ B)
    (γ : A₀ ⟶ A₁) (δ : B₀ ⟶ B₁)
    (hb : b ≫ t = s ≫ bZ) (hn : γ ≫ bZ = d ≫ δ) (hv : r ≫ δ = v ≫ t)
    (ζ : C) (hζ : r.hom ζ ∈ Set.range d.hom) : v.hom ζ ∈ Set.range b.hom := by
  obtain ⟨y, hy⟩ := hζ
  let k := γ ≫ inv s
  have hk : k ≫ b ≫ t = d ≫ δ := by
    rw [hb]
    simp only [k, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hn
  refine ⟨k.hom y, ?_⟩
  apply injective_iso Λ t
  calc
    t.hom (b.hom (k.hom y)) = δ.hom (d.hom y) :=
      congrArg (fun f ↦ f.hom y) hk
    _ = δ.hom (r.hom ζ) := congrArg δ.hom hy
    _ = t.hom (v.hom ζ) := congrArg (fun f ↦ f.hom ζ) hv

private lemma closed_square_coefficient_range
    {X S T Y Z YZ : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (q : ℤ)
    (F' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : Z ⟶ T) [IsClosedImmersion i]
    {eZ : YZ ⟶ Z} {hZ : YZ ⟶ X}
    (sqZ : IsPullback eZ hZ (i ≫ g) p)
    (a : YZ ⟶ Y) (wa : a ≫ e = eZ ≫ i) (wh : a ≫ h = hZ)
    (K : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (β : K ≅ (((i)^*[ModuleCat.{u + 1} Λ]).obj F'))
    (fiber : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ)
    (ζ : fiber.obj ((baseChangeTargetFunctor Λ e h q).obj F'))
    (hζ : (fiber.map (baseChangeTargetTransition Λ e h q i a eZ hZ wa wh F' ≫
        (baseChangeTargetFunctor Λ eZ hZ q).map β.inv)).hom ζ ∈
      Set.range (fiber.map (baseChangeHomologyMap Λ sqZ q K)).hom) :
    (fiber.map ((baseChangeTargetFunctor Λ e h q).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F'))).hom ζ ∈
    Set.range (fiber.map (baseChangeHomologyMap Λ sq q
      (((i)_*[ModuleCat.{u + 1} Λ]).obj
        (((i)^*[ModuleCat.{u + 1} Λ]).obj F')))).hom := by
  let G := (((i)^*[ModuleCat.{u + 1} Λ]).obj F')
  let H := (((i)_*[ModuleCat.{u + 1} Λ]).obj G)
  let η : F' ⟶ H := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F'
  let α : K ⟶ (((i)^*[ModuleCat.{u + 1} Λ]).obj H) :=
    β.hom ≫ ((i)^*[ModuleCat.{u + 1} Λ]).map η
  let b := fiber.map (baseChangeHomologyMap Λ sq q H)
  let bZ := fiber.map (baseChangeHomologyMap Λ sqZ q (((i)^*[ModuleCat.{u + 1} Λ]).obj H))
  let s := fiber.map (baseChangeSourceTransition Λ p g q i H)
  let t := fiber.map (baseChangeTargetTransition Λ e h q i a eZ hZ wa wh H)
  let tF := fiber.map (baseChangeTargetTransition Λ e h q i a eZ hZ wa wh F')
  let v := fiber.map ((baseChangeTargetFunctor Λ e h q).map η)
  let vZ := fiber.map ((baseChangeTargetFunctor Λ eZ hZ q).map (((i)^*[ModuleCat.{u + 1} Λ]).map η))
  let βT := fiber.map ((baseChangeTargetFunctor Λ eZ hZ q).map β.inv)
  have : IsIso s := by
    have := baseChangeSourceTransition_isIso_closed_coefficients Λ p g q i G
    exact Functor.map_isIso _ _
  have : IsIso t := by
    have := baseChangeTargetTransition_isIso_closed_coefficients Λ sq i sqZ a wa wh q G
    exact Functor.map_isIso _ _
  let bFZ := fiber.map (baseChangeHomologyMap Λ sqZ q K)
  simp only [Functor.map_comp] at hζ
  let γ := fiber.map ((baseChangeSourceFunctor Λ p (i ≫ g) q).map α)
  let δ := fiber.map ((baseChangeTargetFunctor Λ eZ hZ q).map α)
  have hn : γ ≫ bZ = bFZ ≫ δ :=
    mapped_square fiber _ _ _ _ (baseChangeHomologyMap_naturality Λ sqZ q α).symm
  have hδ : βT ≫ δ = vZ :=
    map_inv_hom_comp ((baseChangeTargetFunctor Λ eZ hZ q) ⋙ fiber)
      β (((i)^*[ModuleCat.{u + 1} Λ]).map η)
  have hv : v ≫ t = tF ≫ vZ :=
    mapped_square fiber _ _ _ _
      (target_transition_naturality Λ e h q i a eZ hZ wa wh η)
  have hb : b ≫ t = s ≫ bZ :=
    mapped_square fiber _ _ _ _
      (baseChangeHomologyMap_comp_baseChangeTargetTransition Λ sq q i sqZ a wa wh H)
  have hc : (tF ≫ βT) ≫ δ = v ≫ t := by
    rw [Category.assoc, hδ, ← hv]
  exact range_transport Λ b bFZ s t bZ (tF ≫ βT) v γ δ hb hn hc ζ hζ


variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)
/-- A class that is a base-change image on the closed subscheme is an image after
mapping coefficients to the closed pushforward.

Source: Stacks Project, Tag 0F07, closed summand in condition (3).
(blueprint: lem-sbc-closed-coefficient-range)

Proof: the direct image along a closed immersion is exact on etale module sheaves,
and closed-immersion base change identifies e inverse image of i pushforward with
the corresponding closed pushforward on Y. Composition of derived direct images
therefore identifies the base-change map with coefficients i_* i^* F with the map
for the square over Z. Under these identifications the coefficient unit gives the
canonical target transition. Transport a source preimage across the source
identification to obtain the required preimage on T. This works also when Z is empty.
-/
theorem baseChange_closed_coefficient_mem_range (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    {T' : Scheme.{u}} (f : T' ⟶ T)
    (ζ : baseChangeTargetStalk Λ p g q F x (Over.mk f))
    {Z : Scheme.{u}} (i : Z ⟶ T') [IsClosedImmersion i]
    (hζ : (baseChangeTargetStalkMap Λ p g q F x
      (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f)).hom ζ ∈
        Set.range (baseChangeStalkMap Λ p g q F x (Over.mk (i ≫ f))).hom) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
      ((baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p)
        (pullback.snd (f ≫ g) p) q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
          (((f)^*[ModuleCat.{u + 1} Λ]).obj F)))).hom ζ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q
          (((i)_*[ModuleCat.{u + 1} Λ]).obj
            (((i)^*[ModuleCat.{u + 1} Λ]).obj
              (((f)^*[ModuleCat.{u + 1} Λ]).obj F))))).hom := by
  dsimp only [baseChangeTargetStalkMap, baseChangeStalkMap, baseChangeSourceStalk,
    baseChangeTargetStalk, Over.mk, Over.homMk] at hζ
  exact closed_square_coefficient_range Λ (IsPullback.of_hasPullback (f ≫ g) p) q
    (((f)^*[ModuleCat.{u + 1} Λ]).obj F) i
    (IsPullback.of_hasPullback ((i ≫ f) ≫ g) p)
    (pullback.lift
      (pullback.fst ((i ≫ f) ≫ g) p ≫ i)
      (pullback.snd ((i ≫ f) ≫ g) p)
      (by
        calc
          (pullback.fst ((i ≫ f) ≫ g) p ≫ i) ≫ (f ≫ g) =
              ((pullback.fst ((i ≫ f) ≫ g) p ≫ i) ≫ f) ≫ g :=
            (Category.assoc _ f g).symm
          _ = (pullback.fst ((i ≫ f) ≫ g) p ≫ (i ≫ f)) ≫ g :=
            congrArg (· ≫ g) (Category.assoc _ i f)
          _ = pullback.fst ((i ≫ f) ≫ g) p ≫ ((i ≫ f) ≫ g) :=
            Category.assoc _ (i ≫ f) g
          _ = pullback.snd ((i ≫ f) ≫ g) p ≫ p := pullback.condition))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (((i ≫ f)^*[ModuleCat.{u + 1} Λ]).obj F)
    ((upperStarComp (ModuleCat.{u + 1} Λ) i f (i ≫ f) rfl).app F)
    (X.uliftPointSmallEtale x).sheafFiber ζ hζ

end AlgebraicGeometry.Etale
