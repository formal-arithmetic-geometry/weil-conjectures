/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.CategoryTheory.Monoidal.Conjugate

/-!
# Local bases of the integral Tate module

Source: Bhatt–Scholze, The pro-étale topology for schemes, Section 6.8, and the
Tate-twist unit of the current blueprint.
(blueprint: lem-poincare-integral-tate-pullback-local-line)
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {B : Type u₄} [Category.{v₄} B] [MonoidalCategory B]
private theorem twoStepComparison_linear
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ E) (K : E ⥤ B)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] [K.LaxMonoidal]
    (e : F ⋙ G ≅ H ⋙ K) [NatTrans.IsMonoidal e.hom]
    (R : C) [MonObj R] (M : Mod C R) :
    γ[G.obj (F.obj R), ((G.mapMod (F.obj R)).obj ((F.mapMod R).obj M)).X] ≫
      (e.app M.X).hom =
    G.obj (F.obj R) ◁ (e.app M.X).hom ≫ (e.app R).hom ▷ K.obj (H.obj M.X) ≫
      γ[K.obj (H.obj R), ((K.mapMod (H.obj R)).obj ((H.mapMod R).obj M)).X] := by
  have hlin : Functor.LaxMonoidal.μ (F ⋙ G) R M.X ≫
      (F ⋙ G).map γ[R,M.X] ≫ e.hom.app M.X =
      (e.hom.app R ⊗ₘ e.hom.app M.X) ≫
      Functor.LaxMonoidal.μ (H ⋙ K) R M.X ≫ (H ⋙ K).map γ[R,M.X] := by
    rw [e.hom.naturality, ← Category.assoc, NatTrans.IsMonoidal.tensor, Category.assoc]
  change (Functor.LaxMonoidal.μ G (F.obj R) (F.obj M.X) ≫
      G.map (Functor.LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X])) ≫ e.hom.app M.X =
    G.obj (F.obj R) ◁ e.hom.app M.X ≫ e.hom.app R ▷ K.obj (H.obj M.X) ≫
      (Functor.LaxMonoidal.μ K (H.obj R) (H.obj M.X) ≫
        K.map (Functor.LaxMonoidal.μ H R M.X ≫ H.map γ[R,M.X]))
  simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.assoc, tensorHom_def'] using hlin

private theorem twoStep_regular
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ E) (K : E ⥤ B)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] [K.LaxMonoidal]
    (e : F ⋙ G ≅ H ⋙ K) [NatTrans.IsMonoidal e.hom]
    (R : C) [MonObj R] (M : Mod C R)
    (hq : Nonempty (((K.mapMod (H.obj R)).obj ((H.mapMod R).obj M)) ≅
      Mod.regular (K.obj (H.obj R)))) :
    Nonempty (((G.mapMod (F.obj R)).obj ((F.mapMod R).obj M)) ≅
      Mod.regular (G.obj (F.obj R))) := by
  let a : G.obj (F.obj R) ⟶ K.obj (H.obj R) := e.hom.app R
  have : @IsMonHom B _ _ _ _ (G.monObjObj (F.obj R)) (K.monObjObj (H.obj R)) a :=
    IsMonHom.of_eq (h₁ := (F ⋙ G).monObjObj R) (h₂ := (H ⋙ K).monObjObj R)
      a (Functor.monObjObj_comp F G R) (Functor.monObjObj_comp H K R)
  let E : Mod B (K.obj (H.obj R)) ⥤ Mod B (G.obj (F.obj R)) := Mod.comap a
  let em : ((G.mapMod (F.obj R)).obj ((F.mapMod R).obj M)) ≅
      E.obj ((K.mapMod (H.obj R)).obj ((H.mapMod R).obj M)) :=
    Mod.isoMk (e.app M.X) (twoStepComparison_linear F G H K e R M)
  let eu : Mod.regular (G.obj (F.obj R)) ≅
      E.obj (Mod.regular (K.obj (H.obj R))) :=
    Mod.isoMk (e.app R) (by
      change μ[G.obj (F.obj R)] ≫ a =
        G.obj (F.obj R) ◁ a ≫ a ▷ K.obj (H.obj R) ≫ μ[K.obj (H.obj R)]
      rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])
  obtain ⟨q⟩ := hq
  exact ⟨em ≪≫ E.mapIso q ≪≫ eu.symm⟩
end CategoryTheory

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.ProEtale
private theorem comp_inverse_monoidal {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).inv := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} f g).inv
private theorem congr_monoidal {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    NatTrans.IsMonoidal (upperStarCongr Ab.{u + 1} h).hom := by
  subst g
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))

private theorem local_regular_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (h : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj M ≅ Mod.regular _)) :
    ∃ 𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : 𝒱.I₀,
      Nonempty ((((upperStar Ab.{u + 1} (𝒱.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj R)).obj
          (((upperStar Ab.{u + 1} f).mapMod R).obj M)) ≅ Mod.regular _) := by
  obtain ⟨𝒰, h𝒰⟩ := h
  let 𝒱 := 𝒰.pullback₁ f
  refine ⟨𝒱, fun i ↦ ?_⟩
  let g := pullback.snd f (𝒰.f i)
  let e : upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (𝒱.f i) ≅
      upperStar Ab.{u + 1} (𝒰.f i) ⋙ upperStar Ab.{u + 1} g :=
    (upperStarComp Ab.{u + 1} (𝒱.f i) f).symm ≪≫
      upperStarCongr Ab.{u + 1} (pullback.condition (f := f) (g := 𝒰.f i)) ≪≫
        upperStarComp Ab.{u + 1} g (𝒰.f i)
  have := comp_inverse_monoidal (𝒱.f i) f
  have : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} g (𝒰.f i)).hom := by
    have : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} g (𝒰.f i)).symm.hom :=
      comp_inverse_monoidal g (𝒰.f i)
    exact inferInstanceAs
      (NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} g (𝒰.f i)).symm.inv)
  have := congr_monoidal (pullback.condition (f := f) (g := 𝒰.f i))
  have : NatTrans.IsMonoidal e.hom := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    infer_instance
  let F := upperStar Ab.{u + 1} (𝒰.f i)
  let G := upperStar Ab.{u + 1} g
  let : G.Braided := CondensedRing.braided_sheafUpperStar g
  obtain ⟨eM⟩ := h𝒰 i
  apply CategoryTheory.twoStep_regular _ _ _ _ e R M
  exact ⟨(G.mapMod (F.obj R)).mapIso eM ≪≫ G.mapModUnitIso.symm⟩

/-- The integral Tate module, after inverse image, has a pro-étale local basis.

Source: the current blueprint, `sk-def-sp-tate-twist`, integral limit and coefficient
extension; Bhatt–Scholze, Section 6.8.

Proof: identify the free integral level with the roots-of-unity sheaf using
`ℤ_ℓ,X / ℓ^r = (ℤ/ℓ^r)_X`: multiplication and `z ↦ 1 ⊗ z` are inverse, as checked
locally on integer representatives of residue classes. These maps commute with the power
transitions, including the zero level. Thus the inverse limit is the integral Tate line.
When ℓ is invertible, compatible primitive roots give pro-étale local bases of that line.
Pull back the trivializing cover along `f`; inverse image preserves
its covering property and the unit object of module sheaves. The result is the regular
module over the twice-pulled-back integral coefficient ring. This also covers the empty
scheme, where the empty cover suffices.
(blueprint: lem-poincare-integral-tate-pullback-local-line) -/
theorem tateModule_pullback_locally_trivial
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    {Y : Scheme.{u}} (f : Y ⟶ X) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : 𝒰.I₀,
      Nonempty
        ((((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj
            (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))).obj
          (((upperStar Ab.{u + 1} f).mapMod
            (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)).obj
              (tateModule X ℓ))) ≅ 𝟙_ _) := by
  exact local_regular_pullback f
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) (tateModule X ℓ)
      (tateModule_locally_trivial X ℓ hℓ)

end AlgebraicGeometry.ProEtale
