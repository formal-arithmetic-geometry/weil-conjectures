module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarTensor

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T₁ T₂ : Scheme.{u}}
attribute [local instance] Sheaf.symmetricCategory
set_option linter.style.longLine false

noncomputable def EE (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (M : AdicSheaf l T₂) :
    (Mod.mapModComap (adicConstantSheafToLowerStar l a.inv)).obj
      ((Mod.mapModComap (adicUpperStarRingHom l j)).obj M) ⟶
    (Mod.mapModComap (adicUpperStarRingHom l j)).obj
      ((Mod.mapModComap (adicConstantSheafToLowerStar l b.inv)).obj M) :=
  (adicUpperStarExchange l j a b c).hom.app M

lemma w1 (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (M : AdicSheaf l T₂) : (EE j a b c M).hom = (upperStarExchange l j a b c).hom.app M.X :=
  adicUpperStarExchange_hom_app_hom j a b c M

noncomputable def EE' (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (M : AdicSheaf l T₂) :
    (@Mod.mapModComap _ _ _ _ _ _ _ _ _ _ (a.inv)_*[WeilCoefficients.{u} l] Functor.LaxBraided.toLaxMonoidal (adicConstantSheafToLowerStar l a.inv) _).obj
      ((Mod.mapModComap (adicUpperStarRingHom l j)).obj M) ⟶
    (Mod.mapModComap (adicUpperStarRingHom l j)).obj
      ((@Mod.mapModComap _ _ _ _ _ _ _ _ _ _ (b.inv)_*[WeilCoefficients.{u} l] Functor.LaxBraided.toLaxMonoidal (adicConstantSheafToLowerStar l b.inv) _).obj M) :=
  (adicUpperStarExchange l j a b c).hom.app M

lemma w1' (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (M : AdicSheaf l T₂) : (EE' j a b c M).hom = (upperStarExchange l j a b c).hom.app M.X :=
  adicUpperStarExchange_hom_app_hom j a b c M

lemma s2' (g : T₁ ⟶ T₁) [IsIso g] (M : AdicSheaf l T₁)
    [(Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence] :
    adicLowerStarTensorLeftIso l g M =
      Mod.tensorLeftCompMapModComapIso (adicConstantSheafToLowerStar l g)
        (by exact fun _ _ ↦ Functor.LaxBraided.braided _ _) M :=
  rfl

lemma hth (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (X Y : Sheaf (Scheme.ProEt.topology T₂) (WeilCoefficients.{u} l)) :
    μ (a.inv)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj X) ((j)^*[WeilCoefficients.{u} l].obj Y) ≫
      (a.inv)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] X Y) ≫
      (upperStarExchange l j a b c).hom.app (X ⊗ Y) =
    ((upperStarExchange l j a b c).hom.app X ⊗ₘ (upperStarExchange l j a b c).hom.app Y) ≫
      μ (j)^*[WeilCoefficients.{u} l] ((b.inv)_*[WeilCoefficients.{u} l].obj X) ((b.inv)_*[WeilCoefficients.{u} l].obj Y) ≫
      (j)^*[WeilCoefficients.{u} l].map (μ (b.inv)_*[WeilCoefficients.{u} l] X Y) := by
  simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc] using
    NatTrans.IsMonoidal.tensor (τ := (upperStarExchange l j a b c).hom) X Y

variable (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom) (P M : AdicSheaf l T₂)
  [PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (j)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l j))]
  [(Mod.mapModComap (G := (a.inv)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l a.inv)).IsEquivalence]
  [(Mod.mapModComap (G := (b.inv)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l b.inv)).IsEquivalence]
include j a b c P M

lemma r1 : (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l j M).hom.app P) =
    (Mod.mapModComap (adicConstantSheafToLowerStar l a.inv)).map ((Mod.tensorLeftCompMapModComapIso (adicUpperStarRingHom l j)
      (by exact fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ j) _ _) M).hom.app P) := rfl

lemma r2 : (adicLowerStarTensorLeftIso l a.inv ((j)^*ᵃ[l].obj M)).hom.app ((j)^*ᵃ[l].obj P) =
    (Mod.tensorLeftCompMapModComapIso (adicConstantSheafToLowerStar l a.inv)
      (by exact fun _ _ ↦ Functor.LaxBraided.braided _ _) ((Mod.mapModComap (adicUpperStarRingHom l j)).obj M)).hom.app
      ((Mod.mapModComap (adicUpperStarRingHom l j)).obj P) := rfl

lemma r3 : (Mod.tensorLeftMap ((adicUpperStarExchange l j a b c).hom.app M)).app ((a.inv)_*ᵃ[l].obj ((j)^*ᵃ[l].obj P)) =
    (Mod.tensorLeftMap ((fun M ↦ (adicUpperStarExchange l j a b c).hom.app M :
      ∀ M : AdicSheaf l T₂, (Mod.mapModComap (adicConstantSheafToLowerStar l a.inv)).obj ((Mod.mapModComap (adicUpperStarRingHom l j)).obj M) ⟶
      (Mod.mapModComap (adicUpperStarRingHom l j)).obj ((Mod.mapModComap (adicConstantSheafToLowerStar l b.inv)).obj M)) M)).app
      ((Mod.mapModComap (adicConstantSheafToLowerStar l a.inv)).obj ((Mod.mapModComap (adicUpperStarRingHom l j)).obj P)) := rfl

lemma r4 : (Mod.tensorLeft (((b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l]).obj M)).map ((adicUpperStarExchange l j a b c).hom.app P) =
    (Mod.tensorLeft ((Mod.mapModComap (adicUpperStarRingHom l j)).obj ((Mod.mapModComap (adicConstantSheafToLowerStar l b.inv)).obj M))).map
      ((fun M ↦ (adicUpperStarExchange l j a b c).hom.app M :
      ∀ M : AdicSheaf l T₂, (Mod.mapModComap (adicConstantSheafToLowerStar l a.inv)).obj ((Mod.mapModComap (adicUpperStarRingHom l j)).obj M) ⟶
      (Mod.mapModComap (adicUpperStarRingHom l j)).obj ((Mod.mapModComap (adicConstantSheafToLowerStar l b.inv)).obj M)) P) := rfl

lemma r6 : (j)^*ᵃ[l].map ((adicLowerStarTensorLeftIso l b.inv M).hom.app P) =
    (Mod.mapModComap (adicUpperStarRingHom l j)).map ((Mod.tensorLeftCompMapModComapIso (adicConstantSheafToLowerStar l b.inv)
      (by exact fun _ _ ↦ Functor.LaxBraided.braided _ _) M).hom.app P) := rfl

lemma r7 : (adicUpperStarTensorLeftIso l j ((b.inv)_*ᵃ[l].obj M)).hom.app ((b.inv)_*ᵃ[l].obj P) =
    (Mod.tensorLeftCompMapModComapIso (adicUpperStarRingHom l j)
      (by exact fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ j) _ _)
      ((Mod.mapModComap (adicConstantSheafToLowerStar l b.inv)).obj M)).hom.app
      ((Mod.mapModComap (adicConstantSheafToLowerStar l b.inv)).obj P) := rfl

omit j a b c P M
lemma inst2 (T : Scheme.{u}) :
    (SymmetricCategory.toBraidedCategory : BraidedCategory (Sheaf (Scheme.ProEt.topology T) (WeilCoefficients.{u} l))) =
    ProEtale.sheafBraidedCategory (WeilCoefficients.{u} l) T := rfl

lemma inst3 (T : Scheme.{u}) :
    (ProEtale.sheafSymmetricCategory T).toBraidedCategory =
    ProEtale.sheafBraidedCategory (WeilCoefficients.{u} l) T := rfl

end AlgebraicGeometry.ProEtale
