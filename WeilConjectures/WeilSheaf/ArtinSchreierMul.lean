/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierTrace
public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.Isotypic
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Multiplicativity of Artin–Schreier sheaves of functions

Draft.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Congr

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The pushforwards of pro-étale Weil sheaves along equal morphisms are isomorphic. -/
noncomputable def ProEtaleWeilSheaf.lowerStarCongrIso {φ φ' : X ⟶ Y}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    ProEtaleWeilSheaf.lowerStar k₀ l φ ≅ ProEtaleWeilSheaf.lowerStar k₀ l φ' := by
  subst h
  exact Iso.refl _

lemma ProEtaleWeilSheaf.lowerStarCongrIso_hom_app_hom_f {φ φ' : X ⟶ Y}
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ')
    (K : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.lowerStarCongrIso k₀ l h).hom.app K).hom.f =
      (ProEtale.adicLowerStarCongr l
        (Scheme.Hom.geometricFiberMap_congr h (comp_over φ _) (comp_over φ' _))).hom.app
        K.carrier := by
  subst h
  refine Mod.hom_ext _ _ ?_
  rw [ProEtale.adicLowerStarCongr_hom_app_hom, ProEtale.lowerStarCongr_rfl]
  rfl

variable (k₀ l) in
/-- The Weil morphism `ℚ̄_ℓ ⟶ φ_* ℚ̄_ℓ`, adjoint to `φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
noncomputable def ProEtaleWeilSheaf.adicConstantToLowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.adicConstant k₀ l Y ⟶
      (ProEtaleWeilSheaf.lowerStar k₀ l φ).obj (ProEtaleWeilSheaf.adicConstant k₀ l X) :=
  (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).homEquiv _ _
    (WeilSheaf.upperStarAdicConstantIso φ).hom.hom

end Congr
lemma ProEtaleWeilSheaf.adicConstantToLowerStar_hom_f_hom (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.adicConstantToLowerStar k₀ l φ).hom.f.hom =
      ProEtale.adicConstantSheafToLowerStar l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) := by
  rw [ProEtaleWeilSheaf.adicConstantToLowerStar, Adjunction.homEquiv_unit,
    Endofunctor.IsoAlgebra.comp_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f, Mod.comp_hom']
  erw [Adjunction.modAdjunction_unit_app_hom]
  rw [Category.assoc]
  erw [← Functor.map_comp]
  exact ((ProEtale.upperStarLowerStarAdjunction _ _).homEquiv _ _).apply_symm_apply _

end Congr

end AlgebraicGeometry
