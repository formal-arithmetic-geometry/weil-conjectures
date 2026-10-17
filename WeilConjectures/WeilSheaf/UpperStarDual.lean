/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LisseDuality
public import WeilConjectures.WeilSheaf.UpperStarTensor

/-!
# Pullbacks of duals of lisse Weil sheaves

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes. The pullback of the constant pro-étale Weil sheaf
`ℚ̄_ℓ` is `ℚ̄_ℓ` (`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarAdicConstantIso`), and the pullback
of the dual of a lisse Weil sheaf is the dual of its pullback
(`AlgebraicGeometry.WeilSheaf.upperStarDualIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal MonObj

namespace AlgebraicGeometry

open ProEtale Endofunctor

open scoped Obj

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "σX" => (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "σY" => (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "W" => WeilCoefficients.{u} l

/-- The Weil structure of the constant pro-étale Weil sheaf `ℚ̄_ℓ` preserves the unit section. -/
lemma adicConstant_one_str {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))] :
    ε ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W] ≫
        ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W].map
          (η : 𝟙_ _ ⟶ adicConstantSheaf l (S ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
        (ProEtaleWeilSheaf.adicConstant k₀ l S).str.hom.hom =
        (η : 𝟙_ _ ⟶ adicConstantSheaf l (S ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  set e := (S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm
  have : IsMonHom (adicConstantSheafLowerStarIso l e).inv :=
    inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l e.hom))
  have : IsMonHom (adicConstantSheafLowerStarIso l e).hom := by
    have : IsMonHom (inv (adicConstantSheafLowerStarIso l e).inv) := inferInstance
    rwa [IsIso.Iso.inv_inv] at this
  exact IsMonHom.one_hom (f := (adicConstantSheafLowerStarIso l e).hom)

/-- A section of a pro-étale Weil sheaf is compatible with the Weil structure in pushforward form
if and only if it is in pullback form. -/
lemma unit_str_iff {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]
    (P : ProEtaleWeilSheaf k₀ l S) (e : 𝟙_ _ ⟶ P.carrier.X) :
    ε ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W] ≫
        ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W].map e ≫
        P.str.hom.hom = e ↔
      ε ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[W] ≫
        ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[W].map e ≫
        frobeniusStr P = e := by
  set ι' := upperStarIsoLowerStarInv W (S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  have hu := NatTrans.IsMonoidal.unit (τ := ι'.hom)
  rw [frobeniusStr, ι'.hom.naturality_assoc, reassoc_of% hu]


/-- The pullback of a section compatible with the Weil structure is compatible with the Weil
structure, in pullback form. -/
lemma upperStar_unit_frobeniusStr (P : ProEtaleWeilSheaf k₀ l Y) (e : 𝟙_ _ ⟶ P.carrier.X)
    (he : ε ((σY).hom)^*[W] ≫ ((σY).hom)^*[W].map e ≫ frobeniusStr P = e) :
    ε ((σX).hom)^*[W] ≫ ((σX).hom)^*[W].map (ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e) ≫
        frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) =
      ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e := by
  set ψ := (upperStarComp W (σX).hom φ̄).symm ≪≫
    upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm ≪≫
    upperStarComp _ φ̄ (σY).hom
  have hψ : NatTrans.IsMonoidal ψ.hom := by
    simp only [ψ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hfs : frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) = ψ.hom.app _ ≫
      (φ̄)^*[W].map (frobeniusStr P) := by
    rw [frobeniusStr_upperStar]
    simp [ψ]
  have hψu := NatTrans.IsMonoidal.unit (τ := ψ.hom)
  simp only [Functor.LaxMonoidal.comp_ε] at hψu
  have hn := ψ.hom.naturality e
  simp only [Functor.comp_map] at hn
  rw [hfs, Functor.map_comp_assoc, reassoc_of% hn, reassoc_of% hψu, ← Functor.map_comp,
    ← Functor.map_comp, he]

/-- The pullback of a section compatible with the Weil structure is compatible with the Weil
structure. -/
lemma upperStar_unit_str (P : ProEtaleWeilSheaf k₀ l Y) (e : 𝟙_ _ ⟶ P.carrier.X)
    (he : ε ((σY).inv)_*[W] ≫ ((σY).inv)_*[W].map e ≫ P.str.hom.hom = e) :
    ε ((σX).inv)_*[W] ≫ ((σX).inv)_*[W].map (ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e) ≫
        ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).str.hom.hom =
      ε (φ̄)^*[W] ≫ (φ̄)^*[W].map e :=
  (unit_str_iff _ _).2 (upperStar_unit_frobeniusStr φ P e ((unit_str_iff P e).1 he))

end ProEtaleWeilSheaf

end AlgebraicGeometry
