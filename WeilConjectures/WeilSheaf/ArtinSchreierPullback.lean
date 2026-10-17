/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierTrace
public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Pullbacks of Artin–Schreier sheaves

The constant Weil sheaf is stable under pullback
(`AlgebraicGeometry.WeilSheaf.upperStarAdicConstantIso`), and the pullback of the
Artin–Schreier sheaf `ℒ_ψ` along the Artin–Schreier map `AS` is the constant Weil sheaf
(`AlgebraicGeometry.WeilSheaf.upperStarArtinSchreierMapImageIso`), the trivialisation of
`ĀS^* ℒ_ψ` being compatible with the Weil structures.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section HomOfSection

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The coordinate of the morphism `X ⟶ 𝔸¹` defined by a function `a` is `a`. -/
@[simp]
lemma affineLine.homOfSection_appTop_coord (a : Γ(X, ⊤)) :
    (affineLine.homOfSection k₀ a).appTop (AffineSpace.coord _ PUnit.unit) = a :=
  AffineSpace.homOfVector_appTop_coord _ _ _

omit [Finite k₀] in
/-- The composite of a function `a : X ⟶ 𝔸¹` with the scaling `x ↦ c x` is the function `c a`. -/
lemma affineLine.homOfSection_comp_smul (a : Γ(X, ⊤)) (c : k₀) :
    affineLine.homOfSection k₀ a ≫ affineLine.smul k₀ c =
      affineLine.homOfSection k₀
        ((X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom c) * a) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · simp [affineLine.homOfSection, affineLine.smul]
  · simp only [affineLine.smul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.smul_appTop_coord, map_mul]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    simp [affineLine.homOfSection]

/-- The composite of a function `a : X ⟶ 𝔸¹` with the Artin–Schreier map is `a ^ q - a`. -/
lemma affineLine.homOfSection_comp_artinSchreierMap (a : Γ(X, ⊤)) :
    letI := Fintype.ofFinite k₀
    affineLine.homOfSection k₀ a ≫ affineLine.artinSchreierMap k₀ =
      affineLine.homOfSection k₀ (a ^ Fintype.card k₀ - a) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · simp [affineLine.homOfSection, affineLine.artinSchreierMap]
  · simp [affineLine.artinSchreierMap, affineLine.homOfSection]

end HomOfSection


namespace WeilSheaf

section HomMk

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A morphism of the underlying sheaves of modules of two Weil sheaves which is compatible with
their Weil structures `Fr^* F ⟶ F` (`AlgebraicGeometry.WeilSheaf.frobeniusStr`), as a morphism
of Weil sheaves. -/
noncomputable def homMkOfFrobeniusStr {F G : WeilSheaf k₀ l X}
    (f : F.obj.carrier ⟶ G.obj.carrier)
    (hf : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map f.hom ≫
      G.frobeniusStr = F.frobeniusStr ≫ f.hom) : F ⟶ G :=
  ObjectProperty.homMk (ObjectProperty.homMk ⟨f, by
    refine Mod.hom_ext _ _ ?_
    rw [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
      ← cancel_epi ((ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.app F.obj.carrier.X),
      ← (ProEtale.upperStarIsoLowerStarInv _ _).hom.naturality_assoc]
    exact hf⟩)

@[simp]
lemma homMkOfFrobeniusStr_hom_hom_f {F G : WeilSheaf k₀ l X}
    (f : F.obj.carrier ⟶ G.obj.carrier)
    (hf : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map f.hom ≫
      G.frobeniusStr = F.frobeniusStr ≫ f.hom) :
    (homMkOfFrobeniusStr f hf).hom.hom.f = f :=
  rfl

end HomMk

section Constant

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The underlying morphism of the canonical isomorphism `g^* ℚ̄_ℓ ≅ ℚ̄_ℓ` of sheaves of modules. -/
lemma _root_.AlgebraicGeometry.ProEtale.adicUpperStarUnitIso_hom_hom {Z W : Scheme.{u}}
    (g : Z ⟶ W) :
    (ProEtale.adicUpperStarUnitIso l g).hom.hom = ProEtale.upperStarAdicConstantSheafHom l g :=
  rfl

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The canonical isomorphism `φ̄^* ℚ̄_ℓ ≅ ℚ̄_ℓ` is compatible with the canonical Weil structures
`Fr^* ℚ̄_ℓ ≅ ℚ̄_ℓ`, by the cocycle condition. -/
lemma upperStarAdicConstantSheafHom_frobenius :
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
        (ProEtale.upperStarAdicConstantSheafHom l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))) ≫
        ProEtale.upperStarAdicConstantSheafHom l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom =
      (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).inv.app
          (ProEtale.adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
        (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app
          (ProEtale.adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
        (ProEtale.upperStarComp _
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app
          (ProEtale.adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[_].map
          (ProEtale.upperStarAdicConstantSheafHom l
            (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom) ≫
        ProEtale.upperStarAdicConstantSheafHom l
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) := by
  rw [← cancel_epi ((ProEtale.upperStarComp (WeilCoefficients.{u} l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).hom.app
        (ProEtale.adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)),
    Iso.hom_inv_id_app_assoc, ProEtale.upperStarAdicConstantSheafHom_comp,
    ProEtale.upperStarAdicConstantSheafHom_comp,
    ProEtale.upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom]

/-- The canonical morphism `φ^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` of Weil sheaves: the canonical isomorphism
`φ̄^* ℚ̄_ℓ ≅ ℚ̄_ℓ` of the underlying sheaves, which is compatible with the Weil structures by the
cocycle condition for these canonical isomorphisms. -/
noncomputable def upperStarAdicConstantHom :
    (upperStar φ).obj (adicConstant k₀ l Y) ⟶ adicConstant k₀ l X :=
  homMkOfFrobeniusStr (ProEtale.adicUpperStarUnitIso l
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).hom (by
    rw [ProEtale.adicUpperStarUnitIso_hom_hom, frobeniusStr_adicConstant, frobeniusStr_upperStar,
      frobeniusStr_adicConstant]
    simp only [Category.assoc]
    exact upperStarAdicConstantSheafHom_frobenius φ)

instance : IsIso (upperStarAdicConstantHom (k₀ := k₀) (l := l) φ) := by
  have : IsIso (upperStarAdicConstantHom (k₀ := k₀) (l := l) φ).hom.hom.f :=
    inferInstanceAs (IsIso (ProEtale.adicUpperStarUnitIso l
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).hom)
  exact isIso_of_isIso_hom_hom_f _

/-- **The pullback of the constant Weil sheaf is the constant Weil sheaf**: `φ^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
noncomputable def upperStarAdicConstantIso :
    (upperStar φ).obj (adicConstant k₀ l Y) ≅ adicConstant k₀ l X :=
  asIso (upperStarAdicConstantHom φ)

end Constant

end WeilSheaf

end AlgebraicGeometry
