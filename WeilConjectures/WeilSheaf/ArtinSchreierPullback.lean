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
public import WeilConjectures.WeilSheaf.UpperStarConstant

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

omit [Finite k₀] in
/-- The composite of a morphism `φ : Y ⟶ X` over `k₀` with the function `a : X ⟶ 𝔸¹` is the
function `φ^* a`. -/
lemma affineLine.comp_homOfSection {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))] (a : Γ(X, ⊤)) :
    φ ≫ affineLine.homOfSection k₀ a = affineLine.homOfSection k₀ (φ.appTop a) := by
  rw [affineLine.homOfSection, affineLine.homOfSection, AffineSpace.comp_homOfVector,
    comp_over]
  rfl

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

end WeilSheaf

section Trivialization

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

variable (ψ : AddChar k₀ (PadicAlgCl l))

variable (l) in
/-- The evaluation `ĀS^* ℒ_ψ ⟶ ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` at the point of the fibre given by the
Artin–Schreier cover, as a morphism of sheaves of modules. -/
noncomputable def affineLine.artinSchreierImageEvalModHom :
    (ĀS)^*ᵃ[l].obj (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier ⟶
      (WeilSheaf.adicConstant k₀ l (affineLine k₀)).obj.carrier :=
  (ĀS)^*ᵃ[l].map (image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f ≫
    (ProEtale.adicUpperStarLowerStarAdjunction l ĀS).counit.app _

lemma affineLine.artinSchreierImageEvalModHom_hom :
    (affineLine.artinSchreierImageEvalModHom l ψ).hom =
      affineLine.artinSchreierImageEval ψ 0 := by
  rw [affineLine.artinSchreierImageEvalModHom, Mod.comp_hom', ProEtale.adicUpperStar_map_hom]
  erw [Adjunction.modAdjunction_counit_app_hom]
  rw [affineLine.artinSchreierImageEval, affineLine.artinSchreierTranslation_zero,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

lemma affineLine.isIso_artinSchreierImageEval :
    IsIso (affineLine.artinSchreierImageEval ψ 0) := by
  obtain ⟨E, hE⟩ := affineLine.exists_iso_artinSchreierImage ψ
  have h := hE 0
  rw [AddChar.map_zero_eq_one] at h
  have h' : affineLine.artinSchreierImageEval ψ 0 = E.hom := by
    rw [affineLine.artinSchreierImageEval, h]
    erw [one_smul]
    exact Category.comp_id _
  rw [h']
  infer_instance

/-- The trivialisation `AS^* ℒ_ψ ⟶ ℚ̄_ℓ` of the pullback of `ℒ_ψ` along the Artin–Schreier map,
as a morphism of Weil sheaves: the evaluation at the point of the fibre given by the cover, which
is compatible with the Weil structures
(`AlgebraicGeometry.affineLine.artinSchreierImageEval_frobenius`). -/
noncomputable def WeilSheaf.upperStarArtinSchreierMapImageHom :
    (WeilSheaf.upperStar (affineLine.artinSchreierMap k₀)).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ)) ⟶
      WeilSheaf.adicConstant k₀ l (affineLine k₀) :=
  WeilSheaf.homMkOfFrobeniusStr (affineLine.artinSchreierImageEvalModHom l ψ) (by
    rw [affineLine.artinSchreierImageEvalModHom_hom, WeilSheaf.frobeniusStr_upperStar]
    simp only [Category.assoc]
    exact (Iso.eq_inv_comp ((ProEtale.upperStarComp (WeilCoefficients.{u} l)
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ĀS).app _)).2
      (affineLine.artinSchreierImageEval_frobenius ψ))

instance : IsIso (WeilSheaf.upperStarArtinSchreierMapImageHom ψ) := by
  have : IsIso (affineLine.artinSchreierImageEvalModHom l ψ).hom := by
    rw [affineLine.artinSchreierImageEvalModHom_hom]
    exact affineLine.isIso_artinSchreierImageEval ψ
  have : IsIso (affineLine.artinSchreierImageEvalModHom l ψ) :=
    isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso (WeilSheaf.upperStarArtinSchreierMapImageHom ψ).hom.hom.f :=
    inferInstanceAs (IsIso (affineLine.artinSchreierImageEvalModHom l ψ))
  exact WeilSheaf.isIso_of_isIso_hom_hom_f _

/-- Blueprint `lem-fd-as-lisse`: the pullback of `ℒ_ψ` along the Artin–Schreier map is the
constant Weil sheaf, `AS^* ℒ_ψ ≅ ℚ̄_ℓ`. -/
noncomputable def WeilSheaf.upperStarArtinSchreierMapImageIso :
    (WeilSheaf.upperStar (affineLine.artinSchreierMap k₀)).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ)) ≅
      WeilSheaf.adicConstant k₀ l (affineLine k₀) :=
  asIso (WeilSheaf.upperStarArtinSchreierMapImageHom ψ)

end Trivialization

end AlgebraicGeometry
