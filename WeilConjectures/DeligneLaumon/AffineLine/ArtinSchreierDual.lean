/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.DeligneLaumon.AffineLine.Constituent
public import WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.ArtinSchreierDual
public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.WeilSheaf.TraceFunctionOps
public import WeilConjectures.WeilSheaf.UpperStarComp

/-!
# Duals of the linear Artin–Schreier sheaves

The linear Artin–Schreier sheaf `ℒ_{ψ(a x)}` is the Artin–Schreier sheaf `ℒ_{ψ,f}` of the
function `f = a x` on the line (`AlgebraicGeometry.nonempty_iso_artinSchreier_artinSchreierOf`).
Hence the identities `ℒ_{ψ,0} ≅ ℚ̄_ℓ` and `ℒ_{ψ⁻¹,f} ≅ ℒ_{ψ,-f}` of blueprint
`lem-fd-as-characters` (`AlgebraicGeometry.nonempty_iso_artinSchreierOf_zero`,
`AlgebraicGeometry.nonempty_iso_artinSchreierOf_inv`) give `ℒ_{ψ(0 · x)} ≅ ℚ̄_ℓ` and
`ℒ_{ψ⁻¹(a x)} ≅ ℒ_{ψ(-a x)}`, and with the dual `(ℒ_{ψ(a x)})^∨ ≅ ℒ_{ψ⁻¹(a x)}`
(`AlgebraicGeometry.nonempty_iso_dual_artinSchreier`) also `(ℒ_{ψ(a x)})^∨ ≅ ℒ_{ψ(-a x)}`. On the
geometric line, the double dual of the geometric linear character `ℒ_{ψ⁻¹(b x)}` is the geometric
linear character `ℒ_{ψ(-b x)}`
(`AlgebraicGeometry.exists_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Pullbacks of Weil sheaves along equal morphisms are isomorphic. -/
theorem WeilSheaf.nonempty_iso_upperStar_of_eq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {φ φ' : X ⟶ Y}
    {i : φ.IsOver (Spec (CommRingCat.of k₀))} {i' : φ'.IsOver (Spec (CommRingCat.of k₀))}
    (h : φ = φ') (F : WeilSheaf k₀ l Y) :
    Nonempty ((WeilSheaf.upperStar φ).obj F ≅ (WeilSheaf.upperStar φ').obj F) := by
  subst h
  obtain rfl : i = i' := Subsingleton.elim _ _
  exact ⟨Iso.refl _⟩

/-- The pullback of Weil sheaves along a composite is the composite of the pullbacks. -/
theorem WeilSheaf.nonempty_iso_upperStar_comp {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) (χ : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [χ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Z) :
    Nonempty ((WeilSheaf.upperStar (φ ≫ χ)).obj F ≅
      (WeilSheaf.upperStar φ).obj ((WeilSheaf.upperStar χ).obj F)) :=
  ⟨ObjectProperty.isoMk _ (WeilSheaf.upperStarObjIso (φ ≫ χ) F ≪≫
    (ProEtaleWeilSheaf.upperStarCompIso k₀ l φ χ).app F.obj ≪≫
    (ProEtaleWeilSheaf.upperStar k₀ l φ).mapIso (WeilSheaf.upperStarObjIso χ F).symm ≪≫
    (WeilSheaf.upperStarObjIso φ _).symm)⟩

omit [Finite k₀] in
/-- The function `a x` on the line, as a morphism to the line, followed by `x ↦ 1 · x`, is the
multiplication by `a`. -/
lemma affineLine.homOfSection_comp_smul_one (a : k₀) :
    affineLine.homOfSection k₀ ((affineLine.smul k₀ a).appTop (AffineSpace.coord _ PUnit.unit)) ≫
      affineLine.smul k₀ 1 = affineLine.smul k₀ a := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · simp [affineLine.homOfSection, affineLine.smul]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineLine.smul,
      AffineSpace.smul_appTop_coord]
    simp [affineLine.homOfSection, affineLine.smul]

/-- The linear Artin–Schreier sheaf `ℒ_{ψ(a x)}` is the Artin–Schreier sheaf `ℒ_{ψ,f}` of the
function `f = a x` on the line. -/
theorem nonempty_iso_artinSchreier_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty (artinSchreier ψ a ≅
      artinSchreierOf ψ ((affineLine.smul k₀ a).appTop (AffineSpace.coord _ PUnit.unit))) := by
  obtain ⟨I, hI⟩ : ∃ I : WeilSheaf k₀ l (affineLine k₀), ∀ b : k₀,
      Nonempty (artinSchreier ψ b ≅ (WeilSheaf.upperStar (affineLine.smul k₀ b)).obj I) :=
    ⟨_, fun _ ↦ ⟨Iso.refl _⟩⟩
  have hs := affineLine.homOfSection_comp_smul_one (k₀ := k₀) a
  exact ⟨(hI a).some ≪≫ (WeilSheaf.nonempty_iso_upperStar_of_eq hs.symm I).some ≪≫
    (WeilSheaf.nonempty_iso_upperStar_comp _ _ I).some ≪≫
    (WeilSheaf.upperStar _).mapIso (hI 1).some.symm⟩

/-- `ℒ_{ψ(0 · x)}`, the Artin–Schreier sheaf of the zero function, is the constant Weil sheaf
`ℚ̄_ℓ` (`AlgebraicGeometry.nonempty_iso_artinSchreierOf_zero`). It is the unit of the kernel
family `ℒ_{ψ(a x)}`. -/
theorem nonempty_iso_artinSchreier_zero (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (artinSchreier ψ 0 ≅ WeilSheaf.adicConstant k₀ l (affineLine k₀)) := by
  obtain ⟨e₁⟩ := nonempty_iso_artinSchreier_artinSchreierOf ψ 0
  obtain ⟨e₂⟩ := nonempty_iso_artinSchreierOf_zero (X := affineLine k₀) ψ
  have h : (affineLine.smul k₀ 0).appTop (AffineSpace.coord _ PUnit.unit) = 0 := by
    simp [affineLine.smul]
  rw [h] at e₁
  exact ⟨e₁ ≪≫ e₂⟩

/-- **The inverse character**: `ℒ_{ψ⁻¹(a x)} ≅ ℒ_{ψ(-a x)}`, the clause `ℒ_{ψ⁻¹,f} ≅ ℒ_{ψ,-f}`
(`AlgebraicGeometry.nonempty_iso_artinSchreierOf_inv`) for `f = a x`. -/
theorem nonempty_iso_artinSchreier_inv (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty (artinSchreier ψ⁻¹ a ≅ artinSchreier ψ (-a)) := by
  obtain ⟨e₁⟩ := nonempty_iso_artinSchreier_artinSchreierOf ψ⁻¹ a
  obtain ⟨e₂⟩ := nonempty_iso_artinSchreierOf_inv ψ
    ((affineLine.smul k₀ a).appTop (AffineSpace.coord _ PUnit.unit))
  obtain ⟨e₃⟩ := nonempty_iso_artinSchreier_artinSchreierOf ψ (-a)
  have h : (affineLine.smul k₀ (-a)).appTop (AffineSpace.coord _ PUnit.unit) =
      -(affineLine.smul k₀ a).appTop (AffineSpace.coord _ PUnit.unit) := by
    simp [affineLine.smul]
  rw [h] at e₃
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃.symm⟩

/-- **The inverse of a linear Artin–Schreier sheaf**: `(ℒ_{ψ(a x)})^∨ ≅ ℒ_{ψ⁻¹(a x)} ≅
ℒ_{ψ(-a x)}`. (blueprint: `lem-fd-as-characters`, the clause `(ℒ_{ψ,f})^{-1} ≅ ℒ_{ψ,-f}` for
`f = a x`) -/
theorem nonempty_iso_dual_artinSchreier_neg (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty ((artinSchreier ψ a).dual (isLisse_artinSchreier ψ a) ≅ artinSchreier ψ (-a)) :=
  ⟨(nonempty_iso_dual_artinSchreier ψ a).some ≪≫ (nonempty_iso_artinSchreier_inv ψ a).some⟩

/-- The double dual of the inverse character is `ℒ_{ψ(-x)}`:
`(ℒ_{ψ⁻¹(x)})^∨∨ ≅ (ℒ_{ψ⁻¹(-x)})^∨ ≅ ℒ_{ψ⁻¹(x)} ≅ ℒ_{ψ(-x)}`. -/
theorem nonempty_iso_dual_dual_artinSchreier_inv (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (((artinSchreier ψ⁻¹ 1).dual (isLisse_artinSchreier ψ⁻¹ 1)).dual
      (isLisse_artinSchreier ψ⁻¹ 1).dual ≅ artinSchreier ψ (-1)) := by
  obtain ⟨e₁⟩ := nonempty_iso_dual_artinSchreier_neg ψ⁻¹ 1
  obtain ⟨e₂⟩ := nonempty_iso_dual_artinSchreier_neg ψ⁻¹ (-1)
  obtain ⟨e₃⟩ := nonempty_iso_artinSchreier_inv ψ 1
  rw [neg_neg] at e₂
  exact ⟨WeilSheaf.dualIsoOfIso e₁ _ (isLisse_artinSchreier ψ⁻¹ (-1)) ≪≫ e₂ ≪≫ e₃⟩

/-- **The double dual of a geometric linear character.** For `b ∈ k̄`, the double dual of the
geometric sheaf `ℒ_{ψ⁻¹(b x)}` on `𝔸¹_{k̄}` is a geometric linear character `ℒ_{ψ(a x)}`, namely
for `a = -b`. For `b = 0` both are the constant sheaf; for `b ≠ 0` the multiplication by `b` is
an automorphism, along which pullback commutes with internal homs, and the double dual of
`ℒ_{ψ⁻¹(x)}` is `ℒ_{ψ(-x)}`. -/
theorem nonempty_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : AlgebraicClosure k₀) :
    Nonempty
      ((ProEtale.AdicSheaf.ihom ((ProEtale.AdicSheaf.ihom
          ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj (artinSchreier ψ⁻¹ 1).obj.carrier)).obj
            (ProEtale.AdicSheaf.unit l _))).obj (ProEtale.AdicSheaf.unit l _) ≅
        (affineLine.geometricSMul k₀ (-b))^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) := by
  rcases eq_or_ne b 0 with rfl | hb
  · obtain ⟨e₁⟩ := WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l)
      ψ⁻¹ 1
    obtain ⟨e₂⟩ := WeilSheaf.nonempty_iso_upperStar_geometricSMul_zero_artinSchreier (l := l)
      ψ 1
    rw [neg_zero]
    refine ⟨?_⟩
    set U := ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
    have e₃ : (ProEtale.AdicSheaf.ihom ((affineLine.geometricSMul k₀ 0)^*ᵃ[l].obj
        (artinSchreier ψ⁻¹ 1).obj.carrier)).obj U ≅ U :=
      (Mod.ihomMapIso e₁).symm.app U ≪≫ Mod.ihomRegularIso.app U
    exact (Mod.ihomMapIso e₃).symm.app U ≪≫ Mod.ihomRegularIso.app U ≪≫ e₂.symm
  · have := affineLine.isIso_geometricSMul k₀ hb
    set g := affineLine.geometricSMul k₀ b
    have : WeaklyEtale g := MorphismProperty.of_isIso _ g
    set U := ProEtale.AdicSheaf.unit l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
    -- pullback along the automorphism `g` commutes with `𝓗om(-, ℚ̄_ℓ)`
    have eD (S : ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
        (ProEtale.AdicSheaf.ihom ((g)^*ᵃ[l].obj S)).obj U ≅
          (g)^*ᵃ[l].obj ((ProEtale.AdicSheaf.ihom S).obj U) :=
      (ProEtale.AdicSheaf.ihom _).mapIso (ProEtale.adicUpperStarUnitIso l g).symm ≪≫
        ((ProEtale.adicUpperStarIhomIso l g S).app U).symm
    obtain ⟨eW⟩ := nonempty_iso_dual_dual_artinSchreier_inv (l := l) ψ
    have hs : g ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1))
        (comp_over (affineLine.smul k₀ (-1)) _) =
          affineLine.geometricSMul k₀ (-b) ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ 1)
            (comp_over (affineLine.smul k₀ 1) _) := by
      rw [affineLine.geometricSMul_comp_geometricFiberMap_smul,
        affineLine.geometricSMul_comp_geometricFiberMap_smul]
      simp
    refine ⟨?_⟩
    exact (Mod.ihomMapIso (eD _)).symm.app U ≪≫ eD _ ≪≫
      (g)^*ᵃ[l].mapIso ((WeilSheaf.carrierFunctor k₀ l _).mapIso eW) ≪≫
      (ProEtale.adicUpperStarCompIso l hs).app _

/-- The double dual of the geometric sheaf `ℒ_{ψ⁻¹(b x)}` on `𝔸¹_{k̄}` is a geometric linear
character `ℒ_{ψ(a x)}`
(`AlgebraicGeometry.nonempty_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv`). -/
theorem exists_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : AlgebraicClosure k₀) :
    ∃ a : AlgebraicClosure k₀, Nonempty
      ((ProEtale.AdicSheaf.ihom ((ProEtale.AdicSheaf.ihom
          ((affineLine.geometricSMul k₀ b)^*ᵃ[l].obj (artinSchreier ψ⁻¹ 1).obj.carrier)).obj
            (ProEtale.AdicSheaf.unit l _))).obj (ProEtale.AdicSheaf.unit l _) ≅
        (affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier) :=
  ⟨-b, nonempty_iso_ihom_ihom_upperStar_geometricSMul_artinSchreier_inv ψ b⟩

end AlgebraicGeometry
