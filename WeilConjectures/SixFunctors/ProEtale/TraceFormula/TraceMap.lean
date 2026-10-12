/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass

/-!
# The trace map of external duality and the Verdier trace class

For an endocorrespondence `(C, c, u)` on `(X, K)` with fixed scheme `F = Fix(c)`, external
duality `H_c(K) ≃ Rc^! (K ⊠ D_X K)`, the evaluation kernel `K ⊠ D_X K ⟶ RΔ_* ω_X` and the
right-adjoint form `Rc^! RΔ_* ≃ Ri_{F*} Rd^!` of base change in the fixed square give the
trace map `𝔱_{c,K} : H_c(K) ⟶ Ri_{F*} ω_F`. Applied to the mate `ũ : A_C ⟶ H_c(K)` of the
coefficient map it gives the Verdier trace class `Tr_c(u) : A_F ⟶ ω_F`.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricOperations.evaluationKernel`: `δ_K : K ⊠ D_X K ⟶ RΔ_* ω_X`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.traceMap`: the trace map `𝔱_{c,K}`
  (blueprint `lem-trf-trace-map-from-external-duality`).
- `AlgebraicGeometry.ProEtale.Correspondence.verdierTraceClass`: the Verdier trace class
  (blueprint `def-trf-trace-class`).
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {s : Scheme.{u}}

namespace GeometricOperations

variable [DerivedBraiding A] (G : GeometricOperations A s)
section EvaluationKernel

variable {X Z : Scheme.{u}} {aX : X ⟶ s} [IsGeometric aX] {p₁ p₂ : Z ⟶ X} (δ : X ⟶ Z)
  (h₁ : δ ≫ p₁ = 𝟙 X) (h₂ : δ ≫ p₂ = 𝟙 X)
  (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))

/-- The evaluation kernel `δ_K : K ⊠ D_X K ⟶ Rδ_* ω_X` on `Z = X ×_s X` with diagonal `δ`
(sections `δ ≫ p₁ = δ ≫ p₂ = 𝟙`): the adjoint under `Lδ^* ⊣ Rδ_*` of

```
  Lδ^* (Lp₁^* K ⊗ᴸ Lp₂^* D_X K) ≃ Lδ^* Lp₁^* K ⊗ᴸ Lδ^* Lp₂^* D_X K ≃ K ⊗ᴸ D_X K ──ev──▶ ω_X
```

(part of blueprint `def-trf-kernel-pushforward-maps` (6),
`lem-trf-trace-map-from-external-duality`). -/
noncomputable def evaluationKernel :
    ((upperStar A p₁).leftDerivedFunctor).obj K ⊗
        ((upperStar A p₂).leftDerivedFunctor).obj (G.verdierDual aX K) ⟶
      ((lowerStar A δ).rightDerivedFunctor).obj (G.dualizing aX) :=
  (derivedUpperStarLowerStarAdjunction A δ).homEquiv _ _
    ((G.upperStarTensor δ _ _).hom ≫
      ((leftDerivedUpperStarCompIso δ h₁ K ≪≫ (leftDerivedUpperStarId A X).app K).hom ⊗ₘ
        (leftDerivedUpperStarCompIso δ h₂ _ ≪≫ (leftDerivedUpperStarId A X).app _).hom) ≫
      (ihom.ev K).app (G.dualizing aX))

end EvaluationKernel

section TraceMap

variable {F C X Z : Scheme.{u}} {aX : X ⟶ s} [IsGeometric aX] [HasCompactification aX]
  [QuasiCompact aX] [s.IsSpecOfField] {p₁ p₂ : Z ⟶ X} (sq : IsPullback p₁ p₂ aX aX)
  [IsGeometric (p₁ ≫ aX)] [HasCompactification p₁] {δ : X ⟶ Z} (h₁ : δ ≫ p₁ = 𝟙 X)
  (h₂ : δ ≫ p₂ = 𝟙 X) (hδ : IsGeometricHom s δ) [IsProper δ] {c : C ⟶ Z}
  (hc : IsGeometricHom s c) [HasCompactification c] {c₁ c₂ : C ⟶ X} [HasCompactification c₁]
  (hc₁ : c ≫ p₁ = c₁) (hc₂ : c ≫ p₂ = c₂) [HasCompactification (c ≫ p₁)] {i : F ⟶ C}
  {d : F ⟶ X} (fsq : IsPullback i d c δ) (hd : IsGeometricHom s d) (hi : IsGeometricHom s i)
  [HasCompactification d] [IsProper i] [IsGeometric (d ≫ aX)]
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)

/-- Blueprint `lem-trf-trace-map-from-external-duality`: the trace map
`𝔱_{c,K} : H_c(K) ⟶ Ri_* ω_F` of an endocorrespondence over a Cartesian square `Z = X ×_s X`
with diagonal `δ` and Cartesian fixed square `F = C ×_Z X`, the composite

```
  H_c(K) = RHom(Lc₂^* K, Rc₁^! K) ≃ Rc^! (K ⊠ D_X K) ──Rc^! δ_K──▶ Rc^! Rδ_* ω_X
      ≃ Ri_* Rd^! ω_X ≃ Ri_* ω_F
```

of external duality, the evaluation kernel, the right-adjoint form of base change in the fixed
square and the dualizing composition. Its effect on global sections
`RΓ(C, H_c(K)) ⟶ RΓ(F, ω_F)` is `GeometricOperations.verdierTraceClassOf`. -/
noncomputable def traceMap :
    (ihom (((upperStar A c₂).leftDerivedFunctor).obj K)).obj
        ((rightDerivedUpperShriek A c₁).obj K) ⟶
      ((lowerStar A i).rightDerivedFunctor).obj (G.dualizing (d ≫ aX)) :=
  (G.externalDualityIso c hc sq hc₁ hc₂ hK).hom ≫
    (rightDerivedUpperShriek A c).map (G.evaluationKernel δ h₁ h₂ K) ≫
    ((G.baseChangeRightAdjoint fsq hc hδ hd hi).hom.app
      ⟨G.dualizing aX, G.ctf_dualizing aX⟩).hom ≫
    ((lowerStar A i).rightDerivedFunctor).map (G.dualizingComp d aX).hom

/-- The Verdier trace class attached to a section `ũ : A_C ⟶ H_c(K)` (the mate of a coefficient
map): the adjoint under `Li^* ⊣ Ri_*` of `ũ ≫ 𝔱_{c,K} : A_C ⟶ Ri_* ω_F`, read through
`Li^* A_C ≃ A_F` (blueprint `def-trf-trace-class`). -/
noncomputable def verdierTraceClassOf
    (ũ : 𝟙_ _ ⟶ (ihom (((upperStar A c₂).leftDerivedFunctor).obj K)).obj
      ((rightDerivedUpperShriek A c₁).obj K)) :
    𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology F) A)) ⟶ G.dualizing (d ≫ aX) :=
  (G.upperStarUnit i).inv ≫
    ((derivedUpperStarLowerStarAdjunction A i).homEquiv _ _).symm
      (ũ ≫ G.traceMap sq h₁ h₂ hδ hc hc₁ hc₂ fsq hd hi hK)

end TraceMap

end GeometricOperations

namespace Correspondence

variable [DerivedBraiding A] (G : GeometricOperations A s) {X : Scheme.{u}} {aX : X ⟶ s}
  [IsGeometric aX] [HasCompactification aX] [QuasiCompact aX] [s.IsSpecOfField]
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)
  (c : Correspondence aX aX K K) [IsGeometric c.str] [HasCompactification c.toProd]
  [HasCompactification (pullback.fst aX aX)]

/-- Blueprint `def-trf-trace-class`: the *Verdier trace class* `Tr_c(u) : A_F ⟶ ω_F` of an
endocorrespondence on the fixed scheme `F = Fix(c)`: the mate `ũ : A_C ⟶ H_c(K)` of the
coefficient map followed by the trace map `𝔱_{c,K}` of external duality, read on `F` through
the adjunction `Li_F^* ⊣ Ri_{F*}` (`GeometricOperations.verdierTraceClassOf`). -/
noncomputable def verdierTraceClass : G.borelMooreSections c.fixStr :=
  haveI : IsGeometric ((c.fixι ≫ c.fst) ≫ aX) :=
    IsGeometric.of_eq (a := c.fixStr) (by simp [fixStr, c.fst_comp])
  G.verdierTraceClassOf (IsPullback.of_hasPullback aX aX) (pullback.diagonal_fst aX)
    (pullback.diagonal_snd aX) (.mk (aX := aX) (aY := pullback.fst aX aX ≫ aX) (by simp))
    c.isGeometricHom_toProd c.toProd_fst c.toProd_snd c.isPullback_fixι_toProd
    (.mk (aX := c.fixStr) (aY := aX) (by simp [fixStr, c.fst_comp]))
    (.mk (aX := c.fixStr) (aY := c.str) rfl) hK c.mate ≫
    (G.dualizingCongr (by simp [fixStr, c.fst_comp])).hom

end Correspondence

end AlgebraicGeometry.ProEtale
