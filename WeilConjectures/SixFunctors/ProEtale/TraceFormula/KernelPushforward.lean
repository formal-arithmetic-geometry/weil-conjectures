/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward

/-!
# The kernel pushforward maps

For a proper morphism `f : X ⟶ Y` of geometric schemes and `K ∈ Dᵇctf(X)` with
`K' = Rf_* K`, this file builds the maps of blueprint `def-trf-kernel-pushforward-maps` which
compare the kernels `P_X = K ⊠ D_X K` on `X ×_s X` and `P_Y = K' ⊠ D_Y K'` on `Y ×_s Y` along
`q = f × f`, together with the kernel class, the support isomorphisms and the exchange
transformation used in the proof of proper pushforward compatibility.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricOperations.externalKernel`: the kernel
  `P_X = K ⊠ D_X K` (item 1).
- `AlgebraicGeometry.ProEtale.GeometricOperations.pushforwardTrace`: the trace
  `τ_f : Rf_* ω_X ⟶ ω_Y` (item 2).
- `AlgebraicGeometry.ProEtale.GeometricOperations.lowerStarTensorMap`: the multiplication
  `μ_f : Rf_* M ⊗ᴸ Rf_* N ⟶ Rf_* (M ⊗ᴸ N)` (item 3).
- `AlgebraicGeometry.ProEtale.GeometricOperations.lowerStarVerdierDualMap`: the dual
  pushforward `χ_f : Rf_* D_X K ⟶ D_Y K'` (item 4).
- `AlgebraicGeometry.ProEtale.GeometricOperations.lowerStarKunnethIso`: the `!`-Künneth
  isomorphism `Π_f : Rf_* M ⊠ Rf_* N ≃ Rq_* (M ⊠ N)`, and
  `AlgebraicGeometry.ProEtale.GeometricOperations.kernelPushforward`: the kernel pushforward
  `ρ_f : Rq_* P_X ⟶ P_Y` (item 5).
- `AlgebraicGeometry.ProEtale.GeometricOperations.kernelClassOf`,
  `AlgebraicGeometry.ProEtale.Correspondence.kernelClass`: the kernel class
  `[u]_P : Rc_! A_C ⟶ P_X` (item 7).
- `AlgebraicGeometry.ProEtale.GeometricOperations.supportIso`: the support isomorphism
  `ζ_c : Ri_* ω_F ≃ Rc^! RΔ_* ω_X` (item 8).
- `AlgebraicGeometry.ProEtale.GeometricOperations.lowerStarLowerShriekCompIso`: the
  composition `Ξ : Rb_! Rg_* ≃ Rq_* Rc_!`, and
  `AlgebraicGeometry.ProEtale.GeometricOperations.lowerStarUpperShriekExchange`: the exchange
  `𝖤 : Rg_* Rc^! ⟶ Rb^! Rq_*` (item 9), and
  `AlgebraicGeometry.ProEtale.ProperPushforwardDiagram.lowerStarUpperShriekExchange`: the
  exchange for the support square `b ∘ g = q ∘ c` of a proper pushforward diagram, with
  `q = ProperPushforwardDiagram.prodMap`.

The evaluation kernels `δ_K`, `δ_{K'}` of item 6 are
`AlgebraicGeometry.ProEtale.GeometricOperations.evaluationKernel`.

## Implementation notes

All constructions are stated for arbitrary Cartesian squares and arbitrary morphisms `q`
with the relevant equations rather than on the literal fibre products, as the kernel checks
of composites over `pullback aX aX` are very slow. The `!`-Künneth isomorphism is built from
a factorisation `q = q₁ ≫ q₂` of `q = f × f` through `W = Y ×_s X` into two base changes of
`f`, using `!`-base change, the projection formula and `lowerShriekComp`.
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

/-- The kernel `P_X = K ⊠ D_X K = Lp₁^* K ⊗ᴸ Lp₂^* D_X K` on `Z = X ×_s X` with projections
`p₁`, `p₂` (blueprint `def-trf-kernel-pushforward-maps` (1); the kernel `P_Y` is the same
construction for `K' = Rf_* K` on `Y ×_s Y`). -/
noncomputable abbrev externalKernel {X Z : Scheme.{u}} (p₁ p₂ : Z ⟶ X) (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) :=
  ((upperStar A p₁).leftDerivedFunctor).obj K ⊗
    ((upperStar A p₂).leftDerivedFunctor).obj (G.verdierDual aX K)

section Pushforward

variable {X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s} [IsGeometric aX] [IsGeometric aY]
  {f : X ⟶ Y} (hf : f ≫ aY = aX) [HasCompactification f] [IsProper f]

/-- The trace along a proper morphism `f : X ⟶ Y` of geometric schemes over `s`: the
composite

```
  τ_f : Rf_* ω_X ≃ Rf_! ω_X ≃ Rf_! f^! ω_Y ──ε──▶ ω_Y
```

of `properComparison`, the dualizing composition `f^! ω_Y ≃ ω_X` and the counit of the
exceptional adjunction (blueprint `def-trf-kernel-pushforward-maps` (2); the trace `τ_h` along
the induced map on fixed schemes is the same construction). -/
noncomputable def pushforwardTrace :
    ((lowerStar A f).rightDerivedFunctor).obj (G.dualizing aX) ⟶ G.dualizing aY :=
  haveI : IsGeometric (f ≫ aY) := IsGeometric.of_eq hf.symm
  ((G.properComparison f (.mk hf)).inv.app ⟨G.dualizing aX, G.ctf_dualizing aX⟩).hom ≫
    (rightDerivedLowerShriek A f).map ((G.dualizingCongr hf).inv ≫ (G.dualizingComp f aY).inv) ≫
    G.exceptionalCounit f (.mk hf) (G.dualizing aY) (G.ctf_dualizing aY)

/-- The multiplication `μ_f : Rf_* M ⊗ᴸ Rf_* N ⟶ Rf_* (M ⊗ᴸ N)` of the direct image along a
morphism `f : X ⟶ Y`: the adjoint under `Lf^* ⊣ Rf_*` of

```
  Lf^* (Rf_* M ⊗ᴸ Rf_* N) ≃ Lf^* Rf_* M ⊗ᴸ Lf^* Rf_* N ──ε ⊗ ε──▶ M ⊗ᴸ N
```

(blueprint `def-trf-kernel-pushforward-maps` (3)). -/
noncomputable def lowerStarTensorMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((lowerStar A f).rightDerivedFunctor).obj M ⊗ ((lowerStar A f).rightDerivedFunctor).obj N ⟶
      ((lowerStar A f).rightDerivedFunctor).obj (M ⊗ N) :=
  (derivedUpperStarLowerStarAdjunction A f).homEquiv _ _
    ((G.upperStarTensor f _ _).hom ≫
      ((derivedUpperStarLowerStarAdjunction A f).counit.app M ⊗ₘ
        (derivedUpperStarLowerStarAdjunction A f).counit.app N))

/-- The dual pushforward `χ_f : Rf_* D_X K ⟶ D_Y (Rf_* K)` along a proper morphism `f` of
geometric schemes: the tensor-hom adjoint of

```
  Rf_* K ⊗ᴸ Rf_* D_X K ──μ_f──▶ Rf_* (K ⊗ᴸ D_X K) ──Rf_* ev──▶ Rf_* ω_X ──τ_f──▶ ω_Y
```

(blueprint `def-trf-kernel-pushforward-maps` (4)). -/
noncomputable def lowerStarVerdierDualMap
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((lowerStar A f).rightDerivedFunctor).obj (G.verdierDual aX K) ⟶
      G.verdierDual aY (((lowerStar A f).rightDerivedFunctor).obj K) :=
  curry (G.lowerStarTensorMap f K (G.verdierDual aX K) ≫
    ((lowerStar A f).rightDerivedFunctor).map ((ihom.ev K).app (G.dualizing aX)) ≫
    G.pushforwardTrace hf)

end Pushforward

section BaseChangeProjection

variable {X' X Y' Y T : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) (hf : IsGeometricHom s f) (hg : IsGeometricHom s g)
  (hf' : IsGeometricHom s f') (hg' : IsGeometricHom s g') [HasCompactification f]
  [HasCompactification f'] {v : Y' ⟶ T} {t : X' ⟶ T} (hv : IsGeometricHom s v)
  (hvt : f' ≫ v = t) {M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  (hM : G.ctf X M) {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)} (hN : G.ctf T N)

/-- `!`-base change combined with the projection formula: for a Cartesian square
`X' = X ×_Y Y'` with projections `g' : X' ⟶ X`, `f' : X' ⟶ Y'` and `t = f' ≫ v`,

```
  Rf'_! (Lg'^* M ⊗ᴸ Lt^* N) ≃ Rf'_! (Lg'^* M ⊗ᴸ Lf'^* Lv^* N) ≃ Rf'_! Lg'^* M ⊗ᴸ Lv^* N
      ≃ Lg^* Rf_! M ⊗ᴸ Lv^* N
```

(part of blueprint `def-trf-kernel-pushforward-maps` (5)). -/
noncomputable def lowerShriekTensorUpperStarIso :
    (rightDerivedLowerShriek A f').obj (((upperStar A g').leftDerivedFunctor).obj M ⊗
        ((upperStar A t).leftDerivedFunctor).obj N) ≅
      ((upperStar A g).leftDerivedFunctor).obj ((rightDerivedLowerShriek A f).obj M) ⊗
        ((upperStar A v).leftDerivedFunctor).obj N :=
  (rightDerivedLowerShriek A f').mapIso
      (whiskerLeftIso _ (leftDerivedUpperStarCompIso f' hvt N).symm) ≪≫
    ((G.projectionFormula f' hf').app
      (⟨_, G.ctf_upperStar g' hg' hM⟩, ⟨_, G.ctf_upperStar v hv hN⟩)).symm ≪≫
    whiskerRightIso ((G.ctf Y').ι.mapIso ((G.baseChange sq hf hg hf' hg').app ⟨M, hM⟩)).symm _

end BaseChangeProjection

section Kunneth

/- The square `q = f × f : Z_X = X ×_s X ⟶ Z_Y = Y ×_s Y`, factored as
`q₁ = f × 𝟙 : Z_X ⟶ W = Y ×_s X` followed by `q₂ = 𝟙 × f : W ⟶ Z_Y`, both base changes of
`f`. -/
variable {X Y ZX ZY W : Scheme.{u}} {p₁ p₂ : ZX ⟶ X} {r₁ r₂ : ZY ⟶ Y} {w₁ : W ⟶ Y}
  {w₂ : W ⟶ X} {f : X ⟶ Y} {q₁ : ZX ⟶ W} {q₂ : W ⟶ ZY} {q : ZX ⟶ ZY}
  (sq₁ : IsPullback p₁ q₁ f w₁) (sq₂ : IsPullback w₂ q₂ f r₂) (hw₂ : q₁ ≫ w₂ = p₂)
  (hr₁ : q₂ ≫ r₁ = w₁) (hq : q₁ ≫ q₂ = q) (hf : IsGeometricHom s f)
  (hp₁ : IsGeometricHom s p₁) (hp₂ : IsGeometricHom s p₂) (hq₁ : IsGeometricHom s q₁)
  (hq₂ : IsGeometricHom s q₂) (hq' : IsGeometricHom s q) (hw₁ : IsGeometricHom s w₁)
  (hw₂' : IsGeometricHom s w₂) (hr₁' : IsGeometricHom s r₁) (hr₂ : IsGeometricHom s r₂)
  [HasCompactification f] [HasCompactification q₁] [HasCompactification q₂]
  [HasCompactification q] {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  (hK : G.ctf X K) {L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hL : G.ctf X L)

/-- The `!`-Künneth isomorphism `Rq_! (K ⊠ L) ≃ Rf_! K ⊠ Rf_! L` for `q = f × f`, along a
factorisation `q = q₁ ≫ q₂` into the base changes `q₁ = f × 𝟙` and `q₂ = 𝟙 × f` of `f`:

```
  Rq_! (Lp₁^* K ⊗ᴸ Lp₂^* L) ≃ Rq₂_! Rq₁_! (Lp₁^* K ⊗ᴸ Lp₂^* L)
      ≃ Rq₂_! (Lw₁^* Rf_! K ⊗ᴸ Lw₂^* L) ≃ Rq₂_! (Lw₂^* L ⊗ᴸ Lw₁^* Rf_! K)
      ≃ Lr₂^* Rf_! L ⊗ᴸ Lr₁^* Rf_! K ≃ Lr₁^* Rf_! K ⊗ᴸ Lr₂^* Rf_! L
```

of `lowerShriekComp`, `!`-base change with the projection formula
(`lowerShriekTensorUpperStarIso`) for both squares, and the braiding
(part of blueprint `def-trf-kernel-pushforward-maps` (5)). -/
noncomputable def lowerShriekKunnethIso :
    (rightDerivedLowerShriek A q).obj (((upperStar A p₁).leftDerivedFunctor).obj K ⊗
        ((upperStar A p₂).leftDerivedFunctor).obj L) ≅
      ((upperStar A r₁).leftDerivedFunctor).obj ((rightDerivedLowerShriek A f).obj K) ⊗
        ((upperStar A r₂).leftDerivedFunctor).obj ((rightDerivedLowerShriek A f).obj L) :=
  haveI : HasCompactification (q₁ ≫ q₂) := .of_eq hq.symm
  have hP : G.ctf ZX (((upperStar A p₁).leftDerivedFunctor).obj K ⊗
      ((upperStar A p₂).leftDerivedFunctor).obj L) :=
    G.ctf_tensor hp₁.id_source (G.ctf_upperStar p₁ hp₁ hK) (G.ctf_upperStar p₂ hp₂ hL)
  (G.ctf ZY).ι.mapIso ((ctfLowerShriekCongr hq (fun _ hM ↦ G.ctf_lowerShriek _ (hq₁.comp hq₂) hM)
      (fun _ hM ↦ G.ctf_lowerShriek _ hq' hM)).app ⟨_, hP⟩).symm ≪≫
    (G.ctf ZY).ι.mapIso ((G.lowerShriekComp q₁ q₂ hq₁ hq₂ (hq₁.comp hq₂)).app ⟨_, hP⟩).symm ≪≫
    (rightDerivedLowerShriek A q₂).mapIso
      (G.lowerShriekTensorUpperStarIso sq₁ hf hw₁ hq₁ hp₁ hw₂' hw₂ hK hL ≪≫ β_ _ _) ≪≫
    G.lowerShriekTensorUpperStarIso sq₂ hf hr₂ hq₂ hw₂' hr₁' hr₁ hL
      (G.ctf_lowerShriek f hf hK) ≪≫ β_ _ _

variable [IsProper f] [IsProper q]

/-- The `!`-Künneth isomorphism `Π : Rf_* K ⊠ Rf_* L ≃ Rq_* (K ⊠ L)` for a proper `f` and
`q = f × f`: `lowerShriekKunnethIso` read through `properComparison` for `f` and `q`
(blueprint `def-trf-kernel-pushforward-maps` (5), at `L = D_X K`). -/
noncomputable def lowerStarKunnethIso :
    ((upperStar A r₁).leftDerivedFunctor).obj (((lowerStar A f).rightDerivedFunctor).obj K) ⊗
        ((upperStar A r₂).leftDerivedFunctor).obj
          (((lowerStar A f).rightDerivedFunctor).obj L) ≅
      ((lowerStar A q).rightDerivedFunctor).obj (((upperStar A p₁).leftDerivedFunctor).obj K ⊗
        ((upperStar A p₂).leftDerivedFunctor).obj L) :=
  have hP : G.ctf ZX (((upperStar A p₁).leftDerivedFunctor).obj K ⊗
      ((upperStar A p₂).leftDerivedFunctor).obj L) :=
    G.ctf_tensor hp₁.id_source (G.ctf_upperStar p₁ hp₁ hK) (G.ctf_upperStar p₂ hp₂ hL)
  tensorIso
      (((upperStar A r₁).leftDerivedFunctor).mapIso
        ((G.ctf Y).ι.mapIso ((G.properComparison f hf).app ⟨K, hK⟩)).symm)
      (((upperStar A r₂).leftDerivedFunctor).mapIso
        ((G.ctf Y).ι.mapIso ((G.properComparison f hf).app ⟨L, hL⟩)).symm) ≪≫
    (G.lowerShriekKunnethIso sq₁ sq₂ hw₂ hr₁ hq hf hp₁ hp₂ hq₁ hq₂ hq' hw₁ hw₂' hr₁' hr₂ hK
      hL).symm ≪≫
    (G.ctf ZY).ι.mapIso ((G.properComparison q hq').app ⟨_, hP⟩)

variable {aX : X ⟶ s} {aY : Y ⟶ s} [IsGeometric aX] [IsGeometric aY] (hfa : f ≫ aY = aX)

/-- The kernel pushforward `ρ_f : Rq_* P_X ⟶ P_Y` for `q = f × f`, `P_X = K ⊠ D_X K` and
`P_Y = K' ⊠ D_Y K'` with `K' = Rf_* K`: the composite

```
  Rq_* (K ⊠ D_X K) ≃ K' ⊠ Rf_* D_X K ──𝟙 ⊠ χ_f──▶ K' ⊠ D_Y K'
```

of the inverse of the `!`-Künneth isomorphism `lowerStarKunnethIso` and the dual pushforward
`lowerStarVerdierDualMap` (blueprint `def-trf-kernel-pushforward-maps` (5)). -/
noncomputable def kernelPushforward :
    ((lowerStar A q).rightDerivedFunctor).obj (G.externalKernel p₁ p₂ aX K) ⟶
      G.externalKernel r₁ r₂ aY (((lowerStar A f).rightDerivedFunctor).obj K) :=
  (G.lowerStarKunnethIso sq₁ sq₂ hw₂ hr₁ hq hf hp₁ hp₂ hq₁ hq₂ hq' hw₁ hw₂' hr₁' hr₂ hK
      (G.ctf_ihom hf.id_source hK (G.ctf_dualizing aX))).inv ≫
    (_ ◁ ((upperStar A r₂).leftDerivedFunctor).map (G.lowerStarVerdierDualMap hfa K))

end Kunneth

section KernelClass

variable {C X Z : Scheme.{u}} {aX : X ⟶ s} [IsGeometric aX] [HasCompactification aX]
  [QuasiCompact aX] [s.IsSpecOfField] {p₁ p₂ : Z ⟶ X} (sq : IsPullback p₁ p₂ aX aX)
  [IsGeometric (p₁ ≫ aX)] [HasCompactification p₁] {c : C ⟶ Z} (hc : IsGeometricHom s c)
  [HasCompactification c] {c₁ c₂ : C ⟶ X} [HasCompactification c₁] (hc₁ : c ≫ p₁ = c₁)
  (hc₂ : c ≫ p₂ = c₂) [HasCompactification (c ≫ p₁)]
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)

/-- The kernel class `[u]_P : Rc_! A_C ⟶ P_X` attached to a section `ũ : A_C ⟶ H_c(K)` (the
mate of a coefficient map), over a Cartesian square `Z = X ×_s X`: the exceptional adjoint of

```
  A_C ──ũ──▶ H_c(K) ≃ Rc^! (K ⊠ D_X K)
```

for the external duality isomorphism `externalDualityIso`
(blueprint `def-trf-kernel-pushforward-maps` (7)). -/
noncomputable def kernelClassOf
    (ũ : 𝟙_ _ ⟶ (ihom (((upperStar A c₂).leftDerivedFunctor).obj K)).obj
      ((rightDerivedUpperShriek A c₁).obj K)) :
    (rightDerivedLowerShriek A c).obj (𝟙_ _) ⟶ G.externalKernel p₁ p₂ aX K :=
  have hp₁ : IsGeometricHom s p₁ := .mk (aY := aX) rfl
  have hp₂ : IsGeometricHom s p₂ := .mk (aX := p₁ ≫ aX) (aY := aX) sq.w.symm
  (G.exceptionalHomEquiv c hc (G.ctf_unit hc.id_source)
    (G.ctf_tensor hp₁.id_source (G.ctf_upperStar p₁ hp₁ hK)
      (G.ctf_upperStar p₂ hp₂ (G.ctf_ihom hp₁.id_target hK (G.ctf_dualizing aX))))).symm
    (ũ ≫ (G.externalDualityIso c hc sq hc₁ hc₂ hK).hom)

end KernelClass

section SupportIso

variable {F C X Z : Scheme.{u}} {aX : X ⟶ s} [IsGeometric aX] {i : F ⟶ C} {d : F ⟶ X}
  {c : C ⟶ Z} {δ : X ⟶ Z} (fsq : IsPullback i d c δ) (hc : IsGeometricHom s c)
  (hδ : IsGeometricHom s δ) (hd : IsGeometricHom s d) (hi : IsGeometricHom s i)
  [HasCompactification c] [HasCompactification d] [IsProper δ] [IsProper i]
  [IsGeometric (d ≫ aX)]

/-- The support isomorphism `ζ_c : Ri_* ω_F ≃ Rc^! Rδ_* ω_X` of a Cartesian square
`F = C ×_Z X` with `δ` and `i` proper: the inverse of

```
  Rc^! Rδ_* ω_X ≃ Ri_* Rd^! ω_X ≃ Ri_* ω_F
```

of the right-adjoint form `baseChangeRightAdjoint` of base change and the dualizing
composition (blueprint `def-trf-kernel-pushforward-maps` (8); `ζ_b` is the same construction
for the target correspondence). -/
noncomputable def supportIso :
    ((lowerStar A i).rightDerivedFunctor).obj (G.dualizing (d ≫ aX)) ≅
      (rightDerivedUpperShriek A c).obj
        (((lowerStar A δ).rightDerivedFunctor).obj (G.dualizing aX)) :=
  (((lowerStar A i).rightDerivedFunctor).mapIso (G.dualizingComp d aX)).symm ≪≫
    ((G.ctf C).ι.mapIso ((G.baseChangeRightAdjoint fsq hc hδ hd hi).app
      ⟨G.dualizing aX, G.ctf_dualizing aX⟩)).symm

end SupportIso

section Exchange

variable {C D ZX ZY : Scheme.{u}} {c : C ⟶ ZX} {g : C ⟶ D} {b : D ⟶ ZY} {q : ZX ⟶ ZY}
  (w : g ≫ b = c ≫ q) (hc : IsGeometricHom s c) (hg : IsGeometricHom s g)
  (hb : IsGeometricHom s b) (hq : IsGeometricHom s q) [HasCompactification c]
  [HasCompactification b] [IsProper g] [IsProper q] [HasCompactification (g ≫ b)]
  [HasCompactification (c ≫ q)]

/-- The composition isomorphism `Ξ : Rb_! Rg_* ≃ Rq_* Rc_!` on `Dᵇctf(C)` for a commutative
square `b ∘ g = q ∘ c` with `g` and `q` proper: the composite

```
  Rb_! Rg_* ≃ Rb_! Rg_! ≃ R(g ≫ b)_! = R(c ≫ q)_! ≃ Rq_! Rc_! ≃ Rq_* Rc_!
```

of `properComparison` and `lowerShriekComp` (blueprint `def-trf-kernel-pushforward-maps`
(9)). -/
noncomputable def lowerStarLowerShriekCompIso :
    G.lowerStarCtf g hg ⋙ G.lowerShriekCtf b hb ≅ G.lowerShriekCtf c hc ⋙ G.lowerStarCtf q hq :=
  Functor.isoWhiskerRight (G.properComparison g hg).symm _ ≪≫
    G.lowerShriekComp g b hg hb (hg.comp hb) ≪≫ ctfLowerShriekCongr w _ _ ≪≫
    (G.lowerShriekComp c q hc hq (hc.comp hq)).symm ≪≫
    Functor.isoWhiskerLeft _ (G.properComparison q hq)

/-- The exchange transformation `𝖤 : Rg_* Rc^! ⟶ Rb^! Rq_*` on `Dᵇctf(Z_X)` for a
commutative square `b ∘ g = q ∘ c` with `g` and `q` proper: the exceptional adjoint of

```
  Rb_! Rg_* Rc^! ≃ Rq_* Rc_! Rc^! ──Rq_* ε──▶ Rq_*,
```

that is, the mate of `lowerStarLowerShriekCompIso` along the exceptional adjunctions of `c`
and `b` (blueprint `def-trf-kernel-pushforward-maps` (9)). -/
noncomputable def lowerStarUpperShriekExchange :
    G.upperShriekCtf c hc ⋙ G.lowerStarCtf g hg ⟶ G.lowerStarCtf q hq ⋙ G.upperShriekCtf b hb :=
  (mateEquiv (G.exceptionalAdjunction c hc) (G.exceptionalAdjunction b hb)
    (G.lowerStarLowerShriekCompIso w hc hg hb hq).hom).natTrans

end Exchange

end GeometricOperations

namespace Correspondence

variable [DerivedBraiding A] (G : GeometricOperations A s) {X : Scheme.{u}} {aX : X ⟶ s}
  [IsGeometric aX] [HasCompactification aX] [QuasiCompact aX] [s.IsSpecOfField]
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)
  (c : Correspondence aX aX K K) [IsGeometric c.str] [HasCompactification c.toProd]
  [HasCompactification (pullback.fst aX aX)]

/-- The kernel class `[u]_P : Rc_! A_C ⟶ K ⊠ D_X K` of an endocorrespondence on
`X ×_s X`: `GeometricOperations.kernelClassOf` at the mate `ũ` of the coefficient map
(blueprint `def-trf-kernel-pushforward-maps` (7)). -/
noncomputable def kernelClass :
    (rightDerivedLowerShriek A c.toProd).obj (𝟙_ _) ⟶
      G.externalKernel (pullback.fst aX aX) (pullback.snd aX aX) aX K :=
  G.kernelClassOf (IsPullback.of_hasPullback aX aX) c.isGeometricHom_toProd c.toProd_fst
    c.toProd_snd hK c.mate

end Correspondence
namespace ProperPushforwardDiagram

variable {X : Scheme.{u}} {aX : X ⟶ s} {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {c : Correspondence aX aX K K} (P : ProperPushforwardDiagram c)

/-- The product map `q = f × f : X ×_s X ⟶ Y ×_s Y` of a proper pushforward diagram
(part of blueprint `def-trf-kernel-pushforward-maps` (5)). -/
noncomputable def prodMap : pullback aX aX ⟶ pullback P.tgtStr P.tgtStr :=
  pullback.map aX aX P.tgtStr P.tgtStr P.f P.f (𝟙 s) (by simp [P.f_comp]) (by simp [P.f_comp])

/-- The support square `b ∘ g = q ∘ c` of a proper pushforward diagram commutes. -/
@[reassoc]
lemma g_toProd : P.g ≫ P.toProd = c.toProd ≫ P.prodMap := by
  apply pullback.hom_ext <;> simp [toProd, prodMap, P.g_fst, P.g_snd]

variable [DerivedBraiding A] (G : GeometricOperations A s) [IsGeometric aX]
  [IsGeometric P.tgtStr] [IsGeometric c.str] [IsGeometric P.str] [HasCompactification c.toProd]
  [HasCompactification P.toProd] [IsProper P.prodMap] [HasCompactification (P.g ≫ P.toProd)]
  [HasCompactification (c.toProd ≫ P.prodMap)]

/-- The exchange transformation `𝖤 : Rg_* Rc^! ⟶ Rb^! Rq_*` of a proper pushforward diagram,
for the support maps `c : C ⟶ X ×_s X`, `b : D ⟶ Y ×_s Y` and `q = f × f`:
`GeometricOperations.lowerStarUpperShriekExchange` at the square `g_toProd`
(blueprint `def-trf-kernel-pushforward-maps` (9)). -/
noncomputable def lowerStarUpperShriekExchange :
    G.upperShriekCtf c.toProd c.isGeometricHom_toProd ⋙ G.lowerStarCtf P.g (.mk P.g_comp_str) ⟶
      G.lowerStarCtf P.prodMap
          (.mk (aX := pullback.fst aX aX ≫ aX) (aY := pullback.fst P.tgtStr P.tgtStr ≫ P.tgtStr)
            (by simp [prodMap, P.f_comp])) ⋙
        G.upperShriekCtf P.toProd
          (.mk (aX := P.str) (aY := pullback.fst P.tgtStr P.tgtStr ≫ P.tgtStr)
            (by simp [toProd, P.fst_comp])) :=
  G.lowerStarUpperShriekExchange P.g_toProd _ _ _ _

end ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale
