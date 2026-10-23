/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing

/-!
# Finite reduction of the Poincaré pairing

Let `Λ, Λ'` be finite coefficient rings with Tate twist data, for instance `A_n = 𝒪_E/ϖⁿ` and
`A_m = 𝒪_E/ϖᵐ` with `m ≤ n`, and let `Ψ : D(-, Λ) ⥤ D(-, Λ')` be a change of coefficients,
such as the derived reduction `K ↦ K ⊗ᴸ_{A_n} A_m`
(`AlgebraicGeometry.Etale.derivedExtendScalars`). Blueprint `thm-pod-finite-reduction`: the
reduction of the derived Poincaré pairing `β_{K_n}` is the pairing `β_{K_m}` of the reduction,
and consequently the square of inverse adjoints

```
Ψ(RΓ_c(X, K_n)^∨)  ──Ψ(β_{K_n}^{♯,-1})──▶ Ψ(RΓ(X, K_n^∨(d))[2d])
       │ ≀                                       │ ≀
       ▼                                         ▼
RΓ_c(X, K_m)^∨     ───β_{K_m}^{♯,-1}───▶  RΓ(X, K_m^∨(d))[2d]
```

commutes; the right vertical comparison is an isomorphism as soon as the left one is.

## Main statements

- `CategoryTheory.MonoidalClosed.map_curry_comp_dualComparison`: for a functor `F` with a
  tensor comparison, the reduction of a pairing `β` agreeing with a pairing `β'` makes the
  square of adjoints `β^♯` commute.
- `CategoryTheory.MonoidalClosed.IsPerfectPairing.map_iso_inv_comp`: the square of inverse
  adjoints, for perfect pairings.
- `AlgebraicGeometry.Etale.TateOrientation.map_poincarePairing`: the reduction of the derived
  Poincaré pairing is the Poincaré pairing of the reduction.
- `AlgebraicGeometry.Etale.TateOrientation.finiteReduction_poincarePairing`
  (`thm-pod-finite-reduction`): the displayed square.

## Implementation notes

As in `WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction`, the coefficient change and its
compatibilities with the operations are arguments: the repository provides the derived
reduction `AlgebraicGeometry.Etale.derivedExtendScalars` and its compatibility with the tensor
product (`AlgebraicGeometry.Etale.derivedExtendScalarsTensorIso`), but not the coherent
comparisons with `Ra_!`, `Ra_*` and the coefficient dual. The hypotheses are exactly the
constituent squares of the blueprint proof: the reduction of the cup product, evaluation and
shift part of the pairing (`lem-fix-operation-reduction`), of the orientation and of the counit
of `Ra_! ⊣ Ra^!` (`thm-pur-finite-reduction-of-purity`). The dual `RΓ_c(X, K)^∨` is the
internal hom `RHom(Ra_! K, Λ_Y)` in `D(Y_ét)`, which over `Y = Spec k` is the dual of the
point complex; its comparison map is the canonical
`CategoryTheory.MonoidalClosed.dualComparisonOfTensorIso`, an isomorphism for `RΓ_c(X, K_n)` perfect
(`thm-pod-point-perfectness`), which is a hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalClosed

variable {C D : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
  [Category D] [MonoidalCategory D] [MonoidalClosed D] (F : C ⥤ D)

/-- The canonical comparison `F(P^∨) ⟶ (F P)^∨` of duals `P^∨ = [P, 𝟙]` for a functor `F`
with a comparison `μ : F(P ⊗ -) ≅ F P ⊗ F(-)` and `ε : F 𝟙 ≅ 𝟙`: the adjoint of
`F P ⊗ F(P^∨) ≅ F(P ⊗ P^∨) ⟶ F 𝟙 ≅ 𝟙`, the image of the evaluation. -/
noncomputable def dualComparisonOfTensorIso (P : C)
    (μ : (curriedTensor C).obj P ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj P))
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D) :
    F.obj ((ihom P).obj (𝟙_ C)) ⟶ (ihom (F.obj P)).obj (𝟙_ D) :=
  curry (μ.inv.app _ ≫ F.map ((ihom.ev P).app (𝟙_ C)) ≫ ε.hom)

variable {F}

/-- **Reduction of the adjoint of a pairing.** Let `β : P ⊗ Q ⟶ 𝟙` and `β' : P' ⊗ Q' ⟶ 𝟙` be
pairings, `u : F P ≅ P'` and `w : F Q ⟶ Q'`. If the image of `β` under `F` is `β'` read through
`u` and `w`, then the adjoints `β^♯ : Q ⟶ P^∨` and `β'^♯` are compatible:
`F(β^♯) ≫ (F(P^∨) ⟶ (F P)^∨) = w ≫ β'^♯ ≫ u^∨`. -/
theorem map_curry_comp_dualComparison {P Q : C} {P' Q' : D}
    (μ : (curriedTensor C).obj P ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj P))
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D) (β : P ⊗ Q ⟶ 𝟙_ C) (β' : P' ⊗ Q' ⟶ 𝟙_ D) (u : F.obj P ≅ P')
    (w : F.obj Q ⟶ Q') (h : μ.inv.app Q ≫ F.map β ≫ ε.hom = u.hom ▷ F.obj Q ≫ P' ◁ w ≫ β') :
    F.map (curry β) ≫ dualComparisonOfTensorIso F P μ ε =
      w ≫ curry β' ≫ (pre u.hom).app (𝟙_ D) := by
  apply uncurry_injective
  have hn := μ.inv.naturality (curry β)
  dsimp at hn
  rw [uncurry_natural_left, dualComparisonOfTensorIso, uncurry_curry, reassoc_of% hn,
    ← F.map_comp_assoc, ← uncurry_eq, uncurry_curry, h, uncurry_natural_left, uncurry_pre_app,
    uncurry_curry, whisker_exchange_assoc]

/-- **Reduction of the inverse adjoint of a perfect pairing.** In the situation of
`CategoryTheory.MonoidalClosed.map_curry_comp_dualComparison`, if `β` and `β'` are perfect and
the dual comparison `F(P^∨) ⟶ (F P)^∨` is an isomorphism, then `w` is an isomorphism and the
square of inverse adjoints commutes: `F(β^{♯,-1}) ≫ w = (F(P^∨) ≅ P'^∨) ≫ β'^{♯,-1}`. -/
theorem IsPerfectPairing.map_iso_inv_comp {P Q : C} {P' Q' : D}
    (μ : (curriedTensor C).obj P ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj P))
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D) {β : P ⊗ Q ⟶ 𝟙_ C} {β' : P' ⊗ Q' ⟶ 𝟙_ D} (u : F.obj P ≅ P')
    (w : F.obj Q ⟶ Q') (h : μ.inv.app Q ≫ F.map β ≫ ε.hom = u.hom ▷ F.obj Q ≫ P' ◁ w ≫ β')
    (hβ : IsPerfectPairing β) (hβ' : IsPerfectPairing β')
    [IsIso (dualComparisonOfTensorIso F P μ ε)] :
    IsIso w ∧ F.map hβ.iso.inv ≫ w =
      (dualComparisonOfTensorIso F P μ ε ≫ (pre u.inv).app (𝟙_ D)) ≫ hβ'.iso.inv := by
  have H := map_curry_comp_dualComparison μ ε β β' u w h
  have H' : F.map hβ.iso.hom ≫ dualComparisonOfTensorIso F P μ ε ≫ (pre u.inv).app (𝟙_ D) =
      w ≫ hβ'.iso.hom := by
    change F.map (curry β) ≫ _ ≫ _ = w ≫ curry β'
    rw [reassoc_of% H, ← NatTrans.comp_app, ← pre_map, u.inv_hom_id, pre_id,
      NatTrans.id_app, Category.comp_id]
  have hw : w = F.map hβ.iso.hom ≫ dualComparisonOfTensorIso F P μ ε ≫ (pre u.inv).app (𝟙_ D) ≫
      hβ'.iso.inv := by
    rw [reassoc_of% H', Iso.hom_inv_id, Category.comp_id]
  refine ⟨?_, ?_⟩
  · rw [hw]
    infer_instance
  · rw [hw, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp, Category.assoc]

end CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry

open Scheme

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable (A' : Type*) [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']
  {FA' : A' → A' → Type (u + 1)} {CA' : A' → Type (u + 1)}
  [∀ X Y, FunLike (FA' X Y) (CA' X) (CA' Y)] [ConcreteCategory.{u + 1} A' FA']
  [HasSmallSiteSheafify A'] [Etale.UpperStarPreservesFlat A']
  [(CategoryTheory.forget A').ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A')]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A')]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]
  [(R(a)_![A']).IsLeftAdjoint] {d : ℕ}

/-- The derived Poincaré pairing before the trace,
`Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Ra_!(T[2d])`: the shift moved out, the mixed-support cup
product, the twisted evaluation and the shift compatibility of `Ra_!`. The derived Poincaré
pairing is this map followed by the smooth trace
(`AlgebraicGeometry.Etale.poincarePairing_eq`). -/
noncomputable def poincarePairingUntraced (d : ℕ) (T K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶
      (R(a)_![A]).obj (T⟦(2 * d : ℤ)⟧) :=
  (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (poincarePairingEvaluation a T K)⟦(2 * d : ℤ)⟧' ≫
      ((R(a)_![A]).commShiftIso (2 * d : ℤ)).inv.app _

variable {A a}

omit [HasSmallSiteSheafify A] in
/-- The derived Poincaré pairing is the untraced pairing followed by the smooth trace. -/
lemma poincarePairing_eq {T : 𝐃(X, A)} (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (K : 𝐃(X, A)) :
    poincarePairing a γ K = poincarePairingUntraced A a d T K ≫ smoothTrace γ := by
  simp only [poincarePairing, poincarePairingUntraced, Category.assoc]

variable {A'}

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] [HasSmallSiteSheafify A']
  [Etale.UpperStarPreservesFlat A'] in
/-- Blueprint `thm-pur-finite-reduction-of-purity` (the smooth trace): **the smooth trace
reduces.** Let `Ψ` be a change of coefficients, `ψ : Ra_! ⋙ Ψ_Y ≅ Ψ_X ⋙ Ra_!` its commutation
with `Ra_!`, `ε : Ψ_Y Λ_Y ≅ Λ'_Y`, `v₀ : Ψ_X(T[2d]) ≅ T'[2d]` and `vω : Ψ_X ω_X ≅ ω'_X`. If the
orientations `γ : T[2d] ≅ ω_X`, `γ'` reduce (`hγ`) and the counit of `Ra_! ⊣ Ra^!` at `Λ_Y`
reduces (`hS`), then `Ψ_Y(Tr_γ) = Tr_{γ'}` read through `ψ`, `v₀` and `ε`. -/
theorem map_smoothTrace (ΨX : 𝐃(X, A) ⥤ 𝐃(X, A')) (ΨY : 𝐃(Y, A) ⥤ 𝐃(Y, A'))
    (ψ : R(a)_![A] ⋙ ΨY ≅ ΨX ⋙ R(a)_![A']) (ε : ΨY.obj (𝟙_ _) ≅ 𝟙_ _) {T : 𝐃(X, A)}
    {T' : 𝐃(X, A')} (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (γ' : T'⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A' a)
    (v₀ : ΨX.obj (T⟦(2 * d : ℤ)⟧) ≅ T'⟦(2 * d : ℤ)⟧)
    (vω : ΨX.obj (dualizingComplex A a) ≅ dualizingComplex A' a)
    (hγ : ΨX.map γ.hom ≫ vω.hom = v₀.hom ≫ γ'.hom)
    (hS : ψ.hom.app _ ≫ (R(a)_![A']).map vω.hom ≫
        (rightDerivedUpperShriekAdjunction A' a).counit.app (𝟙_ _) =
      ΨY.map ((rightDerivedUpperShriekAdjunction A a).counit.app (𝟙_ _)) ≫ ε.hom) :
    ΨY.map (smoothTrace γ) ≫ ε.hom =
      ψ.hom.app _ ≫ (R(a)_![A']).map v₀.hom ≫ smoothTrace γ' := by
  have hψ := ψ.hom.naturality γ.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hψ
  simp only [smoothTrace, Functor.map_comp, Category.assoc, ← hS]
  rw [reassoc_of% hψ, ← Functor.map_comp_assoc, hγ, Functor.map_comp_assoc]

omit [HasSmallSiteSheafify A] [HasSmallSiteSheafify A'] in
/-- Blueprint `thm-pod-finite-reduction` (first assertion): **the reduction of the derived
Poincaré pairing is the Poincaré pairing of the reduction.** Let `Ψ` be a change of
coefficients (for instance `- ⊗ᴸ_{A_n} A_m`), `K ∈ D(X, A)` and `K' ∈ D(X, A')` (the reduction
`K_m` of `K = K_n`), with comparisons `u : Ψ_Y(Ra_! K) ≅ Ra_! K'` (compact support) and
`w : Ψ_Y(Ra_*(K^∨ ⊗ᴸ T)[2d]) ⟶ Ra_*(K'^∨ ⊗ᴸ T')[2d]` (ordinary global sections), and a
tensor comparison `μ`. If the cup product, evaluation and shift part of the pairing reduces
(`hE`, `lem-fix-operation-reduction`), and so do the orientation (`hγ`) and the counit (`hS`)
(`thm-pur-finite-reduction-of-purity`), then `Ψ_Y(β_K)` is `β_{K'}` read through `μ`, `ε`, `u`
and `w`. -/
theorem map_poincarePairing (ΨX : 𝐃(X, A) ⥤ 𝐃(X, A')) (ΨY : 𝐃(Y, A) ⥤ 𝐃(Y, A'))
    (ψ : R(a)_![A] ⋙ ΨY ≅ ΨX ⋙ R(a)_![A']) (ε : ΨY.obj (𝟙_ _) ≅ 𝟙_ _) {T : 𝐃(X, A)}
    {T' : 𝐃(X, A')} (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (γ' : T'⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A' a)
    (v₀ : ΨX.obj (T⟦(2 * d : ℤ)⟧) ≅ T'⟦(2 * d : ℤ)⟧)
    (vω : ΨX.obj (dualizingComplex A a) ≅ dualizingComplex A' a)
    (hγ : ΨX.map γ.hom ≫ vω.hom = v₀.hom ≫ γ'.hom)
    (hS : ψ.hom.app _ ≫ (R(a)_![A']).map vω.hom ≫
        (rightDerivedUpperShriekAdjunction A' a).counit.app (𝟙_ _) =
      ΨY.map ((rightDerivedUpperShriekAdjunction A a).counit.app (𝟙_ _)) ≫ ε.hom)
    (K : 𝐃(X, A)) (K' : 𝐃(X, A'))
    (μ : (derivedTensor A Y).obj ((R(a)_![A]).obj K) ⋙ ΨY ≅
      ΨY ⋙ (derivedTensor A' Y).obj (ΨY.obj ((R(a)_![A]).obj K)))
    (u : ΨY.obj ((R(a)_![A]).obj K) ≅ (R(a)_![A']).obj K')
    (w : ΨY.obj (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶
      ((R((a)_*[A'])).obj (((derivedTensor A' X).obj
          ((DerivedCategory.coefficientDual A' X).obj (op K'))).obj T'))⟦(2 * d : ℤ)⟧)
    (hE : μ.inv.app _ ≫ ΨY.map (poincarePairingUntraced A a d T K) ≫ ψ.hom.app _ ≫
        (R(a)_![A']).map v₀.hom =
      ((derivedTensor A' Y).map u.hom).app _ ≫ ((derivedTensor A' Y).obj _).map w ≫
        poincarePairingUntraced A' a d T' K') :
    μ.inv.app _ ≫ ΨY.map (poincarePairing a γ K) ≫ ε.hom =
      ((derivedTensor A' Y).map u.hom).app _ ≫ ((derivedTensor A' Y).obj _).map w ≫
        poincarePairing a γ' K' := by
  rw [poincarePairing_eq, poincarePairing_eq, Functor.map_comp, Category.assoc,
    map_smoothTrace ΨX ΨY ψ ε γ γ' v₀ vω hγ hS, ← reassoc_of% hE]

omit [HasSmallSiteSheafify A] [HasSmallSiteSheafify A'] in
/-- Blueprint `thm-pod-finite-reduction`: Finite reduction of the Poincaré pairing.

Let `n ≥ m ≥ 1`, `A = ModuleCat A_n`, `A' = ModuleCat A_m`, `Ψ = - ⊗ᴸ_{A_n} A_m`, `K = K_n`
site-perfect and `K' = K_m`, and orientations `γ : T[2d] ≅ ω_X`, `γ'` (for a Tate orientation
`T = Λ_X(d)`, `AlgebraicGeometry.Etale.TateOrientation.dualizingComplexIso`). Assume the
constituent compatibilities of `AlgebraicGeometry.Etale.map_poincarePairing`, that the
pairings `β_K` and `β_{K'}` are perfect (derived Poincaré duality,
`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`), and that the
canonical comparison `Ψ_Y(RΓ_c(X, K_n)^∨) ⟶ (Ψ_Y RΓ_c(X, K_n))^∨` is an isomorphism (as it is
for the perfect complex `RΓ_c(X, K_n)`, `thm-pod-point-perfectness`). Then the comparison
`w : Ψ_Y(RΓ(X, K_n^∨(d))[2d]) ⟶ RΓ(X, K_m^∨(d))[2d]` is an isomorphism and the square

```
Ψ(RΓ_c(X, K_n)^∨)  ──Ψ(β_{K_n}^{♯,-1})──▶ Ψ(RΓ(X, K_n^∨(d))[2d])
       │ ≀                                       │ w
       ▼                                         ▼
RΓ_c(X, K_m)^∨     ───β_{K_m}^{♯,-1}───▶  RΓ(X, K_m^∨(d))[2d]
```

commutes, the left vertical map being the dual comparison followed by the dual of
`u : Ψ_Y RΓ_c(X, K_n) ≅ RΓ_c(X, K_m)`. Here `RΓ_c(X, K)^∨ = RHom(Ra_! K, Λ_Y)` in `D(Y_ét)`
and `β^♯` is the adjoint of the pairing. -/
theorem finiteReduction_poincarePairing (ΨX : 𝐃(X, A) ⥤ 𝐃(X, A'))
    (ΨY : 𝐃(Y, A) ⥤ 𝐃(Y, A'))
    (ψ : R(a)_![A] ⋙ ΨY ≅ ΨX ⋙ R(a)_![A']) (ε : ΨY.obj (𝟙_ _) ≅ 𝟙_ _) {T : 𝐃(X, A)}
    {T' : 𝐃(X, A')} (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (γ' : T'⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A' a)
    (v₀ : ΨX.obj (T⟦(2 * d : ℤ)⟧) ≅ T'⟦(2 * d : ℤ)⟧)
    (vω : ΨX.obj (dualizingComplex A a) ≅ dualizingComplex A' a)
    (hγ : ΨX.map γ.hom ≫ vω.hom = v₀.hom ≫ γ'.hom)
    (hS : ψ.hom.app _ ≫ (R(a)_![A']).map vω.hom ≫
        (rightDerivedUpperShriekAdjunction A' a).counit.app (𝟙_ _) =
      ΨY.map ((rightDerivedUpperShriekAdjunction A a).counit.app (𝟙_ _)) ≫ ε.hom)
    {K : 𝐃(X, A)} {K' : 𝐃(X, A')}
    (μ : (derivedTensor A Y).obj ((R(a)_![A]).obj K) ⋙ ΨY ≅
      ΨY ⋙ (derivedTensor A' Y).obj (ΨY.obj ((R(a)_![A]).obj K)))
    (u : ΨY.obj ((R(a)_![A]).obj K) ≅ (R(a)_![A']).obj K')
    (w : ΨY.obj (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶
      ((R((a)_*[A'])).obj (((derivedTensor A' X).obj
          ((DerivedCategory.coefficientDual A' X).obj (op K'))).obj T'))⟦(2 * d : ℤ)⟧)
    (hE : μ.inv.app _ ≫ ΨY.map (poincarePairingUntraced A a d T K) ≫ ψ.hom.app _ ≫
        (R(a)_![A']).map v₀.hom =
      ((derivedTensor A' Y).map u.hom).app _ ≫ ((derivedTensor A' Y).obj _).map w ≫
        poincarePairingUntraced A' a d T' K')
    (hβ : IsPerfectPairing (poincarePairing a γ K))
    (hβ' : IsPerfectPairing (poincarePairing a γ' K'))
    [IsIso (MonoidalClosed.dualComparisonOfTensorIso ΨY _ μ ε)] :
    IsIso w ∧ ΨY.map hβ.iso.inv ≫ w =
      (MonoidalClosed.dualComparisonOfTensorIso ΨY _ μ ε ≫ (MonoidalClosed.pre u.inv).app (𝟙_ _)) ≫
        hβ'.iso.inv :=
  MonoidalClosed.IsPerfectPairing.map_iso_inv_comp μ ε u w
    (map_poincarePairing ΨX ΨY ψ ε γ γ' v₀ vω hγ hS K K' μ u w hE) hβ hβ'

end Etale

end AlgebraicGeometry
