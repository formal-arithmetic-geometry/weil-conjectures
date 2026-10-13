/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity

/-!
# Global operators and fibres of the Weil `!`-pushforward

Let `f : X ⟶ Y` be a morphism of geometric schemes over `s = Spec Ω` compatible with the
Frobenius morphisms, and let `(L, ψ) = (Rf_! K, Rf_! φ ∘ θ_{f,1})` be the Weil `!`-pushforward
(`WeilComplex.lowerShriekPush`) of a Weil complex `(K, φ)` on `X`. The global operators of
`(K, φ)` and `(L, ψ)` have the same trace, and at a point `ȳ` of `Y` fixed by `Φ_{Y,m}` the stalk
Frobenius of `ψ_m` has the trace of the degree-one global operator of the fibre `X_ȳ` with the
restricted coefficient morphism `φ_m|_ȳ`.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.fibre`: the fibre `X_ȳ = X ×_{Y} s` of `f` at a point
  `ȳ` fixed by an endomorphism of `Y` lifted by `Φ_{X,m}`, with Frobenius the restriction of
  `Φ_{X,m}` and coefficient morphism `φ_m|_ȳ`.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.trace_globalOperator_lowerShriekPush`: the global
  operators of `(K, φ)` and `(L, ψ)` have the same trace.
- `AlgebraicGeometry.ProEtale.WeilComplex.exists_isModelFrobenius_fibre`: the fibre has a model
  Frobenius over `𝐅_{q^m}`, and the stalk Frobenius of `ψ_m` at `ȳ` has the trace of the
  degree-one global operator of the fibre.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

namespace WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  (W : WeilComplex (A := A) aX)

/-- The fibre `X_ȳ = X ×_{f, Y, ȳ} s` of `f : X ⟶ Y` at a point `ȳ : s ⟶ Y` fixed by an
endomorphism `g_Y` of `Y` with `Φ_{X,m} ≫ f = f ≫ g_Y`, as a Weil complex over `s`: its Frobenius
is the restriction of `Φ_{X,m}` and its coefficient morphism is the restriction
`φ_m|_ȳ = W.upperStarPullCoeff m` of the iterate `φ_m` to the fibre (blueprint
`lem-trf-weil-shriek-operator-fibres`, item 2). -/
noncomputable def fibre (f : X ⟶ Y) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY) (y : s ⟶ Y) (hy : y ≫ gY = y) :
    WeilComplex (A := A) (pullback.snd f y) where
  frobenius := pullback.lift (pullback.fst f y ≫ W.frobeniusIterate m) (pullback.snd f y)
    (by rw [Category.assoc, hfg, ← Category.assoc, pullback.condition, Category.assoc, hy])
  frobenius_comp := pullback.lift_snd _ _ _
  obj := ((upperStar A (pullback.fst f y)).leftDerivedFunctor).obj W.obj
  coeff := W.upperStarPullCoeff m ⟨pullback.lift_fst _ _ _⟩

variable [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

section Pushforward

variable (G : GeometricOperations A s) (hW : G.ctf X W.obj) [IsGeometric aX] [IsGeometric aY]
  [HasCompactification aX] [HasCompactification aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
  [HasCompactification f] (frobY : Y ⟶ Y) (hY : frobY ≫ aY = aY)
  (h : f ≫ frobY = W.frobenius ≫ f) [IsGeometric (pullback.snd frobY f ≫ aX)]
  [IsProper (relativeFrobenius f W.frobenius frobY h)]

/-- Item 1 of blueprint `lem-trf-weil-shriek-operator-fibres` (subsection `sk-d-weil-push`):
the composition isomorphism `RΓ_c(Y, Rf_! K) ≃ RΓ_c(X, K)` conjugates the global operator
`F_{c,m}(ψ)` of the Weil `!`-pushforward into `F_{c,m}(φ)`, so the two have the same trace. -/
theorem trace_globalOperator_lowerShriekPush (m : ℕ)
    [IsProper (W.graph G hW m).snd]
    [IsProper ((W.lowerShriekPush G hW f hf frobY hY h).graph G
      (G.ctf_lowerShriek f (.mk hf) hW) m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [HasRightDual ((rightDerivedLowerShriek A aY).obj
      (W.lowerShriekPush G hW f hf frobY hY h).obj)] :
    MonoidalCategory.trace (Correspondence.globalOperator G
        ((W.lowerShriekPush G hW f hf frobY hY h).graph G (G.ctf_lowerShriek f (.mk hf) hW) m)
        (G.ctf_lowerShriek f (.mk hf) hW)) =
      MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G hW m) hW) :=
  sorry

end Pushforward

/-- Item 2 of blueprint `lem-trf-weil-shriek-operator-fibres` (subsection `sk-d-weil-push`):
let `X`, `Y` be base changes to `s = Spec Ω` of `X₀`, `Y₀` over a finite field `k`, with
compatible Frobenius morphisms, `f` the base change of `f₀' : X₀ ⟶ Y₀`, and `ȳ` a point of `Y`
fixed by `Φ_{Y,m}`, `m ≥ 1`, lying over `y ∈ Y₀(𝐅_{q^m})`. Then the fibre `X_ȳ`
(`WeilComplex.fibre`) is the base change of `X_{0,y} = X₀ ×_{Y₀, y} Spec 𝐅_{q^m}` with model
Frobenius the restriction of `Φ_{X,m}`, and the stalk Frobenius `ψ_{m,ȳ}` of the Weil
`!`-pushforward is conjugate, through proper base change, to the degree-one global operator
`F_{c,1}(φ_m|_ȳ)` of the fibre, so they have the same trace. -/
theorem exists_isModelFrobenius_fibre {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {X Y : Scheme.{u}} {aX : X ⟶ Spec (.of Ω)}
    {aY : Y ⟶ Spec (.of Ω)} [IsGeometric aX] [IsGeometric aY] [HasCompactification aX]
    [HasCompactification aY] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (f : X ⟶ Y)
    (hf : f ≫ aY = aX) [HasCompactification f] (frobY : Y ⟶ Y) (hY : frobY ≫ aY = aY)
    (h : f ≫ frobY = W.frobenius ≫ f) [IsGeometric (pullback.snd frobY f ≫ aX)]
    [IsProper (relativeFrobenius f W.frobenius frobY h)]
    {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k)} {g₀ : Y₀ ⟶ Spec (.of k)} {σ : Spec (.of Ω) ⟶ Spec (.of k)}
    {pX : X ⟶ X₀} {pY : Y ⟶ Y₀} (hΦ : W.IsModelFrobenius f₀ σ pX)
    (hYpb : IsPullback pY aY g₀ σ) (FY : Y₀ ⟶ Y₀) (hFY : FY.IsFrobenius (Nat.card k))
    (hpY : frobY ≫ pY = pY ≫ FY) (f₀' : X₀ ⟶ Y₀) (hf₀' : f₀' ≫ g₀ = f₀)
    (hpf : f ≫ pY = pX ≫ f₀') (m : ℕ) (hm : 1 ≤ m)
    (hfg : W.frobeniusIterate m ≫ f =
      f ≫ (W.lowerShriekPush G hW f hf frobY hY h).frobeniusIterate m)
    (y : Spec (.of Ω) ⟶ Y) (hys : y ≫ aY = 𝟙 _)
    (hy : y ≫ (W.lowerShriekPush G hW f hf frobY hY h).frobeniusIterate m = y) :
    ∃ (k' : Type u) (_ : Field k') (_ : Finite k') (σ' : Spec (.of Ω) ⟶ Spec (.of k'))
      (y₀ : Spec (.of k') ⟶ Y₀) (hy₀ : y ≫ pY = σ' ≫ y₀),
      Nat.card k' = Nat.card k ^ m ∧
      (W.fibre f m _ hfg y hy).IsModelFrobenius (pullback.snd f₀' y₀) σ'
        (pullback.map f y f₀' y₀ pX σ' pY hpf hy₀) ∧
      ∀ (hctf : G.ctf (pullback f y) (W.fibre f m _ hfg y hy).obj)
        [IsGeometric (pullback.snd f y)] [HasCompactification (pullback.snd f y)]
        [IsProper ((W.fibre f m _ hfg y hy).graph G hctf 1).snd]
        [HasRightDual ((rightDerivedLowerShriek A (pullback.snd f y)).obj
          (W.fibre f m _ hfg y hy).obj)]
        [HasRightDual (((upperStar A y).leftDerivedFunctor).obj
          (W.lowerShriekPush G hW f hf frobY hY h).obj)],
        MonoidalCategory.trace ((W.lowerShriekPush G hW f hf frobY hY h).stalkFrobenius m y hy) =
          MonoidalCategory.trace (Correspondence.globalOperator G
            ((W.fibre f m _ hfg y hy).graph G hctf 1) hctf) :=
  sorry

end WeilComplex

end AlgebraicGeometry.ProEtale
