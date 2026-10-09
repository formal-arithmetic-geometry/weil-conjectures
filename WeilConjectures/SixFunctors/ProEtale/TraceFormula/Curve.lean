/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization

/-!
# Local terms of Frobenius on a smooth curve

Let `X` be the geometric base change of a smooth `𝐅_q`-curve `X₀`, let `(K, φ)` be a Weil
complex on `X` and let `x̄` be a geometric point fixed by the `m`-th Frobenius iterate
`Φ_m`. Writing `i : Z ⟶ X` for the closed point `{x̄}` and `j : U ⟶ X` for its open
complement, the localization triangle splits `K` into the two pieces `K^Z = Ri_* i^* K` and
`K^U = j_! j^* K`, each carrying an induced Frobenius coefficient morphism. The trace class
of the graph correspondence is additive along this decomposition, the open piece has zero
stalk at `x̄` and therefore zero local term, and what is left is the categorical trace of
Frobenius on the geometric stalk `K_x̄`.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_zero_of_isZero`:
  a fixed point with vanishing stalk has vanishing local term.
- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_trace`: the local
  term of Frobenius at a fixed point is the trace on the geometric stalk.

## Implementation notes

Smoothness of pure dimension one is rendered as
`AlgebraicGeometry.SmoothOfRelativeDimension 1 aX`. The Frobenius of the Weil complex is the
base change of the `q`-power Frobenius of a model `X₀` over `𝐅_q`
(`WeilComplex.IsModelFrobenius`): for an arbitrary `s`-endomorphism the fixed points need not
be transversal and the local terms are not the naive ones. The geometric point is a section
`x : s ⟶ X` of `a_X` fixed by `Φ_m`, as in the rendering of `X₀(𝐅_{q^m})`. The clopen component of
`x̄` inside the fixed scheme is taken as data, since the project constructs neither the
reduced point structure nor open complements. Isolatedness of the fixed point, which the
blueprint derives from the vanishing of the map induced by `Φ_m` on the cotangent space, is
therefore assumed rather than proved. The local term integrates over the whole fixed scheme
(`GeometricOperations.localTerm`), so the statements assume it proper over `s`, as it is for
the Frobenius of a separated `X₀` of finite type: `Fix(Φ_m)` is then finite over `s`.

The pieces `K^Z` and `K^U` of the localization triangle at `x̄` and the additivity of the
trace class along it are stated for an arbitrary closed-open decomposition in
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization`; the curve argument
specialises them to `Z = {x̄}`.

The trace class needs `a_X` separated, locally of finite type and quasi-compact. The first
two are instances derived from `HasCompactification aX` (`HasCompactification.isSeparated`
and `HasCompactification.locallyOfFiniteType`), so the statements only add
`[QuasiCompact aX]`.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {s X : Scheme.{u}} {aX : X ⟶ s}

namespace GeometricOperations

/-- Zero-stalk vanishing on a smooth curve: a geometric point `x̄` fixed by `Φ_m` is an
isolated, hence open-and-closed, component `B` of the fixed scheme `Fix(c_m)` of the graph
correspondence `c_m = (1, Φ_m)`; purity in relative dimension zero computes the trace class
there from the pair `(K_x̄, u_x̄)` alone, so if the geometric stalk `K_x̄` vanishes then so
does the local term `LT_x̄(φ_m)` (blueprint: `sk-i-curve-zero`). -/
theorem localTerm_traceClass_eq_zero_of_isZero [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s)
    [s.IsSpecOfField] [HasCompactification aX] [QuasiCompact aX]
    (W : WeilComplex (A := A) aX) {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) (σ : s ⟶ Spec (.of k)) (p : X ⟶ X₀)
    (hΦ : W.IsModelFrobenius f₀ σ p) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hxs : x ≫ aX = 𝟙 s) (hx : x ≫ W.frobeniusIterate m = x)
    (xFix : s ⟶ (W.graph G hW m).fix)
    (hxFix : xFix ≫ (W.graph G hW m).fixι = x) {B : Scheme.{u}} (jB : B ⟶ (W.graph G hW m).fix)
    [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base))
    (hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (W.graph G hW m).fixStr] [IsProper (W.graph G hW m).fixStr]
    (hstalk : IsZero (((upperStar A x).leftDerivedFunctor).obj W.obj)) :
    G.localTerm (W.graph G hW m).fixStr jB hB (G.traceClass (W.graph G hW m) hW) = 0 :=
  sorry

/-- Frobenius local terms on smooth curves: the local term of the graph correspondence
`c_m = (1, Φ_m)` at a geometric point `x̄` fixed by `Φ_m` is the categorical trace of
Frobenius on the geometric stalk,

`LT_x̄(φ_m) = tr_A(F_{x,m} ∣ K_x̄)`, where `F_{x,m}` is `W.stalkFrobenius m x hx`.

No local constancy of `K` at `x̄` is assumed (blueprint: `sk-p-frob`). -/
theorem localTerm_traceClass_eq_trace [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s)
    [s.IsSpecOfField] [HasCompactification aX] [QuasiCompact aX]
    (W : WeilComplex (A := A) aX) {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) (σ : s ⟶ Spec (.of k)) (p : X ⟶ X₀)
    (hΦ : W.IsModelFrobenius f₀ σ p) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hxs : x ≫ aX = 𝟙 s) (hx : x ≫ W.frobeniusIterate m = x)
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    (xFix : s ⟶ (W.graph G hW m).fix) (hxFix : xFix ≫ (W.graph G hW m).fixι = x) {B : Scheme.{u}}
    (jB : B ⟶ (W.graph G hW m).fix) [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base))
    (hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (W.graph G hW m).fixStr] [IsProper (W.graph G hW m).fixStr] :
    G.localTerm (W.graph G hW m).fixStr jB hB (G.traceClass (W.graph G hW m) hW) =
      MonoidalCategory.trace (W.stalkFrobenius m x hx) :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
