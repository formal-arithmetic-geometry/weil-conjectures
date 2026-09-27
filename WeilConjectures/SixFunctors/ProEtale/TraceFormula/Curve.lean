/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing

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

Smoothness of pure dimension one is rendered as
`AlgebraicGeometry.SmoothOfRelativeDimension 1 aX`. The geometric point is an `s`-point
`x : s ⟶ X` fixed by `Φ_m`, as in the rendering of `X₀(𝐅_{q^m})`, and the closed point
subscheme and its open complement are hypotheses: the project constructs neither the
reduced point structure nor open complements. Likewise the clopen component of `x̄` inside
the fixed scheme, the identification of the stalk of the fixed-point component and the
endomorphism `F_{x,m}` of the geometric stalk are taken as data.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.curvePieces` (blueprint `sk-d-curve-pieces`)

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_zero_of_isZero`
  (blueprint `sk-i-curve-zero`)
- `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass_graph_eq_traceClass_add_traceClass`
  (blueprint `sk-i-additivity`)
- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_trace` (blueprint
  `sk-p-frob`)
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}

/-- Blueprint `sk-d-curve-pieces`: Curve coefficient pieces.

Let `(K, φ)` be a Weil complex on `X`, with `X₀` smooth of pure dimension one, let `m ≥ 1`
and let `x̄ : s ⟶ X` be a geometric point fixed by `Φ_m`. Let `i : Z ⟶ X` be the closed
immersion of `{x̄}` and `j : U ⟶ X` the open immersion of its complement. The two pieces of
the functorial localization triangle are

`K^Z = Ri_* i^* K`  and  `K^U = j_! j^* K`,

and both inherit a Frobenius coefficient morphism. On the closed piece it is the proper
pushforward `u^Z = [i, i]_!(F_{x,m})` of the stalk map, and on the open piece it is the
composite

`Φ^* j_! j^* K ≃ j_! Φ_U^* j^* K --(j_! j^* φ)--> j_! j^* K`,

whose first map is open `!`-base change for the Cartesian square relating `Φ` and its
restriction `Φ_U` to `U`. The same recipe applies to an arbitrary Frobenius coefficient
morphism in the sense of `AlgebraicGeometry.ProEtale.WeilComplex`, and that is how it is
stated here: no invertibility of `coeff` is required.

The result is the pair `(K^Z, u^Z)`, `(K^U, u^U)` of Weil complexes on `X`, with the same
Frobenius `Φ₁` as `W`; the blueprint's maps on the graph `(1, Φ_m)` are their `m`-th
iterates `WeilComplex.coeffIterate`. Keeping the one-step Frobenius is what makes the three
graph correspondences `W.graph m`, `K^Z.graph m` and `K^U.graph m` share their fixed scheme,
as `sk-i-additivity` needs. Both `!`-base change and the proper pushforward of a stalk map
are comparison data that the package only postulates, so the two coefficient morphisms are
left with `sorry` bodies; their intended composites are the ones displayed above. The closed
point subscheme and its open complement are hypotheses rather than constructions: `i` is a
closed immersion with the same image as `x̄`, and `j` is an open immersion whose image is the
complement of that of `i`. -/
noncomputable def WeilComplex.curvePieces [SmoothOfRelativeDimension 1 aX]
    (W : WeilComplex (A := A) aX) (m : ℕ) (_hm : 1 ≤ m) (x : s ⟶ X)
    (_hx : x ≫ W.frobeniusIterate m = x) {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [HasCompactification j]
    (_hi : Set.range i.base = Set.range x.base)
    (_hj : Set.range j.base = (Set.range i.base)ᶜ) :
    WeilComplex (A := A) aX × WeilComplex (A := A) aX :=
  ⟨{ frobenius := W.frobenius
     frobenius_comp := W.frobenius_comp
     obj := ((lowerStar A i).rightDerivedFunctor).obj
       (((upperStar A i).leftDerivedFunctor).obj W.obj)
     coeff := sorry },
   { frobenius := W.frobenius
     frobenius_comp := W.frobenius_comp
     obj := (rightDerivedLowerShriek A j).obj (((upperStar A j).leftDerivedFunctor).obj W.obj)
     coeff := sorry }⟩

namespace GeometricOperations

/-- Blueprint `sk-i-curve-zero`: Zero-stalk vanishing on a smooth curve.

In the smooth-curve setting, a geometric point `x̄` fixed by `Φ_m` is an isolated, hence
open-and-closed, component `B` of the fixed scheme `Fix(c_m)` of the graph correspondence
`c_m = (1, Φ_m)`. Purity in relative dimension zero computes the trace class there from the
pair `(K_x̄, u_x̄)` alone, so if the geometric stalk `K_x̄` vanishes then so does the local
term `LT_x̄(φ_m)`.

The argument is local on the fixed scheme and uses no invertibility of the coefficient
morphism, so the statement is for a plain `AlgebraicGeometry.ProEtale.WeilComplex`, which
covers both a Weil datum and an arbitrary Frobenius coefficient morphism `Φ_m^* K ⟶ K`.

The point component of `x̄` is a hypothesis: `xFix` is the lift of `x̄` to the fixed scheme,
and `jB` is a clopen immersion, proper over the base, whose image is exactly that of `xFix`.
Isolatedness of the fixed point, which the blueprint derives from the vanishing of the map
induced by `Φ_m` on the cotangent space, is therefore also assumed rather than proved. -/
theorem localTerm_traceClass_eq_zero_of_isZero [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s) (W : WeilComplex (A := A) aX) (m : ℕ) (_hm : 1 ≤ m)
    (x : s ⟶ X) (_hx : x ≫ W.frobeniusIterate m = x) (xFix : s ⟶ (W.graph m).fix)
    (_hxFix : xFix ≫ (W.graph m).fixι = x) {B : Scheme.{u}} (jB : B ⟶ (W.graph m).fix)
    [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base))
    (_hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (jB ≫ (W.graph m).fixStr)] [IsProper (jB ≫ (W.graph m).fixStr)]
    (_hstalk : IsZero (((upperStar A x).leftDerivedFunctor).obj W.obj)) :
    G.localTerm (W.graph m).fixStr jB hB (G.traceClass (W.graph m)) = 0 :=
  sorry

/-- Blueprint `sk-i-additivity`: Localization trace additivity.

The three coefficient morphisms `φ_m`, `u^Z` and `u^U` of `sk-d-curve-pieces` form a
morphism of the distinguished triangle of the open-closed decomposition, compatibly with
`Lc₂^*` and `Rc₁^!`. Triangle compatibility of the Verdier trace class therefore gives

`Tr_{(1, Φ_m)}(φ_m) = Tr_{(1, Φ_m)}(u^Z) + Tr_{(1, Φ_m)}(u^U)`

in the group of Borel-Moore sections `A_F ⟶ ω_F` on the fixed scheme `F`. No invertibility
of the coefficient morphisms is used, so the statement is for a plain
`AlgebraicGeometry.ProEtale.WeilComplex`.

The three trace classes live on the same fixed scheme: the graph correspondences of the
three Weil complexes have the same legs `(1, Φ_m)`, because `WeilComplex.curvePieces` keeps
the Frobenius of `W`, so `(W.graph m).fix`, `(K^Z.graph m).fix` and `(K^U.graph m).fix` are
definitionally equal and the sum is literally a sum in the group of Borel-Moore sections on
`F = Fix(c_m)`. No transport is needed and none is stated; the two `show` ascriptions only
spell out that common type, which instance search for `+` does not unfold to on its own.
Integrating over a clopen component then descends the identity to local terms, by
`sk-d-integral` and `sk-p-local`. -/
theorem traceClass_graph_eq_traceClass_add_traceClass [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s) (W : WeilComplex (A := A) aX) (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [HasCompactification j]
    (hi : Set.range i.base = Set.range x.base)
    (hj : Set.range j.base = (Set.range i.base)ᶜ) :
    G.traceClass (W.graph m) =
      (show 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology (W.graph m).fix) A)) ⟶
          G.dualizing (W.graph m).fixStr from
        G.traceClass ((W.curvePieces m hm x hx i j hi hj).1.graph m)) +
      (show 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology (W.graph m).fix) A)) ⟶
          G.dualizing (W.graph m).fixStr from
        G.traceClass ((W.curvePieces m hm x hx i j hi hj).2.graph m)) :=
  sorry

/-- Blueprint `sk-p-frob`: Frobenius local terms on smooth curves.

For the smooth-curve datum, the local term of the graph correspondence `c_m = (1, Φ_m)` at a
geometric point `x̄` fixed by `Φ_m` is the categorical trace of Frobenius on the geometric
stalk:

`LT_x̄(φ_m) = tr_A(F_{x,m} ∣ K_x̄)`.

No local constancy of `K` at `x̄` is assumed. The proof of the blueprint extends `K^U` by
zero to see that `(K^U)_x̄ = 0`, kills its local term by `sk-i-curve-zero`, removes it by
`sk-i-additivity`, and evaluates the remaining closed piece by proper compatibility and the
point normalization of `sk-p-local`.

Perfectness of the stalk is `HasRightDual`, `tr_A` is
`CategoryTheory.MonoidalCategory.trace` in `D(s, A)`, whose unit endomorphism ring is `A`,
and the braiding of `D(s, A)` is an instance hypothesis: this project installs a monoidal
structure on a derived category but no braiding.

The stalk endomorphism `F_{x,m}` is data, taken as an explicit hypothesis `Fx` together with
the compatibility that it is the stalk of `φ_m`: an isomorphism `e : K_x̄ ≃ (Φ_m^* K)_x̄`,
which is the comparison for `x̄ ≫ Φ_m = x̄` that the project does not construct, followed by
`Lx̄^*(φ_m)`. As in `sk-i-curve-zero`, the clopen point component `jB` of `x̄` inside the
fixed scheme is a hypothesis. -/
theorem localTerm_traceClass_eq_trace [SmoothOfRelativeDimension 1 aX]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    (G : GeometricOperations A s) (W : WeilComplex (A := A) aX) (m : ℕ) (_hm : 1 ≤ m)
    (x : s ⟶ X) (_hx : x ≫ W.frobeniusIterate m = x)
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    (Fx : ((upperStar A x).leftDerivedFunctor).obj W.obj ⟶
      ((upperStar A x).leftDerivedFunctor).obj W.obj)
    (e : ((upperStar A x).leftDerivedFunctor).obj W.obj ≅
      ((upperStar A x).leftDerivedFunctor).obj
        (((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj W.obj))
    (_hFx : Fx = e.hom ≫ ((upperStar A x).leftDerivedFunctor).map (W.coeffIterate m))
    (xFix : s ⟶ (W.graph m).fix) (_hxFix : xFix ≫ (W.graph m).fixι = x) {B : Scheme.{u}}
    (jB : B ⟶ (W.graph m).fix) [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base))
    (_hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (jB ≫ (W.graph m).fixStr)] [IsProper (jB ≫ (W.graph m).fixStr)] :
    G.localTerm (W.graph m).fixStr jB hB (G.traceClass (W.graph m)) =
      MonoidalCategory.trace Fx :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
