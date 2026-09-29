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

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.closedPiece`,
  `AlgebraicGeometry.ProEtale.WeilComplex.openPiece`: the two pieces `K^Z` and `K^U` of
  the localization triangle, as Weil complexes.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_zero_of_isZero`:
  a fixed point with vanishing stalk has vanishing local term.
- `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass_graph_eq_traceClass_add_traceClass`:
  additivity of the trace class along the localization triangle.
- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm_traceClass_eq_trace`: the local
  term of Frobenius at a fixed point is the trace on the geometric stalk.

## Implementation notes

Smoothness of pure dimension one is rendered as
`AlgebraicGeometry.SmoothOfRelativeDimension 1 aX`. The geometric point is an `s`-point
`x : s ⟶ X` fixed by `Φ_m`, as in the rendering of `X₀(𝐅_{q^m})`, and the closed point
subscheme and its open complement are hypotheses: the project constructs neither the
reduced point structure nor open complements. Likewise the clopen component of `x̄` inside
the fixed scheme, the identification of the stalk of the fixed-point component and the
endomorphism `F_{x,m}` of the geometric stalk are taken as data. Isolatedness of the fixed
point, which the blueprint derives from the vanishing of the map induced by `Φ_m` on the
cotangent space, is therefore assumed rather than proved.

Both pieces keep the Frobenius `Φ₁` of `W`. That is what makes the three graph
correspondences `W.graph m`, `(W.closedPiece …).graph m` and `(W.openPiece …).graph m`
share their fixed scheme, so that the additivity statement is a genuine sum of Borel-Moore
sections on `F = Fix(c_m)` with no transport. Their coefficient morphisms are `!`-base
change along the Cartesian square relating `Φ` to its restriction and the proper
pushforward of a stalk map, neither of which the package constructs, so they are `opaque`
for the reason explained in
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence`.

The sum in `traceClass_graph_eq_traceClass_add_traceClass` is spelled `Add.add` with an
explicit type argument. The three types agree definitionally but not syntactically, and
the elaborator for `+` compares the types of its operands syntactically, so it needs to be
told which one to use.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}

namespace WeilComplex

variable (W : WeilComplex (A := A) aX)

/-- The coefficient morphism of `AlgebraicGeometry.ProEtale.WeilComplex.closedPiece`: the
proper pushforward `u^Z = [i, i]_!(F_{x,m})` of the stalk map. -/
noncomputable opaque closedPieceCoeff {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ((upperStar A W.frobenius).leftDerivedFunctor).obj
        (((lowerStar A i).rightDerivedFunctor).obj
          (((upperStar A i).leftDerivedFunctor).obj W.obj)) ⟶
      ((lowerStar A i).rightDerivedFunctor).obj
        (((upperStar A i).leftDerivedFunctor).obj W.obj) := 0

/-- The coefficient morphism of `AlgebraicGeometry.ProEtale.WeilComplex.openPiece`: the
composite `Φ^* j_! j^* K ≃ j_! Φ_U^* j^* K --(j_! j^* φ)--> j_! j^* K`, whose first map is
open `!`-base change for the Cartesian square relating `Φ` and its restriction `Φ_U`. -/
noncomputable opaque openPieceCoeff {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [HasCompactification j] :
    ((upperStar A W.frobenius).leftDerivedFunctor).obj
        ((rightDerivedLowerShriek A j).obj
          (((upperStar A j).leftDerivedFunctor).obj W.obj)) ⟶
      (rightDerivedLowerShriek A j).obj
        (((upperStar A j).leftDerivedFunctor).obj W.obj) := 0

/-- The closed piece `K^Z = Ri_* i^* K` of the localization triangle of a Weil complex on a
smooth curve at the closed point `i : Z ⟶ X` cut out by a fixed geometric point `x̄`, with
the Frobenius of `W` and the induced coefficient morphism `u^Z`
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable def closedPiece [SmoothOfRelativeDimension 1 aX] (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : Set.range i.base = Set.range x.base) :
    WeilComplex (A := A) aX where
  frobenius := W.frobenius
  frobenius_comp := W.frobenius_comp
  obj := ((lowerStar A i).rightDerivedFunctor).obj
    (((upperStar A i).leftDerivedFunctor).obj W.obj)
  coeff := W.closedPieceCoeff i

/-- The open piece `K^U = j_! j^* K` of the localization triangle of a Weil complex on a
smooth curve along the open complement `j : U ⟶ X` of a fixed geometric point `x̄`, with
the Frobenius of `W` and the induced coefficient morphism `u^U`
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable def openPiece [SmoothOfRelativeDimension 1 aX] (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [HasCompactification j]
    (hj : Set.range j.base = (Set.range x.base)ᶜ) :
    WeilComplex (A := A) aX where
  frobenius := W.frobenius
  frobenius_comp := W.frobenius_comp
  obj := (rightDerivedLowerShriek A j).obj (((upperStar A j).leftDerivedFunctor).obj W.obj)
  coeff := W.openPieceCoeff j

end WeilComplex

namespace GeometricOperations

/-- Zero-stalk vanishing on a smooth curve: a geometric point `x̄` fixed by `Φ_m` is an
isolated, hence open-and-closed, component `B` of the fixed scheme `Fix(c_m)` of the graph
correspondence `c_m = (1, Φ_m)`; purity in relative dimension zero computes the trace class
there from the pair `(K_x̄, u_x̄)` alone, so if the geometric stalk `K_x̄` vanishes then so
does the local term `LT_x̄(φ_m)` (blueprint: `sk-i-curve-zero`). -/
theorem localTerm_traceClass_eq_zero_of_isZero [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s)
    (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k))) [HasCompactification aX]
    [IsSeparated aX] [QuasiCompact aX]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aX aX)) A))]
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    [HasCompactification (W.graph m).toProd]
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) (xFix : s ⟶ (W.graph m).fix)
    (hxFix : xFix ≫ (W.graph m).fixι = x) {B : Scheme.{u}} (jB : B ⟶ (W.graph m).fix)
    [IsOpenImmersion jB] [HasCompactification jB] (hB : IsClosed (Set.range jB.base))
    (hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (jB ≫ (W.graph m).fixStr)] [IsProper (jB ≫ (W.graph m).fixStr)]
    (hstalk : IsZero (((upperStar A x).leftDerivedFunctor).obj W.obj)) :
    G.localTerm (W.graph m).fixStr jB hB (G.traceClass (W.graph m) hs hW) = 0 :=
  sorry

/-- Localization trace additivity: the three coefficient morphisms `φ_m`, `u^Z` and `u^U`
form a morphism of the distinguished triangle of the open-closed decomposition, compatibly
with `Lc₂^*` and `Rc₁^!`, so triangle compatibility of the Verdier trace class gives

`Tr_{(1, Φ_m)}(φ_m) = Tr_{(1, Φ_m)}(u^Z) + Tr_{(1, Φ_m)}(u^U)`

in the group of Borel-Moore sections `A_F ⟶ ω_F` on the fixed scheme `F`
(blueprint: `sk-i-additivity`). -/
theorem traceClass_graph_eq_traceClass_add_traceClass [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s)
    (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k))) [HasCompactification aX]
    [IsSeparated aX] [QuasiCompact aX]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aX aX)) A))]
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    [HasCompactification (W.graph m).toProd]
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) {Z U : Scheme.{u}} (i : Z ⟶ X)
    (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [HasCompactification j]
    (hi : Set.range i.base = Set.range x.base)
    (hj : Set.range j.base = (Set.range x.base)ᶜ)
    (hZ : G.ctf X (W.closedPiece m hm x hx i hi).obj)
    (hU : G.ctf X (W.openPiece m hm x hx j hj).obj)
    [HasCompactification ((W.closedPiece m hm x hx i hi).graph m).toProd]
    [HasCompactification ((W.openPiece m hm x hx j hj).graph m).toProd] :
    G.traceClass (W.graph m) hs hW =
      Add.add (α := G.borelMooreSections (W.graph m).fixStr)
        (G.traceClass ((W.closedPiece m hm x hx i hi).graph m) hs hZ)
        (G.traceClass ((W.openPiece m hm x hx j hj).graph m) hs hU) :=
  sorry

/-- Frobenius local terms on smooth curves: the local term of the graph correspondence
`c_m = (1, Φ_m)` at a geometric point `x̄` fixed by `Φ_m` is the categorical trace of
Frobenius on the geometric stalk,

`LT_x̄(φ_m) = tr_A(F_{x,m} ∣ K_x̄)`.

No local constancy of `K` at `x̄` is assumed (blueprint: `sk-p-frob`). -/
theorem localTerm_traceClass_eq_trace [SmoothOfRelativeDimension 1 aX]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    (G : GeometricOperations A s)
    (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k))) [HasCompactification aX]
    [IsSeparated aX] [QuasiCompact aX]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aX aX)) A))]
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    [HasCompactification (W.graph m).toProd]
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x)
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    (Fx : ((upperStar A x).leftDerivedFunctor).obj W.obj ⟶
      ((upperStar A x).leftDerivedFunctor).obj W.obj)
    (e : ((upperStar A x).leftDerivedFunctor).obj W.obj ≅
      ((upperStar A x).leftDerivedFunctor).obj
        (((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj W.obj))
    (hFx : Fx = e.hom ≫ ((upperStar A x).leftDerivedFunctor).map (W.coeffIterate m))
    (xFix : s ⟶ (W.graph m).fix) (hxFix : xFix ≫ (W.graph m).fixι = x) {B : Scheme.{u}}
    (jB : B ⟶ (W.graph m).fix) [IsOpenImmersion jB] [HasCompactification jB]
    (hB : IsClosed (Set.range jB.base)) (hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (jB ≫ (W.graph m).fixStr)] [IsProper (jB ≫ (W.graph m).fixStr)] :
    G.localTerm (W.graph m).fixStr jB hB (G.traceClass (W.graph m) hs hW) =
      MonoidalCategory.trace Fx :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
