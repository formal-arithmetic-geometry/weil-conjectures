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

- `AlgebraicGeometry.ProEtale.WeilComplex.closedPieceCoeff`,
  `AlgebraicGeometry.ProEtale.WeilComplex.openPieceCoeff`: the coefficient morphisms
  `u^Z : LΦ_m^* K^Z ⟶ K^Z` and `u^U : LΦ_m^* K^U ⟶ K^U` induced by `φ_m` on the two pieces.
- `AlgebraicGeometry.ProEtale.WeilComplex.closedPiece`,
  `AlgebraicGeometry.ProEtale.WeilComplex.openPiece`: the two pieces `K^Z` and `K^U` of
  the localization triangle, as endocorrespondences on the graph `(1, Φ_m)`.

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
the fixed scheme is taken as data. Isolatedness of the fixed
point, which the blueprint derives from the vanishing of the map induced by `Φ_m` on the
cotangent space, is therefore assumed rather than proved.

The closed point `Z = {x̄}` is stable under `Φ_m` but in general not under `Φ₁`, so for
`m > 1` there is no non-zero natural map `LΦ₁^* K^Z ⟶ K^Z`, and the pieces cannot be Weil
complexes for the Frobenius `Φ₁` of `W`. As in the blueprint, which base changes to
`𝐅_{q^m}`, `Φ_m` plays the role of the one-step Frobenius: the pieces are
endocorrespondences on the graph `(1, Φ_m)`, with the same legs as `W.graph G m`. The three
correspondences therefore literally share their fixed scheme, so that the additivity
statement is a genuine sum of Borel-Moore sections on `F = Fix(c_m)` with no transport.
The stability of `Z` and `U` under `Φ_m` is data: a morphism `Φ_Z : Z ⟶ Z` with
`i ≫ Φ_m = Φ_Z ≫ i`, and a Cartesian square exhibiting `Φ_U : U ⟶ U` as the restriction
of `Φ_m`. The coefficient morphisms are built from these, from the exceptional base change
of the package and from the adjunction `Li^* ⊣ Ri_*`.

The trace class needs `a_X` separated, locally of finite type and quasi-compact. The first
two are instances derived from `HasCompactification aX` (`HasCompactification.isSeparated`
and `HasCompactification.locallyOfFiniteType`), so the statements only add
`[QuasiCompact aX]`.

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
  [Abelian.HasFunctorialFlatResolution A] [DerivedBraiding A] {s X : Scheme.{u}} {aX : X ⟶ s}

namespace WeilComplex

variable (W : WeilComplex (A := A) aX)

/-- The coefficient morphism `u^Z : LΦ_m^* K^Z ⟶ K^Z` of the closed piece
`K^Z = Ri_* Li^* K`, for a closed point `i : Z ⟶ X` stable under `Φ_m` with restriction
`Φ_Z`: under `Li^* ⊣ Ri_*` it corresponds to the composite

```
  Li^* LΦ_m^* Ri_* Li^* K ≃ LΦ_Z^* Li^* Ri_* Li^* K ──LΦ_Z^* ε──▶ LΦ_Z^* Li^* K
    ≃ Li^* LΦ_m^* K ──Li^* φ_m──▶ Li^* K
```

where the isomorphisms come from `i ≫ Φ_m = Φ_Z ≫ i`. This is the adjunction form of the
proper pushforward `[i, i]_!(F_{x,m})` of the stalk map (part of blueprint
`sk-d-curve-pieces`). -/
noncomputable def closedPieceCoeff (m : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) (frobZ : Z ⟶ Z)
    (hZ : i ≫ W.frobeniusIterate m = frobZ ≫ i) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj
        (((lowerStar A i).rightDerivedFunctor).obj
          (((upperStar A i).leftDerivedFunctor).obj W.obj)) ⟶
      ((lowerStar A i).rightDerivedFunctor).obj
        (((upperStar A i).leftDerivedFunctor).obj W.obj) :=
  ((derivedUpperStarLowerStarAdjunction A i).homEquiv _ _)
    (((leftDerivedUpperStarComp A i (W.frobeniusIterate m)).symm ≪≫
        leftDerivedUpperStarCongr A hZ ≪≫ leftDerivedUpperStarComp A frobZ i).hom.app _ ≫
      ((upperStar A frobZ).leftDerivedFunctor).map
        ((derivedUpperStarLowerStarAdjunction A i).counit.app
          (((upperStar A i).leftDerivedFunctor).obj W.obj)) ≫
      ((leftDerivedUpperStarComp A frobZ i).symm ≪≫ leftDerivedUpperStarCongr A hZ.symm ≪≫
        leftDerivedUpperStarComp A i (W.frobeniusIterate m)).hom.app W.obj ≫
      ((upperStar A i).leftDerivedFunctor).map (W.coeffIterate m))

/-- The coefficient morphism `u^U : LΦ_m^* K^U ⟶ K^U` of the open piece `K^U = Rj_! Lj^* K`,
for an open immersion `j : U ⟶ X` and a Cartesian square exhibiting `Φ_U : U ⟶ U` as the
restriction of `Φ_m`: the composite

```
  LΦ_m^* Rj_! Lj^* K ≃ Rj_! LΦ_U^* Lj^* K ≃ Rj_! Lj^* LΦ_m^* K
    ──Rj_! Lj^* φ_m──▶ Rj_! Lj^* K
```

whose first map is `!`-base change for that square (part of blueprint
`sk-d-curve-pieces`). -/
noncomputable def openPieceCoeff (G : GeometricOperations A s) (m : ℕ) {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j] (frobU : U ⟶ U)
    (sq : IsPullback frobU j j (W.frobeniusIterate m)) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj
        ((rightDerivedLowerShriek A j).obj
          (((upperStar A j).leftDerivedFunctor).obj W.obj)) ⟶
      (rightDerivedLowerShriek A j).obj
        (((upperStar A j).leftDerivedFunctor).obj W.obj) :=
  (G.baseChange sq).hom.app (((upperStar A j).leftDerivedFunctor).obj W.obj) ≫
    (rightDerivedLowerShriek A j).map
      (((leftDerivedUpperStarComp A frobU j).symm ≪≫ leftDerivedUpperStarCongr A sq.w ≪≫
          leftDerivedUpperStarComp A j (W.frobeniusIterate m)).hom.app W.obj ≫
        ((upperStar A j).leftDerivedFunctor).map (W.coeffIterate m))

/-- The closed piece `K^Z = Ri_* Li^* K` of the localization triangle of a Weil complex on a
curve at a closed point `i : Z ⟶ X` stable under `Φ_m`, as an endocorrespondence on the
graph `(1, Φ_m)` with coefficient map `u^Z` read through `K^Z ≃ 𝟙^! K^Z`
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable def closedPiece (G : GeometricOperations A s) (m : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (frobZ : Z ⟶ Z)
    (hZ : i ≫ W.frobeniusIterate m = frobZ ≫ i) :
    Correspondence aX aX
      (((lowerStar A i).rightDerivedFunctor).obj (((upperStar A i).leftDerivedFunctor).obj W.obj))
      (((lowerStar A i).rightDerivedFunctor).obj
        (((upperStar A i).leftDerivedFunctor).obj W.obj)) where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := W.frobeniusIterate m
  fst_comp := Category.id_comp aX
  snd_comp := W.frobeniusIterate_comp m
  coeff := W.closedPieceCoeff m i frobZ hZ ≫ (G.upperShriekIdIso X).hom.app _

/-- The open piece `K^U = Rj_! Lj^* K` of the localization triangle of a Weil complex on a
curve along an open immersion `j : U ⟶ X` stable under `Φ_m`, as an endocorrespondence on
the graph `(1, Φ_m)` with coefficient map `u^U` read through `K^U ≃ 𝟙^! K^U`
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable def openPiece (G : GeometricOperations A s) (m : ℕ) {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j] (frobU : U ⟶ U)
    (sq : IsPullback frobU j j (W.frobeniusIterate m)) :
    Correspondence aX aX
      ((rightDerivedLowerShriek A j).obj (((upperStar A j).leftDerivedFunctor).obj W.obj))
      ((rightDerivedLowerShriek A j).obj (((upperStar A j).leftDerivedFunctor).obj W.obj)) where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := W.frobeniusIterate m
  fst_comp := Category.id_comp aX
  snd_comp := W.frobeniusIterate_comp m
  coeff := W.openPieceCoeff G m j frobU sq ≫ (G.upperShriekIdIso X).hom.app _

/-- The support map of the closed piece is that of the graph `W.graph G m`, hence a closed
immersion when `aX` is separated. -/
instance isClosedImmersion_closedPiece_toProd [IsSeparated aX] (G : GeometricOperations A s)
    (m : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (frobZ : Z ⟶ Z)
    (hZ : i ≫ W.frobeniusIterate m = frobZ ≫ i) :
    IsClosedImmersion (W.closedPiece G m i frobZ hZ).toProd :=
  inferInstanceAs (IsClosedImmersion (W.graph G m).toProd)

/-- The support map of the open piece is that of the graph `W.graph G m`, hence a closed
immersion when `aX` is separated. -/
instance isClosedImmersion_openPiece_toProd [IsSeparated aX] (G : GeometricOperations A s)
    (m : ℕ) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j]
    (frobU : U ⟶ U) (sq : IsPullback frobU j j (W.frobeniusIterate m)) :
    IsClosedImmersion (W.openPiece G m j frobU sq).toProd :=
  inferInstanceAs (IsClosedImmersion (W.graph G m).toProd)

end WeilComplex

namespace GeometricOperations

/-- Zero-stalk vanishing on a smooth curve: a geometric point `x̄` fixed by `Φ_m` is an
isolated, hence open-and-closed, component `B` of the fixed scheme `Fix(c_m)` of the graph
correspondence `c_m = (1, Φ_m)`; purity in relative dimension zero computes the trace class
there from the pair `(K_x̄, u_x̄)` alone, so if the geometric stalk `K_x̄` vanishes then so
does the local term `LT_x̄(φ_m)` (blueprint: `sk-i-curve-zero`). -/
theorem localTerm_traceClass_eq_zero_of_isZero [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s)
    [s.IsSpecOfField] [HasCompactification aX] [QuasiCompact aX]
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) (xFix : s ⟶ (W.graph G m).fix)
    (hxFix : xFix ≫ (W.graph G m).fixι = x) {B : Scheme.{u}} (jB : B ⟶ (W.graph G m).fix)
    [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base))
    (hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (jB ≫ (W.graph G m).fixStr)] [IsProper (jB ≫ (W.graph G m).fixStr)]
    (hstalk : IsZero (((upperStar A x).leftDerivedFunctor).obj W.obj)) :
    G.localTerm (W.graph G m).fixStr jB hB (G.traceClass (W.graph G m) hW) = 0 :=
  sorry

/-- Localization trace additivity: the three coefficient morphisms `φ_m`, `u^Z` and `u^U`
form a morphism of the distinguished triangle of the open-closed decomposition, compatibly
with `Lc₂^*` and `Rc₁^!`, so triangle compatibility of the Verdier trace class gives

`Tr_{(1, Φ_m)}(φ_m) = Tr_{(1, Φ_m)}(u^Z) + Tr_{(1, Φ_m)}(u^U)`

in the group of Borel-Moore sections `A_F ⟶ ω_F` on the fixed scheme `F`
(blueprint: `sk-i-additivity`). -/
theorem traceClass_graph_eq_traceClass_add_traceClass [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s)
    [s.IsSpecOfField] [HasCompactification aX] [QuasiCompact aX]
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) {Z U : Scheme.{u}} (i : Z ⟶ X)
    (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [HasCompactification j]
    (hi : Set.range i.base = Set.range x.base)
    (hj : Set.range j.base = (Set.range x.base)ᶜ)
    (frobZ : Z ⟶ Z) (hZ : i ≫ W.frobeniusIterate m = frobZ ≫ i) (frobU : U ⟶ U)
    (sqU : IsPullback frobU j j (W.frobeniusIterate m))
    (hKZ : G.ctf X (((lowerStar A i).rightDerivedFunctor).obj
      (((upperStar A i).leftDerivedFunctor).obj W.obj)))
    (hKU : G.ctf X ((rightDerivedLowerShriek A j).obj
      (((upperStar A j).leftDerivedFunctor).obj W.obj))) :
    G.traceClass (W.graph G m) hW =
      Add.add (α := G.borelMooreSections (W.graph G m).fixStr)
        (G.traceClass (W.closedPiece G m i frobZ hZ) hKZ)
        (G.traceClass (W.openPiece G m j frobU sqU) hKU) :=
  sorry

/-- Frobenius local terms on smooth curves: the local term of the graph correspondence
`c_m = (1, Φ_m)` at a geometric point `x̄` fixed by `Φ_m` is the categorical trace of
Frobenius on the geometric stalk,

`LT_x̄(φ_m) = tr_A(F_{x,m} ∣ K_x̄)`, where `F_{x,m}` is `W.stalkFrobenius m x hx`.

No local constancy of `K` at `x̄` is assumed (blueprint: `sk-p-frob`). -/
theorem localTerm_traceClass_eq_trace [SmoothOfRelativeDimension 1 aX]
    (G : GeometricOperations A s)
    [s.IsSpecOfField] [HasCompactification aX] [QuasiCompact aX]
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x)
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    (xFix : s ⟶ (W.graph G m).fix) (hxFix : xFix ≫ (W.graph G m).fixι = x) {B : Scheme.{u}}
    (jB : B ⟶ (W.graph G m).fix) [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base))
    (hBx : Set.range jB.base = Set.range xFix.base)
    [HasCompactification (jB ≫ (W.graph G m).fixStr)] [IsProper (jB ≫ (W.graph G m).fixStr)] :
    G.localTerm (W.graph G m).fixStr jB hB (G.traceClass (W.graph G m) hW) =
      MonoidalCategory.trace (W.stalkFrobenius m x hx) :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
