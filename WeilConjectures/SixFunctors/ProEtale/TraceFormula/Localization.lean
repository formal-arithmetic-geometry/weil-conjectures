/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing

/-!
# The localization pieces of a Weil complex

Let `(K, φ)` be a Weil complex on `X`, let `i : Z ⟶ X` be a closed immersion and
`j : U ⟶ X` the complementary open immersion. The localization triangle
`Rj_! Lj^* K → K → Ri_* Li^* K →` splits `K` into the two pieces `K^Z = Ri_* Li^* K` and
`K^U = Rj_! Lj^* K`. When `Z` and `U` are stable under the Frobenius iterate `Φ_m`, each piece
carries a coefficient morphism induced by `φ_m`, and the trace class of the graph
correspondence `(1, Φ_m)` is the sum of the trace classes of the two pieces.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.closedPieceObj`,
  `AlgebraicGeometry.ProEtale.WeilComplex.openPieceObj`: the two pieces `K^Z = Ri_* Li^* K`
  and `K^U = Rj_! Lj^* K`.
- `AlgebraicGeometry.ProEtale.WeilComplex.closedPieceCoeff`,
  `AlgebraicGeometry.ProEtale.WeilComplex.openPieceCoeff`: the coefficient morphisms
  `u^Z : LΦ_m^* K^Z ⟶ K^Z` and `u^U : LΦ_m^* K^U ⟶ K^U` induced by `φ_m`. Both are the
  pullback coefficient `WeilComplex.upperStarPullCoeff` followed by a pushforward: along the
  derived base change map `ProEtale.derivedBaseChangeMap` for `u^Z`, along the exceptional
  base change `GeometricOperations.baseChange` for `u^U`.
- `AlgebraicGeometry.ProEtale.WeilComplex.closedPiece`,
  `AlgebraicGeometry.ProEtale.WeilComplex.openPiece`: the two pieces as graph
  endocorrespondences `Correspondence.ofGraph` on `(1, Φ_m)`.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.map_unit_comp_closedPieceCoeff`: the unit
  `K ⟶ K^Z` intertwines `φ_m` and `u^Z`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass_graph_eq_traceClass_add_traceClass`:
  additivity of the trace class along the localization triangle.

## Implementation notes

The closed piece `Z` need not be stable under `Φ₁`, only under `Φ_m`, so for `m > 1` there is
in general no non-zero natural map `LΦ₁^* K^Z ⟶ K^Z`, and the pieces cannot be Weil complexes
for the Frobenius `Φ₁` of `W`. They are endocorrespondences on the graph `(1, Φ_m)` instead,
built with the same constructor `Correspondence.ofGraph` as `W.graph G m`. The three
correspondences therefore share their fixed scheme by construction, so that the additivity
statement is a sum of Borel-Moore sections on `F = Fix(c_m)` with no transport.

The stability of `Z` and `U` under `Φ_m` is data: a morphism `Φ_Z : Z ⟶ Z` with a
commutative square `Φ_Z ≫ i = i ≫ Φ_m`, and a Cartesian square exhibiting `Φ_U : U ⟶ U` as
the restriction of `Φ_m`. The project constructs neither restrictions of `Φ_m` to a closed
or an open subscheme, nor open complements, so these are hypotheses.

`closedPieceCoeff` is an instance of the generic construction `Adjunction.liftAlgebraStr`
rather than the composite `derivedBaseChangeMap ≫ Ri_* (upperStarPullCoeff)` written out:
matching the two against each other up to definitional unfolding makes the kernel unfold the
derived functors and time out, while facts about the generic construction, such as the
compatibility with the unit, are proved once for abstract functors.

The unit `K ⟶ K^Z` intertwines `φ_m` and `u^Z`, which is proved. The analogous statement for
the counit `K^U ⟶ K` needs an open-purity comparison `j^! ≃ Lj^*` compatible with the
adjunction `Rj_! ⊣ j^!`, which the package does not provide, so it is not stated.

The sum in `traceClass_graph_eq_traceClass_add_traceClass` is spelled `Add.add` with an
explicit type argument. The three types agree definitionally but not syntactically, and
the elaborator for `+` compares the types of its operands syntactically, so it needs to be
told which one to use.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}

namespace WeilComplex

variable (W : WeilComplex (A := A) aX)

/-- The closed piece `K^Z = Ri_* Li^* K` of a Weil complex along `i : Z ⟶ X`
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable abbrev closedPieceObj {Z : Scheme.{u}} (i : Z ⟶ X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  ((lowerStar A i).rightDerivedFunctor).obj (((upperStar A i).leftDerivedFunctor).obj W.obj)

/-- The open piece `K^U = Rj_! Lj^* K` of a Weil complex along `j : U ⟶ X`
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable abbrev openPieceObj {U : Scheme.{u}} (j : U ⟶ X) [HasCompactification j] :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (rightDerivedLowerShriek A j).obj (((upperStar A j).leftDerivedFunctor).obj W.obj)

/-- The coefficient morphism `u^Z : LΦ_m^* K^Z ⟶ K^Z` of the closed piece `K^Z = Ri_* Li^* K`,
for a morphism `i : Z ⟶ X` and a lift `Φ_Z` of `Φ_m`,

```
  Z ──i──▶ X
  │Φ_Z     │Φ_m
  ▼        ▼
  Z ──i──▶ X
```

the composite

```
  LΦ_m^* Ri_* Li^* K ──derivedBaseChangeMap──▶ Ri_* LΦ_Z^* Li^* K
    ──Ri_* (upperStarPullCoeff)──▶ Ri_* Li^* K
```

It is defined as `Adjunction.liftAlgebraStr` for `Li^* ⊣ Ri_*` and
`leftDerivedUpperStarSquareIso`, which unfolds to this composite. This is the adjunction
form of the proper pushforward `[i, i]_!(F_{x,m})` of the stalk map
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable def closedPieceCoeff (m : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) (frobZ : Z ⟶ Z)
    (hZ : CommSq frobZ i i (W.frobeniusIterate m)) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj (W.closedPieceObj i) ⟶
      W.closedPieceObj i :=
  (derivedUpperStarLowerStarAdjunction A i).liftAlgebraStr (leftDerivedUpperStarSquareIso A hZ)
    (W.coeffIterate m)

/-- The unit `η : K ⟶ Ri_* Li^* K` intertwines `φ_m` and the coefficient morphism `u^Z` of
the closed piece:

```
  LΦ_m^* K ──LΦ_m^* η──▶ LΦ_m^* K^Z
     │φ_m                   │u^Z
     ▼                      ▼
     K ─────────η────────▶ K^Z
```
-/
lemma map_unit_comp_closedPieceCoeff (m : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) (frobZ : Z ⟶ Z)
    (hZ : CommSq frobZ i i (W.frobeniusIterate m)) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).map
        ((derivedUpperStarLowerStarAdjunction A i).unit.app W.obj) ≫
      W.closedPieceCoeff m i frobZ hZ =
    W.coeffIterate m ≫ (derivedUpperStarLowerStarAdjunction A i).unit.app W.obj :=
  (derivedUpperStarLowerStarAdjunction A i).map_unit_app_comp_liftAlgebraStr _ _

/-- The coefficient morphism of the closed piece of a Weil datum is invertible as soon as
the derived base change map of the square `Φ_Z ≫ i = i ≫ Φ_m` is. -/
instance isIso_closedPieceCoeff [IsIso W.coeff] (m : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X)
    (frobZ : Z ⟶ Z) (hZ : CommSq frobZ i i (W.frobeniusIterate m))
    [IsIso (derivedBaseChangeMap A hZ)] :
    IsIso (W.closedPieceCoeff m i frobZ hZ) := by
  have : IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction A i)
      (derivedUpperStarLowerStarAdjunction A i)
        (leftDerivedUpperStarSquareIso A hZ).hom).natTrans :=
    ‹IsIso (derivedBaseChangeMap A hZ)›
  exact Adjunction.isIso_liftAlgebraStr _ _ _

section Pieces

variable [DerivedBraiding A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The coefficient morphism `u^U : LΦ_m^* K^U ⟶ K^U` of the open piece `K^U = Rj_! Lj^* K`,
for a Cartesian square exhibiting `Φ_U : U ⟶ U` as the restriction of `Φ_m`,

```
  U ──j──▶ X
  │Φ_U  ⌟  │Φ_m
  ▼        ▼
  U ──j──▶ X
```

the composite

```
  LΦ_m^* Rj_! Lj^* K ──baseChange──▶ Rj_! LΦ_U^* Lj^* K ──Rj_! (upperStarPullCoeff)──▶
    Rj_! Lj^* K
```

whose first map is the exceptional base change of the package for that square
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable def openPieceCoeff (G : GeometricOperations A s) (hW : G.ctf X W.obj) (m : ℕ)
    [IsGeometric aX] {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j]
    (frobU : U ⟶ U) (hU : IsPullback frobU j j (W.frobeniusIterate m)) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj (W.openPieceObj j) ⟶
      W.openPieceObj j :=
  have hj : IsGeometricHom s j := .mk (aY := aX) rfl
  have hΦ : IsGeometricHom s (W.frobeniusIterate m) := .mk (W.frobeniusIterate_comp m)
  have hfrobU : IsGeometricHom s frobU := .mk (aX := j ≫ aX) (aY := j ≫ aX)
    (by rw [← Category.assoc, hU.w, Category.assoc, W.frobeniusIterate_comp])
  ((G.baseChange hU hj hΦ hj hfrobU).hom.app
      ⟨_, G.ctf_upperStar j hj hW⟩).hom ≫
    (rightDerivedLowerShriek A j).map (W.upperStarPullCoeff m hU.toCommSq)

/-- The closed piece `K^Z = Ri_* Li^* K` along `i : Z ⟶ X`, for a lift `Φ_Z` of `Φ_m`, as the
graph endocorrespondence on `(1, Φ_m)` with coefficient map `u^Z`, given that `K^Z` lies in
`Dᵇctf(X)` (part of blueprint `sk-d-curve-pieces`). -/
noncomputable abbrev closedPiece (G : GeometricOperations A s) [IsGeometric aX] (m : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ X) (frobZ : Z ⟶ Z) (hZ : CommSq frobZ i i (W.frobeniusIterate m))
    (hKZ : G.ctf X (W.closedPieceObj i)) :
    Correspondence aX aX (W.closedPieceObj i) (W.closedPieceObj i) :=
  Correspondence.ofGraph G aX _ hKZ (W.frobeniusIterate m) (W.frobeniusIterate_comp m)
    (W.closedPieceCoeff m i frobZ hZ)

/-- The open piece `K^U = Rj_! Lj^* K` along `j : U ⟶ X`, for a Cartesian square exhibiting
`Φ_U` as the restriction of `Φ_m`, as the graph endocorrespondence on `(1, Φ_m)` with
coefficient map `u^U`, given that `K^U` lies in `Dᵇctf(X)`
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable abbrev openPiece (G : GeometricOperations A s) (hW : G.ctf X W.obj) (m : ℕ)
    [IsGeometric aX] {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j]
    (frobU : U ⟶ U) (hU : IsPullback frobU j j (W.frobeniusIterate m))
    (hKU : G.ctf X (W.openPieceObj j)) :
    Correspondence aX aX (W.openPieceObj j) (W.openPieceObj j) :=
  Correspondence.ofGraph G aX _ hKU (W.frobeniusIterate m) (W.frobeniusIterate_comp m)
    (W.openPieceCoeff G hW m j frobU hU)

/-- The coefficient morphism of the open piece of a Weil datum is invertible: the exceptional
base change is an isomorphism. -/
instance isIso_openPieceCoeff [IsIso W.coeff] (G : GeometricOperations A s) (hW : G.ctf X W.obj)
    (m : ℕ) [IsGeometric aX] {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [HasCompactification j] (frobU : U ⟶ U)
    (hU : IsPullback frobU j j (W.frobeniusIterate m)) :
    IsIso (W.openPieceCoeff G hW m j frobU hU) := by
  dsimp only [openPieceCoeff]
  have : IsIso (((G.baseChange hU (.mk (aY := aX) rfl) (.mk (W.frobeniusIterate_comp m))
      (.mk (aY := aX) rfl) (.mk (aX := j ≫ aX) (aY := j ≫ aX)
        (by rw [← Category.assoc, hU.w, Category.assoc, W.frobeniusIterate_comp]))).hom.app
      ⟨_, G.ctf_upperStar j (.mk (aY := aX) rfl) hW⟩).hom) :=
    inferInstanceAs (IsIso ((DerivedCategory.constructibleFiniteTor A X).ι.map _))
  infer_instance

end Pieces

end WeilComplex

namespace GeometricOperations

variable [DerivedBraiding A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Localization trace additivity: for a closed immersion `i : Z ⟶ X` and the complementary
open immersion `j : U ⟶ X`, both stable under `Φ_m`, the three coefficient morphisms `φ_m`,
`u^Z` and `u^U` form a morphism of the distinguished triangle of the open-closed
decomposition, compatibly with `Lc₂^*` and `Rc₁^!`, so triangle compatibility of the Verdier
trace class gives

`Tr_{(1, Φ_m)}(φ_m) = Tr_{(1, Φ_m)}(u^Z) + Tr_{(1, Φ_m)}(u^U)`

in the group of Borel-Moore sections `A_F ⟶ ω_F` on the fixed scheme `F`. The lifts `Φ_Z`
and `Φ_U` of `Φ_m` are data because the project cannot construct restrictions of `Φ_m` to
a closed or open subscheme (blueprint: `sk-i-additivity`). -/
theorem traceClass_graph_eq_traceClass_add_traceClass (G : GeometricOperations A s)
    [s.IsSpecOfField] [HasCompactification aX] [QuasiCompact aX]
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ) {Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (frobZ : Z ⟶ Z) (hZ : CommSq frobZ i i (W.frobeniusIterate m)) (frobU : U ⟶ U)
    (hU : IsPullback frobU j j (W.frobeniusIterate m))
    (hKZ : G.ctf X (W.closedPieceObj i)) (hKU : G.ctf X (W.openPieceObj j))
    [HasCompactification (W.graph G hW m).toProd]
    [HasCompactification (W.closedPiece G m i frobZ hZ hKZ).toProd]
    [HasCompactification (W.openPiece G hW m j frobU hU hKU).toProd] :
    G.traceClass (W.graph G hW m) hW =
      Add.add (α := G.borelMooreSections (W.graph G hW m).fixStr)
        (G.traceClass (W.closedPiece G m i frobZ hZ hKZ) hKZ)
        (G.traceClass (W.openPiece G hW m j frobU hU hKU) hKU) :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
