/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso

/-!
# Higher-image cohomology square

Source: Stacks Project, Tag 0EYM, lemma-relative-colimit-general, second proof,
the canonical commutative diagram and its stage/limit maps (etale-cohomology.tex
lines 7654--7719), together with Tag 03Q8 (blueprint:
lem-sf-higher-image-cohomology-square).

The definitions below spell out the fibre-product objects, the induced coefficient
map, the canonical cohomology-presheaf maps, and the sectionwise transition map.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The fibre-product scheme `Z = W ×_S Y` used in the source square.
Source: Stacks Project, Tag 0EYM (blueprint: lem-sf-higher-image-cohomology-square). -/
noncomputable def higherImageCohomologySquareZ {Y S : Scheme.{u}} (h : Y ⟶ S) (W : S.Etale) :
    Scheme.{u} :=
  Limits.pullback W.hom h

/-- The fibre-product scheme `Z' = W' ×_{S'} Y'` used in the source square.
Source: Stacks Project, Tag 0EYM (blueprint: lem-sf-higher-image-cohomology-square). -/
noncomputable def higherImageCohomologySquareZ' {Y' S' : Scheme.{u}} (h' : Y' ⟶ S')
    (W' : S'.Etale) : Scheme.{u} :=
  Limits.pullback W'.hom h'

/-- The canonical map `α : Z' ⟶ Z` induced by `v` and `a`.
Source: Stacks Project, Tag 0EYM (blueprint: lem-sf-higher-image-cohomology-square). -/
noncomputable def higherImageCohomologySquareAlpha
    {Y Y' S S' : Scheme.{u}} {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b) {W : S.Etale} {W' : S'.Etale} (v : W'.left ⟶ W.left)
    (hv : v ≫ W.hom = W'.hom ≫ b) :
    higherImageCohomologySquareZ' h' W' ⟶ higherImageCohomologySquareZ h W :=
  Limits.pullback.lift
    (Limits.pullback.fst W'.hom h' ≫ v)
    (Limits.pullback.snd W'.hom h' ≫ a) (by
      simp only [Category.assoc]
      rw [hv, ← Category.assoc, Limits.pullback.condition, Category.assoc, ← sq.w])

/-- The coefficient map `φ_Z : α⁻¹(F|_Z) ⟶ F'|_{Z'}`.
Source: Stacks Project, Tag 0EYM and Tag 03Q8 (blueprint:
lem-sf-higher-image-cohomology-square).
-/
noncomputable def higherImageCohomologySquareCoefficient
    {Y Y' S S' : Scheme.{u}} {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b) {W : S.Etale} {W' : S'.Etale} (v : W'.left ⟶ W.left)
    (hv : v ≫ W.hom = W'.hom ≫ b)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F') :
    (upperStar AddCommGrpCat.{u + 1} (higherImageCohomologySquareAlpha sq v hv)).obj
        ((upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd W.hom h)).obj F) ⟶
      (upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd W'.hom h')).obj F' := by
  let α := higherImageCohomologySquareAlpha sq v hv
  let j := Limits.pullback.snd W.hom h
  let j' := Limits.pullback.snd W'.hom h'
  have hj : α ≫ j = j' ≫ a := by
    simp [α, j, j', higherImageCohomologySquareAlpha]
  exact (upperStarComp AddCommGrpCat.{u + 1} α j (α ≫ j) rfl).inv.app F ≫
    (eqToIso (congrArg (fun k : higherImageCohomologySquareZ' h' W' ⟶ Y =>
      (upperStar AddCommGrpCat.{u + 1} k).obj F) hj)).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} j' a (j' ≫ a) rfl).hom.app F ≫
        ((upperStar AddCommGrpCat.{u + 1} j').map φ)

/-- The canonical section map `ε_{h,F,W}` from the restricted-cohomology presentation
to the degree-`p` direct image section.
Source: Stacks Project, Tag 03Q8 (blueprint: lem-sf-higher-image-cohomology-square). -/
noncomputable def higherImageCohomologySquareEpsilon
    {Y S : Scheme.{u}} (h : Y ⟶ S)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) (W : S.Etale) :
    rawAffineRestrictedCohomology h p F W ⟶
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op W) :=
  letI : IsIso (rawRestrictedCohomologyComparison h p F W) :=
    isIso_rawRestrictedCohomologyComparison h p F W
  (asIso (rawRestrictedCohomologyComparison h p F W)).inv ≫
    (higherDirectImagePresheafToHomologyAbelian h (p : ℤ)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).app (op W)

/-- The canonical cohomology map `H^p(φ_Z) ∘ α^*`, with `α^*` given by the
derived cohomology pullback on the fibre-product schemes.
Source: Stacks Project, Tags 01F8--01FA and 0EYM (blueprint:
lem-sf-higher-image-cohomology-square).
-/
noncomputable def higherImageCohomologySquareCohomologyMap
    {Y Y' S S' : Scheme.{u}} {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b) {W : S.Etale} {W' : S'.Etale} (v : W'.left ⟶ W.left)
    (hv : v ≫ W.hom = W'.hom ≫ b) (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F') :
    rawAffineRestrictedCohomology h p F W ⟶ rawAffineRestrictedCohomology h' p F' W' := by
  let α := higherImageCohomologySquareAlpha sq v hv
  let R := (upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd W.hom h)).obj F
  exact rawAffineComplexPullback (p : ℤ) α
      ((CochainComplex.singleFunctor _ 0).obj R) ≫
    (cohomology AddCommGrpCat.{u + 1} (Limits.pullback W'.hom h') (p : ℤ)).map
      (DerivedCategory.Q.map
        (((upperStar AddCommGrpCat.{u + 1} α).mapCochainComplexSingleFunctor 0).hom.app R ≫
          (CochainComplex.singleFunctor _ 0).map
            (higherImageCohomologySquareCoefficient sq v hv F F' φ)))

/-- The transition `t_{W,W'}`: the `b`-unit, the degree-`p` exchange on
`W ×_S S'`, and restriction along `W' ⟶ W ×_S S'`.
Source: Stacks Project, Tag 0EYM (blueprint: lem-sf-higher-image-cohomology-square). -/
noncomputable def higherImageCohomologySquareTransition
    {Y Y' S S' : Scheme.{u}} {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F') (p : ℕ)
    {W : S.Etale} {W' : S'.Etale} (v : W'.left ⟶ W.left)
    (hv : v ≫ W.hom = W'.hom ≫ b) :
    (((DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op W)) ⟶
      (((DerivedCategory.Plus.homologyFunctor
        (Sheaf S'.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h').obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F'))).obj.obj (op W')) := by
  let H := (DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  let U := (MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) b).obj W
  let l : W' ⟶ U := MorphismProperty.Over.homMk
    (Limits.pullback.lift v W'.hom (by simpa [U] using hv)) (by
      simp [U])
  exact ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).unit.app H).hom.app
      (op W) ≫
    ((upperStar AddCommGrpCat.{u + 1} b).obj H).obj.map l.op ≫
      (relativeHigherDirectImageExchange sq F F' φ p).hom.app (op W')

/-- For every test-object square, the canonical cohomology-presheaf map commutes with
the derived higher-image exchange.

The proof follows the six steps in the second proof of Stacks Project Tag 0EYM
(`etale-cohomology.tex`, lines 7654--7719), together with the cocycle formula of
Tag 03Q8:

1. Choose bounded-below K-injective resolutions `s : F[0] ⟶ I` and
   `s' : F'[0] ⟶ J`. Exactness of inverse image makes `a⁻¹s` a quasi-isomorphism,
   so the K-injective Hom bijection represents `φ[0]` by a chain map
   `β : a⁻¹I ⟶ J`; put `C = h_*I` and `D = h'_*J`.
2. Form the inverse-image composition comparison `θ`, the mate `r`, and the
   direct-image map `T` using the units and counits. Form the direct-image
   comparison `e`, the map `u = a_*β ≫ η_a`, and `k = e ≫ h_*u`; unit compatibility,
   naturality, and the triangle identity give `k = b_*T ≫ η_b`.
3. Transpose `QT` under the derived adjunction. The derived counit, derived
   inverse-image composition comparison, and the representative `β` identify this
   transpose with the prescribed commutative-square exchange followed by
   `Rh'_* (φ[0])`. Taking degree-`p` homology gives the map `τ` in the statement.
4. Let `j : Z ⟶ Y` and `j' : Z' ⟶ Y'` be the projections. They are étale by base
   change, and restriction preserves injectives, so `I|_Z` and `J|_{Z'}` compute the
   two cohomologies. The canonical higher-direct-image presheaf maps are the
   cocycle-to-cohomology-sheaf maps, hence are exactly `ε` on both sides.
5. Put `U = W ×_S S'` and let `l : W' ⟶ U` be induced by `v`. Expanding `k` on
   sections gives a chain map `R : I(Z) ⟶ J(Z')` consisting of the `b`-unit,
   exchange, and restriction. With `δ = (α,j')`, the fibre-product formula and
   inverse-image composition identify `R` with the unit map for `α` followed by a
   chain map representing `φ_Z`. The K-injective Hom bijection then gives
   `H^p(R) = H^p(φ_Z) ∘ α^*`.
6. Chase a cocycle `z ∈ C^p(W)` through the unit, `T`, restriction, and the chain
   map `R`. Exact inverse image preserves cycles and boundaries, so both sides send
   the cohomology-sheaf class of `z` to the class of `R(z)`. This proves the displayed
   section equation, with no cartesian, torsion, or qcqs hypothesis.

Source: Stacks Project, Tag 0EYM, lemma-relative-colimit-general, second proof,
`etale-cohomology.tex` lines 7654--7719, and Tag 03Q8 (blueprint:
`lem-sf-higher-image-cohomology-square`).
-/
theorem higherImageCohomologySquare
    {Y Y' S S' : Scheme.{u}}
    {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F')
    (p : ℕ) {W : S.Etale} {W' : S'.Etale}
    (v : W'.left ⟶ W.left)
    (hv : v ≫ W.hom = W'.hom ≫ b) :
    higherImageCohomologySquareEpsilon h F p W ≫
        higherImageCohomologySquareTransition sq F F' φ p v hv =
      higherImageCohomologySquareCohomologyMap sq v hv p F F' φ ≫
        higherImageCohomologySquareEpsilon h' F' p W' := by
  sorry

end AlgebraicGeometry.Etale
