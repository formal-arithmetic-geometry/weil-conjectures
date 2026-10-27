/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Dual Tate normalization of a supported Cartier orientation

Source: ILO Expose XVI, Section 2.1; the supported Cartier Kummer construction;
Stacks Project, Tags 03PK and 0EYM.
(blueprint: def-sfb-cartier-dual-kummer-normalization).

## Main definitions

- `twistPullback`: the canonical generator-normalized signed Tate transport.
- `closedDual`: the pushed-forward dual Tate sheaf, in degree zero.
- `closedEvaluation`: its pairing with the ambient Tate line by the closed adjunction.
- `KummerNormalized`: the exact Ext equation normalizing a candidate purity isomorphism.
- `closedExchange`: closed exchange followed by reduction for a commuting divisor square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.RamifiedRoot
variable (A : Type (u + 1)) [CommRing A]

/-- Canonical signed Tate transport, fixed by roots generators and tensor duality.
The normalized theorem fixes the line map on generating pure tensors; thus this
choice is determined, rather than chosen from a mere existence of isomorphisms.
Source: Stacks 03PK (blueprint: def-sfb-cartier-dual-kummer-normalization). -/
def twistPullback (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (h : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) (a : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) h).obj (Scheme.finiteEtaleTateSheaf A N Y hA a) ≅
      Scheme.finiteEtaleTateSheaf A N X hA a :=
  IntTensorFamily.iso
    ((Scheme.finiteEtaleTateTensorFamily Y N hN A hA hY).map
      (upperStar (ModuleCat.{u + 1} A) h))
    (Scheme.finiteEtaleTateTensorFamily X N hN A hA hX)
    ((Scheme.finiteEtaleTateLine_pullback_normalized A N hN hA).choose h hY) a

/-- The closed supported dual Tate sheaf in degree zero. Its shift by -2 is the
source of purity. Source: ILO XVI 2.1
(blueprint: def-sfb-cartier-dual-kummer-normalization). -/
def closedDual (N : ℕ) (hA : (N : A) = 0) {D X : Scheme.{u}} (i : D ⟶ X) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((lowerStar (ModuleCat.{u + 1} A) i).obj (Scheme.finiteEtaleTateSheaf A N D hA (-1)))

/-- Evaluation of the ambient line against the pushed-forward dual, by adjunction.
This uses the canonical counit, not a projection-formula isomorphism as extra data.
Source: ILO XVI 2.1 (blueprint: def-sfb-cartier-dual-kummer-normalization). -/
def closedEvaluation (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {D X : Scheme.{u}} (i : D ⟶ X) (hX : IsUnit (N : Γ(X, ⊤)))
    (hD : IsUnit (N : Γ(D, ⊤))) :
    Scheme.finiteEtaleTateLine X N A hA ⊗
        (lowerStar (ModuleCat.{u + 1} A) i).obj
          (Scheme.finiteEtaleTateSheaf A N D hA (-1)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
    (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) i) _ _ ≫
      tensorHom (twistPullback A N hN hA i hX hD 1).hom
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app _) ≫
      (ihom.ev (Scheme.finiteEtaleTateLine D N A hA)).app (ordinaryFiniteConstant A D))

/-- A purity isomorphism has the supported Kummer normalization precisely when
its forget-support map, after tensor evaluation, is the normalized boundary class.
Here the isomorphism is written S[0] ≅ K[2], equivalently S[-2] ≅ K.
Source: ILO XVI 2.1 (blueprint: def-sfb-cartier-dual-kummer-normalization). -/
def KummerNormalized (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hX : IsUnit (N : Γ(X, ⊤)))
    (hD : IsUnit (N : Γ(D, ⊤)))
    (K : DerivedCategoryModule A X) (ι : K ⟶ ordinaryFiniteUnit A X)
    (P : closedDual A N hA i ≅ K⟦(2 : ℤ)⟧) : Prop :=
  letI : PreservesFiniteLimits (tensorLeft (Scheme.finiteEtaleTateLine X N A hA)) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).mp
      (ObjectProperty.flat_of_tensorIso
        (Scheme.finiteEtaleTateLineInverse X N hN A hA hX).rightIso)
  ∃ κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine X N A hA) 2,
    SupportedKummerBoundary A N hA i hI hX κ ∧
    (Ext.mk₀ (closedEvaluation A N hN hA i hX hD)).comp κ (zero_add 2) =
      ((show Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj
          (Scheme.finiteEtaleTateSheaf A N D hA (-1))) (ordinaryFiniteConstant A X) 2 from
        Ext.homEquiv.symm (P.hom ≫ ι⟦(2 : ℤ)⟧')).mapExactFunctor
          (tensorLeft (Scheme.finiteEtaleTateLine X N A hA))).comp
            (Ext.mk₀ (ρ_ (Scheme.finiteEtaleTateLine X N A hA)).hom) (add_zero 2)

/-- The closed exchange followed by the actual reduction map is the ordinary
sheaf mate for the reduced square. The square need only commute; in particular
it is not incorrectly asserted Cartesian when the exponent exceeds one.
Source: ILO XVI 2.1 (blueprint: def-sfb-cartier-dual-kummer-normalization). -/
def closedExchange (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {D D' X X' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
    {h : X' ⟶ X} {d : D' ⟶ D} (sq : CommSq d i' i h)
    (hD : IsUnit (N : Γ(D, ⊤))) (hD' : IsUnit (N : Γ(D', ⊤))) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj (closedDual A N hA i) ⟶
      closedDual A N hA i' :=
  ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((baseChangeMap (ModuleCat.{u + 1} A) sq).app _ ≫
        (lowerStar (ModuleCat.{u + 1} A) i').map
          (twistPullback A N hN hA d hD hD' (-1)).hom)

end AlgebraicGeometry.Etale.RamifiedRoot
