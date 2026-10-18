/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.Paper.RingedTopoiDerivedPullback

/-!
# Shift compatibility of a derived adjunction

Source: Stacks Project, sites-cohomology.tex Tags 07A6 and 0B56, and derived.tex
Tag 0A8D (blueprint: lem-weil-pbc-derived-adjunction-shift).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD r wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical derived ringed-topos adjunction is compatible with its resolution shifts.
Source: Stacks Project, Tags 07A6, 0FND, 0DVC and 0A8D
(blueprint: lem-weil-pbc-derived-adjunction-shift).

The module pullback is fixed on objects and maps by the tensor/change-of-rings formula.
Its right adjoint `G` represents the module direct image. The comparison transformations
`α` and `β` specify the universal derived functors. Their `NatTrans.CommShift` instances
express the resolution normalization of the displayed, already fixed shift structures.
The equation `normalization` is the normalized derived Hom bijection, so the derived
adjunction is the one induced by the original module adjunction.

Proof:
1. The termwise module adjunction induces the homotopy adjunction
   (`lem-weil-pbc-termwise-adjunction-homotopy`). Additivity makes its Hom bijection
   commute with every integer shift, including the differential sign.
2. K-flat complexes with flat terms remain so after shifting: on tensor summand (i,j),
   the comparison multiplies by (-1)^(n*i). K-injectives remain K-injective by
   `lem-weil-pbc-kinjective-shift`. Shifted quasi-isomorphisms remain quasi-isomorphisms.
3. The shift comparisons are characterized by commutation with α and β. On K-flat
   sources and K-injective targets these transformations are invertible, by
   `lem-weil-pbc-ringed-topoi-derived-pullback` and `def-sfb-right-derived-functor`.
4. The normalized pre-derived Hom bijection
   (`lem-pc-pre-derived-adjoint-functors-general`, `lem-pc-derived-adjoint-functors`)
   sends α followed by Q(t) to Q(T(t)) followed by β; this is `normalization`.
5. Apply this formula to shifted representatives and use Step 1 and the two comparison
   normalizations. The Hom bijection intertwines the fixed shifts.
6. Every source has a K-flat resolution (`lem-pc-kflat-resolution`) and every target
   a K-injective resolution (`prop-pur-kinjective-resolutions-exist`). Naturality and
   cancellation of the resolution isomorphisms extend Step 5 to all objects.
7. Specialize the Hom identity to the identity of L(A). This gives the unit equation.
8. Apply `lem-weil-pbc-adjunction-shift-compatibility-unique` to obtain the counit
   equation and uniqueness of each right comparison from the unit equation. This is
   uniqueness among all natural shift isomorphisms, without a coherence assumption.
-/
theorem derivedAdjunctionShiftCompatible
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {RY : Sheaf JC CommRingCat.{r}} {RX RI : Sheaf JD CommRingCat.{r}}
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (toposAdj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : SheafOfModules.AlgebraicInverseImage uInv RY RI) (c : RI ⟶ RX)
    (F : SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY) ⥤
      SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX))
    (hobj : ∀ M : SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY),
      F.obj M = SheafOfModules.changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)} (f : M ⟶ N),
      F.map f = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
          eqToHom (hobj N).symm)
    (G : SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX) ⥤
      SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY))
    [F.Additive] [G.Additive] (adj₀ : F ⊣ G)
    [HasDerivedCategory.{wA} (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY))]
    [HasDerivedCategory.{wB} (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX))]
    (L : DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)) ⥤
      DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)))
    (R : DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)) ⥤
      DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hL : L.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)) (ComplexShape.up ℤ)))
    (hR : R.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)) (ComplexShape.up ℤ)))
    (adj : L ⊣ R)
    (normalization : ∀
      (M : HomotopyCategory (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)) (ComplexShape.up ℤ))
      (K : HomotopyCategory (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)) (ComplexShape.up ℤ))
      (f : (F.mapHomotopyCategory (ComplexShape.up ℤ)).obj M ⟶ K),
      adj.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
        (α.app M ≫ DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map ((adj₀.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv M K f)
        ≫ β.app K)
    [L.CommShift ℤ] [R.CommShift ℤ]
    [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ] :
    (∀ n : ℤ, Adjunction.CommShift.CompatibilityUnit adj
      (L.commShiftIso n) (R.commShiftIso n)) ∧
    (∀ n : ℤ, Adjunction.CommShift.CompatibilityCounit adj
      (L.commShiftIso n) (R.commShiftIso n)) ∧
    (∀ (n : ℤ) (e : shiftFunctor _ n ⋙ R ≅ R ⋙ shiftFunctor _ n),
      Adjunction.CommShift.CompatibilityUnit adj (L.commShiftIso n) e →
        e = R.commShiftIso n) := by
  sorry

end CategoryTheory
