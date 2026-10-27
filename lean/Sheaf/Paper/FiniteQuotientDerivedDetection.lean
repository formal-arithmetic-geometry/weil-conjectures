/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TowerClassFinite
import all Sheaf.Paper.TowerClassFiniteUnit
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.Paper.FiniteInjectiveSectionsAcyclic
import Sheaf.Paper.FiniteQuotientHomBijective
import Sheaf.Paper.FiniteDerivedRestrictionBijective
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Detection of finite coefficient classes on the integral generator

Source: diagonal-tower trace (1), scalar Kummer normalization; the constant-module
class comparison in Stacks 03FD.
(blueprint: lem-sfb-finite-quotient-derived-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses



variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Forgetting coefficients and evaluating on the integral generator detects derived
arrows out of the regular finite coefficient sheaf, with any finite-module target.

Source: diagonal-tower trace (1), constants/scalar-extension adjunction; Stacks 03FD.
(blueprint: lem-sfb-finite-quotient-derived-detection).

Proof: the evaluated coefficient object is the regular module over the constant
finite coefficient ring sheaf. Maps from it are global sections by evaluation at
one. Maps from the integral constant sheaf to an underlying abelian sheaf are
also global sections by evaluation at one. The characterization of finiteQuotient
identifies these degree-zero comparisons. Resolve the target by injective module
sheaves. Their underlying abelian sheaves are acyclic for global sections,
by the injective-module resolution computation of underlying sheaf cohomology
in Stacks 03FD. This computation applies to a ringed site, and requires no
flatness of the coefficient ring as an abelian group. It identifies the two
universal delta functors, rather than asserting that the forgetful functor
preserves injectives. Dimension shifting extends the degree-zero identification to
every degree. The exact forgetful functor and its single and shift comparisons
identify the degree-two comparison with the displayed map. It is therefore
injective. This uses no projective-line decomposition, no Chern class, and no
chosen line comparison. For the empty scheme or the zero coefficient ring all
maps in question are the unique maps, so the conclusion still holds. -/
theorem finiteQuotient_detects_derived_arrows (T : Scheme.{u}) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (M : SheafOfModules.{u + 1}
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))) :
    Function.Injective (fun a :
      (DerivedCategory.singleFunctor _ 0).obj
          ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T))) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧ ↦
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n) ≫
        mapSingleArrow (finiteForget l E T n) (2 : ℤ) a) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
