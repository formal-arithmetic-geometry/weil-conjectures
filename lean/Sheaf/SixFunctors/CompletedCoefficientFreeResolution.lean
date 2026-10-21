/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-!+# Free resolutions over completed integral coefficient sheaves

Source: Stacks Project, proetale.tex, Tag 09C3, and algebraization.tex, Tag 099I;
sites-modules.tex, Tags 093J and 093M; sites-cohomology.tex, Tags 06YQ and 06YM
(blueprint: lem-sf-completed-coefficient-free-resolution).

The index `n` denotes the positive exponent `n + 1`. All coefficients and maps are
the published constant quotient sheaves, their inverse limit and their projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace WeilConjectures.CompletedCoefficientFree

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

/-- The free rank-one complex in degree zero over the existing completion.
Source: Stacks Tag 09C3 (blueprint: lem-sf-completed-coefficient-free-resolution). -/
abbrev freeUnitComplex : CochainComplex (scalarReductionSource l E T) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T))

/-- Multiplication by the positive uniformizer power on the degree-zero free complex.
Source: Stacks Tags 093M and 06YM
(blueprint: lem-sf-completed-coefficient-free-resolution). -/
def uniformizerPower (n : ℕ) : freeUnitComplex l E T ⟶ freeUnitComplex l E T :=
  (integralScalarChainAction l E T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app (freeUnitComplex l E T)

/-- The actual two-term free complex `[B --varpi^(n+1)--> B]` in degrees `-1,0`.
Source: Stacks Tags 093M and 06YM
(blueprint: lem-sf-completed-coefficient-free-resolution). -/
def quotientResolution (n : ℕ) : CochainComplex (scalarReductionSource l E T) ℤ :=
  CochainComplex.mappingCone (uniformizerPower l E T n)

/-- The finite coefficient ring as a module over the completion via its projection.
Source: Stacks Tags 093M and 03CZ
(blueprint: lem-sf-completed-coefficient-free-resolution). -/
abbrev residueModule (n : ℕ) : scalarReductionSource l E T :=
  (scalarReductionRestriction l E T n).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E T n))

/-- The actual quotient projection `B -> R_(n+1)`, as the unit-module map taking
`1` to `1`; the action on the target is restricted along the limit projection.
Source: Stacks Tag 093M (blueprint: lem-sf-completed-coefficient-free-resolution). -/
def quotientProjection (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) ⟶
      residueModule l E T n :=
  (residueModule l E T n).unitHomEquiv.symm
    ((SheafOfModules.unit (integralCoefficientSheaf l E T n)).unitHomEquiv (𝟙 _))

/-- A finite free cell, with rank zero allowed, in an arbitrary integer degree.
Finite products here are the canonical finite direct sums in the abelian module category.
Source: Stacks Tag 09C3 (blueprint: lem-sf-completed-coefficient-free-resolution). -/
def freeCell (r : ℕ) (d : ℤ) : CochainComplex (scalarReductionSource l E T) ℤ :=
  (CochainComplex.singleFunctor _ d).obj
    (∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T))

/-- The canonical reduction of every unbounded derived object. The normalized derived
adjunction fixes this unit on K-flat representatives by `x -> 1 tensor x`; thus the
choice of witness does not introduce an arbitrary arrow.
Source: Stacks Tag 06YY (blueprint: lem-sf-completed-coefficient-free-resolution). -/
def reductionMap (n : ℕ) (M : DerivedCategory (scalarReductionSource l E T)) :
    M ⟶ (scalarReductionDerivedRestriction l E T n).obj
      ((scalarReductionDerivedExtension l E T n).obj M) :=
  (derivedScalarExtensionRestrictionAdjunction l E T n).choose.unit.app M

/-- The free quotient resolution is K-flat and its canonical augmentation is a
quasi-isomorphism; every finite free cell is complete through the actual quotient
projections; and canonical reduction of every unbounded derived object is the cone
of its uniformizer power.

Source: Stacks Project, proetale.tex Tag 09C3, algebraization.tex Tag 099I,
sites-modules.tex Tags 093J/093M, sites-cohomology.tex Tags 06YQ/06YM;
Bhatt--Scholze, Propositions 3.1.9--3.1.10
(blueprint: lem-sf-completed-coefficient-free-resolution).

Proof plan:
1. The extension-integers DVR theorem makes the uniformizer regular and the ring
   Noetherian. Constant module section exactness (093J) gives the regular-element
   short exact sequence and the surjective quotient transitions.
2. Completed constant sheaf reduction (093M) is flat and identifies its reduction
   by the actual limit projection. Tensoring the sequence yields
   `0 -> B -> B -> R_(n+1) -> 0`. The cone augmentation is therefore a quasi-isomorphism;
   its restriction along the degree-zero inclusion is exactly quotientProjection.
3. The resolution is bounded above with free terms, hence K-flat by
   lem-pc-bounded-above-flat-kflat-site. The same holds for each free cell.
4. K-flat computation identifies the free cell's reductions with finite sums of the
   quotient sheaves. The surjective-tower derived-limit theorem gives their Roos
   triangle with the actual coordinate projections. Finite coordinates commute with
   inverse limit, yielding B^r. Shift this triangle for an arbitrary cell degree;
   shifts preserve products as equivalences. Rank zero is included.
5. Resolve an arbitrary, possibly unbounded M by a flat-term K-flat complex Q
   (06YS). Derived change of rings computes reduction by Q tensor R_(n+1).
   K-flat tensor preserves quasi-isomorphisms (06YP), so tensoring the augmented
   two-term resolution identifies it with that reduction. Its inclusion sends
   x to x tensor 1, precisely the normalized derived-adjunction unit reductionMap.
6. The inclusion-compatible tensor/mapping-cone isomorphism identifies the tensor
   resolution with Cone(varpi^(n+1):Q -> Q). Its distinguished cone triangle gives
   the displayed triangle, with the actual reductionMap as the middle arrow.
   No step requires Q or M to be bounded. -/
theorem completed_coefficient_free_resolution :
    (∀ n : ℕ,
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E T)
        (quotientResolution l E T n) ∧
      ∃ ε : quotientResolution l E T n ⟶
          (CochainComplex.singleFunctor _ 0).obj (residueModule l E T n),
        QuasiIso ε ∧
          CochainComplex.mappingCone.inr (uniformizerPower l E T n) ≫ ε =
            (CochainComplex.singleFunctor _ 0).map (quotientProjection l E T n)) ∧
    (∀ (r : ℕ) (d : ℤ), IntegralOnSlice.IsComplete l E T none
      (DerivedCategory.Q.obj (freeCell l E T r d))) ∧
    ∀ (n : ℕ) (M : DerivedCategory (scalarReductionSource l E T)),
      ∃ δ : (scalarReductionDerivedRestriction l E T n).obj
          ((scalarReductionDerivedExtension l E T n).obj M) ⟶ M⟦(1 : ℤ)⟧,
        Triangle.mk
          ((integralScalarDerivedAction l E T
            (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app M)
          (reductionMap l E T n M) δ ∈ distTriang _ := by
  sorry

end WeilConjectures.CompletedCoefficientFree
