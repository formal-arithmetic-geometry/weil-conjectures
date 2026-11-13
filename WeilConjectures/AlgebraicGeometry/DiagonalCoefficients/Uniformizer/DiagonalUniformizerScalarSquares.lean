/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarSquareTypes
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerMateComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerPointResolution

/-! # Perfect uniformizer reduction and direct image

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a v w wc
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory RestrictionSquare.mate Functor.leftDerivedFunctor quotientMap
  canonicalDiagonalRightDerived Profinite.continuousMapRingSheaf
  derivedScalars upperStarFromPoint CondensedRing.lowerStar

/-- A scalar/direct-image square with invertible mate on every complex.
Keeping the coefficient rings as parameters shares the derived-category instances
in the concrete uniformizer theorem. -/
structure ScalarSquareIsomorphisms
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived Λ f) where
  square : CanonicalScalarSquare a f R
  isIso : ScalarMateIsIso a square

private theorem rankOneScalarSquares
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (h : ∃ P : ShortComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ),
      P.ShortExact ∧ Nonempty (P.X₁ ≅ Mod.regular Λ) ∧
        Nonempty (P.X₂ ≅ Mod.regular Λ) ∧
        Nonempty (P.X₃ ≅ (Mod.comap a).obj (Mod.regular Λ')))
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived Λ f) :
    Nonempty (ScalarSquareIsomorphisms a f R) ∧
      ∀ s : CanonicalScalarSquare a f R, ScalarMateIsIso a s := by
  have hh := rankOnePointResolution_scalarSquares (Λ := Λ) (Λ' := Λ') a h f R
  let sq := hh.1.some
  exact ⟨⟨{ square := sq, isIso := hh.2 sq }⟩, hh.2⟩

set_option linter.unusedVariables false in
/-- Uniformizer reduction has a normalized restriction/direct-image square whose
scalar mate is invertible on every complex.

Source: Stacks Tags 070G, 070Y and 0D6E. -/
theorem diagonal_uniformizer_scalar_squares
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived (Profinite.padicIntegersRingObj.{u} l E.1) f) :
    Nonempty (ScalarSquareIsomorphisms (quotientMap l E π n) f R) :=
  (rankOneScalarSquares
    (Λ := Profinite.padicIntegersRingObj.{u} l E.1)
    (Λ' := Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    (quotientMap l E π n) (diagonalUniformizer_pointResolution.{u} l E π hπ n)
    (X := X) (S := S) f R).1

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
