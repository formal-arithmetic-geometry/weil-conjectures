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

This repair restores the quarantined module and re-applies the completed finite-free
rank-one comparison proof against the current sheaf-dag dependency snapshot.
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
in the concrete uniformizer theorem. Source: coefficient changes paragraph (1). -/
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

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), and the finite free
coefficient argument; Stacks Tags 070G, 070Y and 0D6E.


Exact restriction of coefficients commutes with ordinary direct image. Compute derived
direct image using resolutions acyclic for the underlying ringed-topos direct image;
restriction need not preserve injectives. The universal full right-derived units give
the normalized derived restriction isomorphism, also for an arbitrary full universal
integral derived model R. This constructs s and its full-unit normalization.

After exact restriction to integral coefficients, the scalar mate is the projection
comparison for the two-term resolution just constructed. For each regular free term
this is the unitor, hence invertible. The derived direct images are triangulated, so
the comparison on their cones is invertible as well. This proves the projection
comparison for tensoring any input complex with the quotient resolution, without a
bound on that complex. The scalar-adjunction unit and the full-unit normalization of
s identify this comparison with the restriction of s.mate. Exact restriction of scalar
coefficients reflects isomorphisms, so s.mate is invertible. This is also the finite
free scalar perfect-model argument formalized by integralFiniteScalarPerfectModel;
its comparison must be identified with the normalized square used here.
No properness, projective-line cohomology, quotient flatness, trace, or Tate line
is required. The exponent is n+1, so n=0 is the residue field case, and ramification
changes only the nonzero scalar in the differential.
-/
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
