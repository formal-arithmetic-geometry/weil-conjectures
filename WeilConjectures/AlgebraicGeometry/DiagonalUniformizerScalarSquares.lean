/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.CanonicalDiagonalRightDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalScalarSquareTypes
import WeilConjectures.AlgebraicGeometry.DiagonalUniformizerMateComparison
import WeilConjectures.AlgebraicGeometry.DiagonalUniformizerPointResolution

/-! # Perfect uniformizer reduction and direct image


This repair restores the quarantined module and re-applies the completed finite-free
rank-one comparison proof against the current sheaf-dag dependency snapshot.

Source: diagonal tower coefficient changes, paragraph (1), cofinal uniformizer quotients.
(blueprint: lem-diagonal-uniformizer-scalar-squares).
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
in the concrete uniformizer theorem. Source: coefficient changes paragraph (1).
(blueprint: lem-diagonal-uniformizer-scalar-squares). -/
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

private theorem rankOneMateIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (h : ∃ P : ShortComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ),
      P.ShortExact ∧ Nonempty (P.X₁ ≅ Mod.regular Λ) ∧
        Nonempty (P.X₂ ≅ Mod.regular Λ) ∧
        Nonempty (P.X₃ ≅ (Mod.comap a).obj (Mod.regular Λ')))
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived Λ f)
    (s : CanonicalScalarSquare a f R) :
    ScalarMateIsIso a s :=
  (rankOnePointResolution_scalarSquares (Λ := Λ) (Λ' := Λ') a h f R).2 s

-- The uniformizer hypothesis stays in the public interface; square existence is general.
set_option linter.unusedVariables false in
/-- The quotient reduction admits a full-unit-normalized restriction/direct-image
square with the canonical quotient right-derived model.

Proof: the normalized scalar pullback data give a restriction/direct-image
isomorphism between the canonical models satisfying the full cochain-unit
equation; transport the integral model to R by the universal property of the
right-derived functor. No resolution is needed for existence. This is the
square-existence part of the uniformizer scalar-square argument.
(blueprint: lem-diagonal-uniformizer-scalar-squares). -/
theorem diagonal_uniformizer_restriction_square
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived (Profinite.padicIntegersRingObj.{u} l E.1) f) :
    Nonempty (CanonicalScalarSquare (quotientMap l E π n) f R) :=
  normalizedRestrictionSquare_exists
    (Λ := Profinite.padicIntegersRingObj.{u} l E.1)
    (Λ' := Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    (quotientMap l E π n) (X := X) (S := S) f R

/-- The scalar mate of a normalized uniformizer-quotient square is invertible
on every integral derived object.

Proof: identify the mate after exact restriction with the projection comparison
for the two-term finite-free quotient resolution. It is invertible on each free
term, hence on the cone by the triangulated comparison theorem. Exact restriction
reflects isomorphisms, so the original mate is invertible for every unbounded
complex. This is the mate-invertibility part of the uniformizer scalar-square
argument and assumes the normalized square as input.
(blueprint: lem-diagonal-uniformizer-scalar-squares). -/
theorem diagonal_uniformizer_restriction_mate_isIso
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : ScalarRightDerived (Profinite.padicIntegersRingObj.{u} l E.1) f)
    (square : CanonicalScalarSquare (quotientMap l E π n) f R) :
    ScalarMateIsIso (quotientMap l E π n) square :=
  rankOneMateIso
    (Λ := Profinite.padicIntegersRingObj.{u} l E.1)
    (Λ' := Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    (quotientMap l E π n) (diagonalUniformizer_pointResolution.{u} l E π hπ n)
    (X := X) (S := S) f R square

/-- Uniformizer reduction has a normalized restriction/direct-image square whose
scalar mate is invertible on every complex.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), and the finite free
coefficient argument; Stacks Tags 070G, 070Y and 0D6E.
(blueprint: lem-diagonal-uniformizer-scalar-squares).

Proof: The quotient O_E/(pi^(n+1)) has the two-term free O_E-resolution with differential
pi^(n+1). The integer ring is a domain and the specified uniformizer is nonzero, so this
map is injective. Continuous functions on a profinite set preserve this short exact
sequence: finite residue classes have locally constant lifts on a finite clopen
partition, and the inverse of multiplication by pi^(n+1) on its image is continuous.
Pull back from the profinite point to either scheme by the exact monoidal inverse
image. This gives the same two-term free resolution of the pulled-back quotient ring.

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
