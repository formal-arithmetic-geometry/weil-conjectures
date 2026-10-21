/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.NagataRing
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Sheaf.AlgebraicGeometry.NowhereDenseDimZero
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.AlgebraicGeometry.NormalizationInseparableBaseChange
import Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve

/-!
# Generic curve preparation over an excellent base

Source: de Jong, Families of curves and alterations (1997), proof of Theorem 2.4,
Sections 2.7--2.10; Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX,
Section 1.3, printed page 132 (blueprint: lem-trf-excellent-base-generic-curve-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Orgogozo

namespace AlgebraicGeometry

/-- After alterations of source and base, the generic curve is smooth and geometrically
integral, and the reduced inverse image of the boundary has finite étale generic fibre.
Source: de Jong, Families of curves and alterations (1997), Theorem 2.4 proof,
Sections 2.7--2.10, especially Lemma 2.8; Illusie--Laszlo--Orgogozo, Travaux de Gabber,
Exposé IX, Section 1.3, printed page 132
(blueprint: lem-trf-excellent-base-generic-curve-preparation).

`Z` is a closed subset, and `Z ≠ ⊤` says it is proper. The vanishing ideal sheaf of
`Z.preimage a.continuous` gives exactly its reduced induced inverse image in `C₀`.
`IsAlteration` includes a component-dominance clause, which is automatic here because
both source and target are integral and the map is surjective. No separation or
projectivity hypothesis is imposed on the base. Noetherian means locally Noetherian
and quasi-compact. The boundary and its generic fibre may be empty.

Proof, following the sixteen steps of the DAG node:
1. The generic fibre X over k = κ(B) is proper of finite type. Dominance embeds affine
   coordinate rings into κ(C), so its generic-localized charts are nonzero domains with
   their common generic point; hence X is integral. Its dimension is one by hypothesis,
   and the boundary misses its generic point. Use reduced induced closed structures.
2. Apply lem-weil-pbc-normalization-geonormal-insep to X. A finite purely inseparable
   extension k₁/k makes the normalization N₁ of (X_k₁)_red geometrically normal. Purely
   inseparable base change preserves the underlying space and dimension; normalization
   preserves integrality and dimension one. By lem-weil-pbc-geonormal-dim-one-smooth,
   N₁ is smooth.
3. The reduced inverse boundary D₁ misses the generic point, so has dimension at most zero
   by lem-pc-nowhere-dense-dim-zero, and is finite by
   lem-pc-zero-dimensional-closed-subscheme-finite. Its algebra is Noetherian with finitely
   many minimal primes. Apply lem-pur-finite-inseparable-geometric-reduction to obtain a
   finite purely inseparable K/k₁ with D = (D₁_K)_red geometrically reduced and finite.
4. Its finite-dimensional algebra H has every nonzerodivisor invertible, so Q(H) = H.
   By lem-weil-pbc-reduced-noetherian-total-ring-fractions it is a finite product of finite
   field extensions. Each factor is geometrically reduced, hence separable: an inseparable
   minimal polynomial would produce a nonzero nilpotent after algebraic closure. Thus D
   is finite étale by lem-sc-finite-etale-algebra-criterion, including H = 0.
5. By lem-trf-normalization-inseparable-base-change the normalization N of (X_K)_red is
   N₁_K, and its reduced inverse boundary is D. It stays geometrically normal and of
   dimension one, hence smooth. The composite extension K/k is finite purely inseparable.
6. Normalize B in K. Excellence implies Nagata, so the integral closures of its affine
   coordinate rings in K are finite. They glue by integral-closure localization to an
   integral finite dominant B₁ over B with generic fibre Spec K.
7. These finite chart algebras are excellent by lem-exc-finite-type-localization-excellent;
   lem-trf-excellent-scheme-affine-cover gives excellence of B₁. Finiteness gives
   Noetherianity and properness; dominance and closed image give surjectivity, so B₁ → B
   is an alteration without any global affine or separated hypothesis.
8. In C ×_B B₁, the fibre above the generic point of C has one point z by pure
   inseparability. It has no proper generization; sobriety makes its closure an
   irreducible component. Its reduced induced subscheme W dominates C and B₁.
9. The map W → C is finite by finite base change and closed immersion. Thus W is
   Noetherian and excellent by finite-type stability on affine charts. The map W → B₁
   is proper by base change of f and closed immersion.
10. Normalize W in its function field. Nagata makes C₁ → W finite; integral-closure
    localization gives integrality and dominance. Finite chart algebras give excellence
    and Noetherianity. The composites a₁ : C₁ → C and f₁ : C₁ → B₁ are respectively
    a finite alteration and a proper dominant map, and a₁ ≫ f = f₁ ≫ b₁.
11. The generic fibre of W is (X_K)_red: it has the whole irreducible underlying fibre
    and is reduced by generic localization of domains. Integral closure commutes with
    this localization, identifying the generic fibre of C₁ with N over X_K.
12. The reduced inverse boundary Z₁ misses the generic point of C₁, so is nowhere dense.
    Reduction commutes with generic localization: a nilpotent fraction r/t has some u
    killing r^m, and equals (ur)/(ut) with ur nilpotent. Uniqueness of reduced induced
    closed structures identifies the generic boundary with D, which is finite étale.
13. Apply lem-trf-stein-smooth-generic-curve to f₁. Obtain integral excellent Noetherian
    B₀ finite dominant over B₁, with proper dominant f₀ : C₁ → B₀ and smooth
    geometrically integral generic curve of dimension one. Its function field L is the
    finite separable constant field H⁰(N, O_N) over K.
14. The generic fibre of B₀ → B₁ is Spec L, since localizing its finite affine domain
    algebras gives the field L. Fibre-product associativity identifies the generic curve
    over B₀ with N and the generic boundary with the same D carrying its L-structure.
15. Each field factor of H inherits L → E_j, is finite over L, and is separable over L:
    its minimal polynomial over L divides the separable minimal polynomial over K.
    The finite-étale product criterion applies, including the empty product.
16. Set C₀ = C₁, a = a₁ and b = b₁q₀. The square commutes. Both a and b are finite
    proper dominant surjections and therefore alterations. Steps 7, 10 and 13 give the
    scheme properties; Steps 12, 13 and 15 give all generic-curve and boundary clauses.
-/
theorem exists_excellentBaseGenericCurvePreparation
    {C B : Scheme.{u}} [IsIntegral C] [IsIntegral B]
    [IsLocallyNoetherian C] [CompactSpace C] [IsLocallyNoetherian B] [CompactSpace B]
    (hC : IsExcellentScheme C) (hB : IsExcellentScheme B)
    (f : C ⟶ B) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint B)) = 1)
    (Z : Closeds C) (hZ : Z ≠ ⊤) :
    ∃ (C₀ B₀ : Scheme.{u}) (a : C₀ ⟶ C) (b : B₀ ⟶ B) (f₀ : C₀ ⟶ B₀),
      IsIntegral C₀ ∧ IsExcellentScheme C₀ ∧ IsLocallyNoetherian C₀ ∧ CompactSpace C₀ ∧
      IsIntegral B₀ ∧ IsExcellentScheme B₀ ∧ IsLocallyNoetherian B₀ ∧ CompactSpace B₀ ∧
      IsAlteration a ∧ IsAlteration b ∧ IsProper f₀ ∧ IsDominant f₀ ∧
      a ≫ f = f₀ ≫ b ∧
      ∃ η₀ : B₀, IsGenericPoint η₀ Set.univ ∧
        Smooth (f₀.fiberToSpecResidueField η₀) ∧
        GeometricallyIntegral (f₀.fiberToSpecResidueField η₀) ∧
        topologicalKrullDim (f₀.fiber η₀) = 1 ∧
        IsNowhereDense (a ⁻¹' (Z : Set C)) ∧
        IsFinite (((Scheme.IdealSheafData.vanishingIdeal (Z.preimage a.continuous)).subschemeι ≫
          f₀).fiberToSpecResidueField η₀) ∧
        Etale (((Scheme.IdealSheafData.vanishingIdeal (Z.preimage a.continuous)).subschemeι ≫
          f₀).fiberToSpecResidueField η₀) := by
  sorry

end AlgebraicGeometry
