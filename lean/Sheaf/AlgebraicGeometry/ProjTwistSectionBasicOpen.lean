/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Homogeneous twist sections and standard opens on the invertibility locus

Source: Stacks Project, Constructions, Tags 01MU, 01MV and 01MW (5)--(7)
(blueprint: lem-trf-proj-twist-section-basic-open).

## Main definitions

* `AlgebraicGeometry.Proj.twistSectionOnOpen`: the canonical homogeneous section restricted
  to an open subscheme, using the existing twist and restriction functor.
* `AlgebraicGeometry.Proj.twistSectionLoci`: its nonvanishing sets in positive degrees
  divisible by the specified integer.

## Main statements

* `AlgebraicGeometry.Proj.twistSectionBasicOpen`: equality of the section locus with the
  standard open, and the basis and affine basis assertions on every open in `W_d`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The section `f/1` of the twist restricted to an open `U`. It is the restriction of
`unitToTwist hf`, evaluated on the unit section, with the canonical restriction-of-unit
isomorphism. Source: Stacks, Constructions, 01MN (3) and 01MV
(blueprint: lem-trf-proj-twist-section-basic-open). -/
def twistSectionOnOpen (U : (Proj 𝒜).Opens) {q : ℕ} {f : A} (hf : f ∈ 𝒜 q) :
    Γ((twist 𝒜 (0 + (q : ℤ))).restrict U.ι, ⊤) :=
  Scheme.Modules.Hom.app
    ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (unitToTwist hf)) ⊤ (1 : Γ(U.toScheme, ⊤))

/-- The actual stalk nonvanishing loci of the restricted canonical homogeneous sections
in degrees `nd` for `n > 0`. Positive powers are included since their degrees are still
positive multiples of `d`. Source: Stacks, Constructions, 01MV and 01MW (5)--(7)
(blueprint: lem-trf-proj-twist-section-basic-open). -/
def twistSectionLoci (d : ℕ) (U : (Proj 𝒜).Opens) : Set (Set U.toScheme) :=
  {V | ∃ (n : ℕ), 0 < n ∧ ∃ (f : A) (hf : f ∈ 𝒜 (n * d)),
    V = Scheme.Modules.nonvanishingLocus
      ((twist 𝒜 (0 + ((n * d : ℕ) : ℤ))).restrict U.ι) (twistSectionOnOpen 𝒜 U hf)}

/-- Homogeneous sections cut out standard opens on every open of `W_d`, and these
nonvanishing loci, as well as their affine members, form a basis.
Here `hW` writes `W_d` by its equivalent union characterization, including degree-zero `b`.
Source: Stacks, Constructions, 01MU, 01MV and 01MW (5)--(7)
(blueprint: lem-trf-proj-twist-section-basic-open).

Proof: cover `W_d` by `D_+(ab)` with degrees `alpha = beta + d`. On such a chart `a,b`
are units after localizing at `ab`, and `(a/b)^n` freely generates the degree-`nd` part
of the localization. These fraction formulas commute with restrictions, giving a local
frame for the existing twisting sheaf. In this frame `f/1 = (b^n*f/a^n)*(a/b)^n`.
The stalk nonvanishing predicate is therefore exactly the unit locus of `c = b^n*f/a^n`.
Put `k = alpha + beta`; it is positive. The fraction identity
`c^k = (b^(2*n*alpha)/a^(2*n*beta)) * f^k/(ab)^(n*d)` has a degree-zero unit as its first
factor. Thus `c` is a unit exactly on the standard-open intersection given by
`lem-weil-pbc-proj-basic-open-intersection`. Glue over the covering charts to obtain the
first clause. For each point and open neighbourhood in `U`, the positive-degree basis of
`lem-weil-pbc-proj-standard-open-inclusion` gives `D_+(g)` contained in that neighbourhood.
Replace `g` by `g^d`: primality and `d > 0` preserve the standard open, and the new degree
is a positive multiple of `d`. The first clause gives a member of `twistSectionLoci`.
This proves the basis assertion. The chosen standard open is affine by `def-pc-proj`,
so the affine members also form a basis. Empty opens and zero or nilpotent `f` give the
empty locus and require no exceptional hypothesis. -/
theorem twistSectionBasicOpen (d : ℕ) (_hd : 0 < d) (W : (Proj 𝒜).Opens)
    (_hW : W = ⨆ (α : ℕ) (β : ℕ) (a : 𝒜 α) (b : 𝒜 β) (_ : α = β + d),
      basicOpen 𝒜 ((a : A) * (b : A)))
    (U : (Proj 𝒜).Opens) (_hU : U ≤ W) :
    (∀ (n : ℕ), 0 < n → ∀ (f : A) (hf : f ∈ 𝒜 (n * d)),
      Scheme.Modules.nonvanishingLocus
          ((twist 𝒜 (0 + ((n * d : ℕ) : ℤ))).restrict U.ι)
          (twistSectionOnOpen 𝒜 U hf) =
        ((U.ι ⁻¹ᵁ basicOpen 𝒜 f : U.toScheme.Opens) : Set U.toScheme)) ∧
    TopologicalSpace.IsTopologicalBasis (twistSectionLoci 𝒜 d U) ∧
    TopologicalSpace.IsTopologicalBasis
      {V : Set U.toScheme | V ∈ twistSectionLoci 𝒜 d U ∧
        ∃ O : U.toScheme.Opens, (O : Set U.toScheme) = V ∧ IsAffineOpen O} := by
  sorry

end AlgebraicGeometry.Proj
