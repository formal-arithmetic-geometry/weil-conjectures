/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # The section obstruction sequence for principal thickenings

Source: Stacks Project, Tags 0H3D and 0H3E, and the long exact cohomology sequence.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Multiplication by the defining power of a principal thickening on its ambient open. -/
noncomputable def principalThickeningMultiplication
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) (n : ℕ) :
    SheafOfModules.unit W.toScheme.ringCatSheaf ⟶
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  Modules.smulHom _ ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ (n + 1))

/-- The actual image ideal sheaf, rather than a chosen model of the defining ideal. -/
noncomputable abbrev principalThickeningIdeal
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) (n : ℕ) :
    W.toScheme.Modules := image (principalThickeningMultiplication R g W n)

/-- Exactness and naturality of the section obstruction sequence.

Source: Stacks Project, Tags 0H3D and 0H3E (ordinary quotient sheaves), and
Tag 01DZ, Section 20.2 (cohomology as a universal delta-functor).
(blueprint: new-principal-thickening-obstruction)

Proof: Put O = O_W and I_n = image(g^(n+1):O -> O). The kernel of the quotient
R -> R/(g) is (g), and its (n+1)st power is (g^(n+1)). The pullback defining the
thickening is the closed subscheme of W defined by I_n. On affine opens the
quotient sheaf O/I_n is thus the pushforward of its structure sheaf, with quotient
projection equal to restriction. These local identifications agree on overlaps.
The short exact sequence 0 -> I_n -> O -> O/I_n -> 0 gives an additive boundary
map from thickening sections to H^1(W,I_n). Exactness says a boundary-zero section
is the restriction of an ambient section. If kappa commutes with the ideal
inclusions and h commutes with the ambient maps, they give a morphism of these
short exact sequences with middle map the identity. The induced quotient map is
h.appTop. Naturality of the long exact sequence gives the displayed equality.
No cohomology vanishing or torsion bound is needed. For an empty W all groups
are zero. For g=0 the ideal is zero; for a unit g the quotient sheaf is zero. -/
theorem principal_thickening_obstruction
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) :
    ∃ δ : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening
        (Ideal.Quotient.mk (Ideal.span {g})) W n, ⊤) →+
          Modules.H (principalThickeningIdeal R g W n) 1,
      (∀ n t, δ n t = 0 → ∃ a : Γ(W.toScheme, ⊤),
        (FiniteEtale.Adic.openThickeningMap
          (Ideal.Quotient.mk (Ideal.span {g})) W n).appTop a = t) ∧
      (∀ (n m : ℕ)
        (κ : principalThickeningIdeal R g W m ⟶ principalThickeningIdeal R g W n)
        (h : FiniteEtale.Adic.openThickening
            (Ideal.Quotient.mk (Ideal.span {g})) W n ⟶
          FiniteEtale.Adic.openThickening (Ideal.Quotient.mk (Ideal.span {g})) W m),
        κ ≫ image.ι (principalThickeningMultiplication R g W n) =
            image.ι (principalThickeningMultiplication R g W m) →
        h ≫ FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W m =
          FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W n →
        ∀ t, δ n (h.appTop t) = Modules.H.map κ 1 (δ m t)) := by sorry

end AlgebraicGeometry.Scheme
