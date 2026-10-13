/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # Principal thickening sections as degree-zero cohomology of the quotient

Source: Stacks Project, Tags 01IH, 01QP and 01DZ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The cokernel of the principal ideal inclusion has the sections of the thickening,
naturally for maps over the ambient open.

Source: Stacks Project, Tags 01IH and 01QP (quotient structure sheaves), and
Tag 01DZ, Section 20.2 (degree-zero cohomology).
(blueprint: new-principal-thickening-cokernel-sections)

Proof: The kernel of R -> R/(g) is (g), with (n+1)st power (g^(n+1)).
On an affine open Spec B of W, the pullback thickening is Spec B/(g^(n+1)B).
The image of multiplication by the restricted g^(n+1) is the corresponding
ideal sheaf. Thus the cokernel of its image inclusion is canonically the
pushforward of the structure sheaf of the thickening. The identifications are
induced by restriction and agree after localization, so they glue. Taking
global sections and composing with the canonical H^0-to-sections equivalence
gives e. The quotient projection gives the first equation. For the second,
kappa and the identity on O_W give the displayed map of cokernels. The over-W
identity for h says that its structure-sheaf pullback agrees with this map
after precomposition with the quotient projection. That projection is epi
as a sheaf map; hence the maps agree, giving the equation on global sections.
No surjectivity on global sections is claimed. Empty W gives zero groups;
g=0 gives the identity quotient; a unit g gives the zero quotient. -/
theorem principal_thickening_cokernel_sections
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) :
    let p := fun n : ℕ ↦ Modules.smulHom (SheafOfModules.unit W.toScheme.ringCatSheaf)
      ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ (n + 1))
    let i := fun n : ℕ ↦ image.ι (p n)
    ∃ e : ∀ n : ℕ, Modules.H (cokernel (i n)) 0 ≃+
        Γ(FiniteEtale.Adic.openThickening
          (Ideal.Quotient.mk (Ideal.span {g})) W n, ⊤),
      (∀ n (a : Γ(W.toScheme, ⊤)),
        e n (Modules.H.map (cokernel.π (i n)) 0
          ((Modules.H.zeroLinearEquiv _).symm a)) =
        (FiniteEtale.Adic.openThickeningMap
          (Ideal.Quotient.mk (Ideal.span {g})) W n).appTop a) ∧
      (∀ (n m : ℕ) (κ : image (p m) ⟶ image (p n))
        (h : FiniteEtale.Adic.openThickening
            (Ideal.Quotient.mk (Ideal.span {g})) W n ⟶
          FiniteEtale.Adic.openThickening (Ideal.Quotient.mk (Ideal.span {g})) W m)
        (hk : κ ≫ i n = i m),
        h ≫ FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W m =
          FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W n →
        ∀ x, e n (Modules.H.map
          (cokernel.map (i m) (i n) κ (𝟙 _) (by simpa using hk.symm)) 0 x) =
          h.appTop (e m x)) := by sorry

end AlgebraicGeometry.Scheme
