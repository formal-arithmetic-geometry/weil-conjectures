/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre

/-!
# An equivariant homogeneous projective envelope

Source: Stacks Project, Tags 01WD, 03GL, 01R8 and 01RG; the equivariant construction
underlying Rydh, Proposition 4.7 (blueprint: lem-per-equivariant-projective-envelope).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite group action on a finite-type scheme admitting an immersion into finite
projective space over an affine Noetherian base extends to a homogeneous projective envelope.
The quotient is the actual polynomial quotient, and its homogeneous pieces are exactly
the images of homogeneous polynomials. The maps `φ h` are the graded ring maps underlying
`ρ (h⁻¹)`, so `Proj.map (φ h)` is the induced left action, not an independently chosen action.
The degree-zero map is specified by its underlying map into the quotient algebra.
Empty schemes, the zero ring, nonfaithful actions and wild characteristics are allowed.

Source: Stacks Project, Tags 01WD, 03GL, 01R8 and 01RG; homogeneous construction underlying
Rydh, Proposition 4.7 (blueprint: lem-per-equivariant-projective-envelope).

Proof:
1. The affine base is Noetherian (`lem-sc-affine-noetherian-underlying-space`,
   `pqf-def-locnoeth`), hence so is V (`lem-weil-pbc-finite-type-over-noetherian`).
   Every open of V is quasi-compact (`lem-weil-pbc-noetherian-open-subscheme-noetherian`),
   so the immersion used below is quasi-compact.
2. Take the product over H of the translates j composed with the inverse action.
   Separate the identity factor: the graph into the product of the other factors is closed
   since that product is separated. Segre makes it projective (`lem-chow-segre`,
   `def-kun-projective`, `lem-kun-projective-implies-proper`, `def-weil-proper-morphism`).
   Base change and composition of closed immersions then show the product map is an
   immersion (`lem-weil-pbc-closed-immersion-base-change`,
   `lem-weil-pbc-closed-immersion-comp`, `def-weil-open-immersion`).
3. H permutes the factors. The iterated Segre map (`lem-chow-segre`, `def-chow-segre`)
   is equivariant for the induced permutation of monomial coordinates. Its composition
   with the product immersion is an immersion into a finite projective space.
4. Take its scheme-theoretic closure (`lem-chow-closed-model`). On affine opens its ideal
   is the restriction-map kernel (`lem-weil-pbc-scheme-image-qc-kernel`). Equivariance
   identifies these kernels under the ambient coordinate permutations, preserving the
   whole ideal sheaf, including nilpotents. Thus the action restricts to the closure.
5. Use `lem-per-projective-closed-subscheme-homogeneous-ideal`: the homogeneous ideal I
   consists of the forms whose chart functions vanish on that closed subscheme, and
   Proj of the actual polynomial quotient is that subscheme.
6. The coordinate substitution associated to the inverse geometric action preserves I:
   pullback carries each vanishing homogeneous chart function to another such function.
   Apply the inverse group element for equality. These substitutions obey the group law.
7. Descend these graded R-algebra automorphisms to the quotient. The left action on Proj
   uses the inverse automorphism (`prop-nagata-relative-proj-functoriality`). On standard
   charts this is the same fraction substitution as the ambient action, so the open
   immersion is equivariant (`def-pc-proj`).
8. The degree-zero quotient is R/I₀, proving surjectivity. The closed immersion makes
   the envelope projective (`def-kun-projective`). If V is empty take I to be the unit
   ideal and the quotient to be zero. No step uses faithfulness or division by |H|. -/
theorem exists_equivariant_projective_envelope
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (V : Scheme.{u}) (f : V ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hV : ∃ (n : ℕ) (i : V ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R))),
      IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R) = f)
    (H : Type v) [Group H] [Finite H] (a : H →* Aut V)
    (ha : ∀ h : H, (a h).hom ≫ f = f) :
    ∃ (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) R))
      (𝒜 : ℕ → AddSubgroup (MvPolynomial (Fin (N + 1)) R ⧸ I))
      (_ : GradedRing 𝒜) (r₀ : R →+* 𝒜 0)
      (ρ : H →* ((MvPolynomial (Fin (N + 1)) R ⧸ I) ≃ₐ[R]
        (MvPolynomial (Fin (N + 1)) R ⧸ I)))
      (φ : H → (𝒜 →+*ᵍ 𝒜))
      (hφ : ∀ h : H, HomogeneousIdeal.irrelevant 𝒜 ≤
        (HomogeneousIdeal.irrelevant 𝒜).map (φ h))
      (j : V ⟶ Proj 𝒜)
      (k : Proj 𝒜 ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of R))),
      (∀ (p : MvPolynomial (Fin (N + 1)) R) (d : ℕ),
        p ∈ I → MvPolynomial.homogeneousComponent d p ∈ I) ∧
      (∀ (d : ℕ) (x : MvPolynomial (Fin (N + 1)) R ⧸ I),
        x ∈ 𝒜 d ↔ ∃ p : MvPolynomial (Fin (N + 1)) R,
          p.IsHomogeneous d ∧ Ideal.Quotient.mk I p = x) ∧
      (∀ r : R, (r₀ r : MvPolynomial (Fin (N + 1)) R ⧸ I) =
        algebraMap R (MvPolynomial (Fin (N + 1)) R ⧸ I) r) ∧
      Function.Surjective r₀ ∧
      (∀ (h : H) (x : MvPolynomial (Fin (N + 1)) R ⧸ I), φ h x = ρ (h⁻¹) x) ∧
      IsOpenImmersion j ∧ IsClosedImmersion k ∧
      k ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of R)) ↘ Spec (.of R) =
        Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom r₀) ∧
      j ≫ Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom r₀) = f ∧
      ∀ h : H, (a h).hom ≫ j = j ≫ Proj.map (φ h) (hφ h) := by
  sorry

end AlgebraicGeometry
