/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Spec

/-!
# Sections of an affine finite fibre

Source: Stacks Project, Morphisms, affine calculation associated with Tag 02KB
(blueprint: lem-pc-finite-affine-fibre-sections).
-/

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

noncomputable section

set_option quotPrecheck false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (p : Spec (CommRingCat.of A))

local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap A B))
local notation "R" => (Spec (CommRingCat.of A)).presheaf.stalk p
local notation "P" => (Spec.topMap (CommRingCat.ofHom (algebraMap A B)) _*
  (Spec.structureSheaf (CommRingCat.of B)).1).stalk p
local notation "K" => (Spec (CommRingCat.of A)).residueField p

local instance : Algebra R P :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
    (Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap A B))).hom.c).hom.toAlgebra

local instance : Algebra R K := ((Spec (CommRingCat.of A)).residue p).hom.toAlgebra

local instance : Algebra A K :=
  ((StructureSheaf.toStalk (CommRingCat.of A) p) ≫
    (Spec (CommRingCat.of A)).residue p).hom.toAlgebra

/-- For a finite algebra `B` over `A`, the stalk of the direct image of the structure sheaf,
after tensoring with the residue field at `p`, has the same sections as the scheme-theoretic
fibre. Both identifications agree on elements of `B` and of the residue field. The stalk
calculation uses the localization description of a pushed-forward affine structure sheaf;
tensoring with the residue field gives `B ⊗[A] κ(p)`. The affine pullback formula identifies
the fibre with `Spec (B ⊗[A] κ(p))`, so its global sections are that tensor product.
Source: Stacks Project, Morphisms, Tag 02KB, affine calculation in the proof of the lemma
(lemma-finite-flat) (blueprint: lem-pc-finite-affine-fibre-sections)

Proof steps from the source: (1) identify the structure sheaf on `Spec B` with `˜B`,
push it forward along `Spec.map (algebraMap A B)`, and identify its stalk at `p` with
the localization of `B` at the prime of `p`; (2) use `κ(p) = A_p / m_p A_p` to
identify the stalk tensor with `B ⊗[A] κ(p)`; (3) apply the affine fibre-product
calculation to identify the fibre with `Spec (B ⊗[A] κ(p))` and its global sections
with that tensor product. The displayed equations record these identifications on the
generators from `B` and `κ(p)` (using `lem-weil-pbc-spec-tilde-free-module`,
`lem-weil-pbc-pushforward-tilde-spec`, `lem-weil-pbc-spec-tilde-stalk-localization`,
and `lem-weil-pbc-fibre-product-affine-spectra`). Finiteness of `B` over `A` is not used;
it is kept for the citer `lem-pc-flf-properties`. -/
theorem finite_affine_fibre_sections [Module.Finite A B] :
    ∃ (e : (P ⊗[R] K) ≃+* Γ((f).fiber p, ⊤))
      (g : (B ⊗[A] K) ≃+* Γ((f).fiber p, ⊤)),
      (∀ b : B,
        e ((StructureSheaf.toPushforwardStalk
          (CommRingCat.ofHom (algebraMap A B)) p).hom b ⊗ₜ[R] (1 : K)) =
          g (b ⊗ₜ[A] (1 : K))) ∧
      (∀ k : K, e ((1 : P) ⊗ₜ[R] k) = g ((1 : B) ⊗ₜ[A] k)) ∧
      (∀ b : B,
        g (b ⊗ₜ[A] (1 : K)) =
          ((f).fiberι p).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) ∧
      (∀ k : K,
        g ((1 : B) ⊗ₜ[A] k) =
          ((f).fiberToSpecResidueField p).appTop.hom ((Scheme.ΓSpecIso K).inv.hom k)) := by
  sorry

end

end AlgebraicGeometry
