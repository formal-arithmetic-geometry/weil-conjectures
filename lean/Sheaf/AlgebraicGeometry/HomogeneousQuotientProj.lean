/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Proj of a homogeneous quotient

Source: Stacks Project, Algebra, Tag 00JL, section-graded; Constructions, Tag 01MY,
lemma-morphism-proj (blueprint: def-sfb-homogeneous-quotient-proj).

The quotient components are actual images. Their decomposition is uniquely determined
as the inverse of the canonical summation map; no arbitrary algebra or scheme is chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

variable {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The image of the homogeneous component in the actual quotient algebra.
Source: Stacks Project, Tag 00JL (blueprint: def-sfb-homogeneous-quotient-proj). -/
def homogeneousQuotientPiece (I : HomogeneousIdeal 𝒜) (d : ℕ) :
    Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 d).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

/-- The displayed images admit a unique graded-algebra decomposition.
Source: Stacks Project, Tag 00JL (blueprint: def-sfb-homogeneous-quotient-proj).

Proof: descend each homogeneous projection of A to A/I. This is well defined because
I is homogeneous. Every element has finitely many nonzero projections and is their
sum. On a homogeneous image element the projections are zero in all other degrees
and the identity in its own degree. Thus they invert the canonical summation map.
Products and the unit descend from those of A. The inverse of the fixed summation
map is unique, and the remaining structure fields are propositions. This includes
the zero quotient and needs no finite generation assumption. -/
theorem existsUnique_homogeneousQuotientGrading (I : HomogeneousIdeal 𝒜) :
    ∃! g : GradedAlgebra (homogeneousQuotientPiece 𝒜 I), True := by
  sorry

/-- The uniquely determined quotient grading on the explicit image submodules.
Source: Stacks Project, Tag 00JL (blueprint: def-sfb-homogeneous-quotient-proj). -/
noncomputable instance homogeneousQuotientGrading (I : HomogeneousIdeal 𝒜) :
    GradedAlgebra (homogeneousQuotientPiece 𝒜 I) :=
  (existsUnique_homogeneousQuotientGrading 𝒜 I).choose

/-- The actual quotient homomorphism, preserving homogeneous degrees.
Source: Stacks Project, Tag 00JL (blueprint: def-sfb-homogeneous-quotient-proj). -/
def homogeneousQuotientMap (I : HomogeneousIdeal 𝒜) :
    𝒜 →+*ᵍ homogeneousQuotientPiece 𝒜 I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem := fun {_d} {_a} ha ↦ ⟨_, ha, rfl⟩

/-- The quotient-induced morphism Proj(A/I) → Proj(A), with its canonical map on
homogeneous fractions. It is a closed immersion by surjective Proj functoriality.
Source: Stacks Project, Tag 01MY (blueprint: def-sfb-homogeneous-quotient-proj). -/
noncomputable def homogeneousQuotientProjι (I : HomogeneousIdeal 𝒜) :
    Proj (homogeneousQuotientPiece 𝒜 I) ⟶ Proj 𝒜 :=
  Proj.map (homogeneousQuotientMap 𝒜 I)
    (GradedRingHom.irrelevant_le_map_of_surjective (Ideal.Quotient.mk_surjective))

end AlgebraicGeometry
