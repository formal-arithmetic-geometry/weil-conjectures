/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
import Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability

/-! # Cohomological boundedness of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- The canonical Brown right adjoint has finite cohomological amplitude on bounded
constructible inputs.  This is the geometric restriction step of the blueprint proof.

Source: blueprint `det-existence-restriction.proof.md`, Part (2), rational and integral
restriction theorems and their coefficient comparison.
Proof: identify the canonical Brown right adjoint with the geometric exceptional inverse
image on finite affine charts, apply the rational and integral restriction theorems, and
take a common bound over the finite affine cover.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded-canonical)
-/
theorem ellAdic_localizing_canonical_rightAdjoint_obj_isBounded
    (hF : (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((@Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF).obj
          ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  sorry

/-- The supplied localizing right adjoint has finite cohomological amplitude on a bounded
constructible input.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, Part (2).
Proof: use the finite affine factorization of the proper map and the boundedness part of
the rational restriction theorem, or its compatible integral torsion-level analogue.  A
finite affine cover gives a common pair of cohomological bounds; uniqueness of right
adjoints transports these bounds from the geometric construction to the supplied `G`.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/
theorem ellAdic_localizing_rightAdjoint_obj_isBounded
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  let F := ellAdicLocalizingLowerStar Λ ℓ g hΛ
  let hF : F.IsLeftAdjoint := ellAdic_isLeftAdjoint_localizingLowerStar Λ ℓ g hΛ
  let H := @Functor.rightAdjoint _ _ _ _ F hF
  let adjH : F ⊣ H := @Adjunction.ofIsLeftAdjoint _ _ _ _ F hF
  obtain ⟨a, b, hb⟩ := ellAdic_localizing_canonical_rightAdjoint_obj_isBounded
    Λ ℓ g hΛ hF K
  let e := adjH.rightAdjointUniq adj
  refine ⟨a, b, fun i hi ↦ ?_⟩
  let e' := (boundedConstructibleLocalizingClosure Λ Z.left).ι.mapIso
    (e.app ((boundedConstructibleToLocalizing Λ Y.left).obj K))
  exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e'.symm)

end AlgebraicGeometry.ProEtale.CondensedRing
