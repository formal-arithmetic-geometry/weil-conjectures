/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace

/-!
# The full projective-line adjunction

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-adjunction.md
(blueprint: thm-amb-p1-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- On the entire ordinary etale derived categories, projective-line direct image
is left adjoint to inverse image followed by tensor with the shifted finite Tate line.
Its counit is exactly the normalized inverse-projection trace composite.
Source: blueprint thm-amb-p1-adjunction (blueprint: thm-amb-p1-adjunction).

Proof:
1. Take the adjunction of `projectiveLineTraceDatum`, supplied by the existing
   ordinary finite-coefficient projective-line theorem. Its normalized datum
   already includes both triangle identities.
2. The projective-line projection is proper with Noetherian source. The proper
   projection formula makes the ordered projection map an isomorphism for every
   unbounded object K.
3. Precompose both the datum's counit and `projectiveLineTraceEpsilon` with that
   projection. The datum's counit normalization identifies the first composite
   with tensoring by its normalized trace and the tensor unit constraint. The
   projection and its inverse cancel in the second composite, giving the same
   arrow. Cancel the projection to obtain the required counit equality. -/
theorem exists_projectiveLineFullAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ adj : (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)) ⊣
      ordinaryFiniteP1Right A N hA S,
      ∀ K : DerivedCategoryModule A S,
        adj.counit.app K = projectiveLineTraceEpsilon N hN A hA S hS K := by
  let dS := projectiveLineTraceDatum N hN A hA S hS
  let adj := dS.adjunction
  refine ⟨adj, ?_⟩
  intro K
  let : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  let : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  let : IsProper (ProjectiveLine S ↘ S) :=
    ProjectiveSpace.instIsProper (ULift (Fin 2)) S
  let : IsIso (ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K) :=
    isIso_proper_projection_formula_reordered A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K
  apply (cancel_epi
    (ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K)).1
  change _ = ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K ≫
    (inv (ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K) ≫
    ((ordinaryFiniteTensor A S).obj K).map
        (dS.decomposition.inv ≫ CategoryTheory.Limits.biprod.snd) ≫
      (derivedTensorSingleUnitIso K).hom)
  rw [IsIso.hom_inv_id_assoc]
  exact dS.counit_normalization K

end AlgebraicGeometry.Etale
