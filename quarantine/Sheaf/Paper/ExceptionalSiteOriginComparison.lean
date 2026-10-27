/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Bounded-below site comparison on strict coefficient systems -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

/-- Construct comparison at a fixed etale evaluation package, and restrict its actual
unit and counit to bounded-below objects and finite etale origins.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 09B1.
(blueprint: lem-sf-exceptional-site-origin-comparison).

Proof: construct the ordinary geometric image for the actual site morphism and
apply unbounded derived comparison with the supplied etale package. Exact evaluation
localizes uniquely, so its prescribed package does not change the construction.
Realize each finite quotient as fixed-ring module sheaves. The bounded-below site
comparison identifies the finite unit as invertible. Its actual counit is invertible
on the essential image by the triangle identities. The evaluation unit and counit
identities and conservative evaluation give the system unit and origin counit.
Exact inverse image preserves lower bounds, as does its derived right adjoint.
The inverse tensor square identifies normalized reduction adjuncts; the counit
square and conservativity give descent of normalization. Finally evaluation is
exact, hence preserves each common system bound; the origin witness already gives
its finite origin. These arguments include the zero ring and empty scheme. -/
theorem exceptionalSiteOriginComparison
    (O : Type (u + 1)) [CommRing O] (ell : O)
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (T : Scheme.{u}) (PE : StrictEtaleEvaluation T O ell) :
    ∃ C : ExceptionalSystemSiteComparison O ell T PE,
      ExceptionalSystemSiteEquivalence C ∧
      (∀ n M, C.origin M → C.levelOrigin n ((C.proEvaluation.evaluation n).obj M)) ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) → IsIso ((C.image.level n).adjunction.unit.app M)) ∧
      (∀ n M, C.levelOrigin n M → IsIso ((C.image.level n).adjunction.counit.app M)) ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        C.levelOrigin n ((C.image.level n).inverse.obj M)) := by
  sorry

end AlgebraicGeometry
