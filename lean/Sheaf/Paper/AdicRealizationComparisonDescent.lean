/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Common-stage realization comparison descent

This is the comparison and representative-agreement part of the integral descent
argument for one scheme isomorphism. Source: Bhatt--Scholze, Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-comparison-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/--
Given the balanced integral reindexings, the common-stage realization comparison
exists and agrees with each integral representative. The proof composes the
specified realization isomorphisms with the inverse derived balanced comparison
and the completion-unit comparison. Naturality is checked after representing an
arrow over one finite field; scalar extension uses the specified finite-free
comparison and the scalar compatibility square. The inverse components descend by
the same argument. This theorem asserts no tensor or identity/composition law.
 (blueprint: lem-sf-adic-realization-comparison-descent)
-/
theorem exists_realization_comparison_descent (D : FiniteFieldDatum.{u})
    (d : ∀ T : GeometricSpace D, SpaceData l D T)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (B : RingReindex l T.base.left g.hom (d T).realization (d U).realization)
    (I : ∀ E, IntegralReindex l T.base.left g.hom B E) :
    letI := (d T).units
    letI := (d U).units
    ∃ c : commonStageDerivedPullback l (PadicAlgCl l) g.hom ⋙
        ordinary l T.base.left (d T).realization ≅
      ordinary l U.base.left (d U).realization ⋙ derivedPull l T.base.left g.hom B,
    ∀ E, integralRealizationAgreement l g.hom (d T).realization (d U).realization
      B E (I E) c := by
  sorry

end WeilConjectures.AdicQbarRealization
