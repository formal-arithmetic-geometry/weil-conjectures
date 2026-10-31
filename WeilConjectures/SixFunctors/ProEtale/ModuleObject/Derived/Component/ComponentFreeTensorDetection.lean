/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import Mathlib.CategoryTheory.Generator.Sheaf

/-! # Detecting free component tensors by integral functions

Source: Hemo--Richarz--Scholbach, Construction (4.1), using the relative profinite tests.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]

/-- Maps into tensors of pulled-back free test sheaves are detected by integral functions
on each test. The tensor unit is the sheafification of the constant integral presheaf.

Source: Hemo--Richarz--Scholbach, Construction (4.1), the relative component tests;
Bhatt--Scholze, Lemma 2.2.8, the finite-clopen presentation of these tests
(blueprint: lem-zl-component-free-tensor-detection).

Proof: the inverse image of the free abelian sheaf represented by a relative test E is
its free abelian sheaf on the corresponding pro-etale test over T. This follows from
the two free-sheaf adjunctions and the inverse-image adjunction. Its tensor with the
free sheaf on E' is the free sheaf on their fiber product. Locally on any pro-etale
object, a section of this free sheaf is a finite integral sum of pairs of maps to the
two tests. Equalities of maps to the tests can be checked on their continuous profinite
coordinates, by the relative mapping property. At a point, discard repeated pairs by
adding their coefficients. Finite clopen partitions of E and E' separate the remaining
coordinates. The characteristic functions of their blocks define maps from the free
sheaves to the integral unit. Their pairwise tensor evaluations isolate every
coefficient. For each partition of the finite index set whose blocks have coefficient sum zero,
take the closed locus in the component space of the affine testing object where the
maps in each block coincide. The pointwise calculation says that these finitely many
closed profinite loci cover the component space. Their component pullbacks form a
finite jointly surjective pro-etale cover, by the relative-test construction applied
to the affine testing object. On each member of this cover the finite sum cancels
formally block by block. Sheaf separatedness therefore gives zero globally. Apply this to the
difference of the two morphisms, section by section. The empty test gives a zero free
sheaf, and the same conclusion holds without requiring a point of T or either test. -/
theorem component_free_tensor_detection
    (E E' : Over (affineComponentSpace T))
    {Z : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    (f g : Z ⟶
      (componentInverse T).obj
          (Sheaf.freeYoneda
            ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) E
            (𝟙_ Ab.{u + 1})) ⊗
        (componentInverse T).obj
          (Sheaf.freeYoneda
            ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) E'
            (𝟙_ Ab.{u + 1})))
    (h : ∀ (a : Sheaf.freeYoneda
        ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) E
        (𝟙_ Ab.{u + 1}) ⟶ 𝟙_ _)
      (b : Sheaf.freeYoneda
        ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) E'
        (𝟙_ Ab.{u + 1}) ⟶ 𝟙_ _),
      f ≫ ((componentInverse T).map a ⊗ₘ (componentInverse T).map b) =
        g ≫ ((componentInverse T).map a ⊗ₘ (componentInverse T).map b)) :
    f = g := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
