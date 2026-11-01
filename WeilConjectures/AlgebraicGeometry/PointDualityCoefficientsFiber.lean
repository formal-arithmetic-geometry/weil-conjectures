/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.PoincareDualityConventions.PoincareDualityConventions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Coefficients and derived fiber for point duality

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
lem-pod-point-dualizing-complex.md, fixed setting and point evaluation
(blueprint: def-pod-condensed-point-coefficients-fiber).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

end WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- Derived point fiber: transport by the inverse of actual point pullback, then
right-derived singleton evaluation. The equivalence theorem for separably closed
points supplies the inverse; no equivalence with all scalar modules is assumed.
Source: current blueprint lem-pod-point-dualizing-complex, point category;
def-weil-finite-coefficient-point, evaluation
(blueprint: def-pod-condensed-point-coefficients-fiber). -/
def pointDualityFiber
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    DerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k)))) ⥤
      @DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) inferInstance inferInstance
        (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (condensedScalarRing Λ)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  letI := Functor.additive_of_preserves_binary_products e.inverse
  e.inverse.mapDerivedCategory ⋙
    CondensedRing.Evaluation.G (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})

/-- The chosen compactification of the identity of the geometric point, using the
canonical identity structure map to Spec k. This is the chosen compactification,
not the proper identity compactification used to compute its comparison.
Source: def-sfb-compactification-over-field and def-pod-conventions
(blueprint: def-pod-condensed-point-coefficients-fiber). -/
def pointDualityCompactification (k : Type u) [Field k] :
    Compactification (𝟙 (Spec (.of k))) := by
  letI : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩
  exact (compactificationOverField k (𝟙 (Spec (.of k)))).obj.obj

end AlgebraicGeometry.ProEtale
