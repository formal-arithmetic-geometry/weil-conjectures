/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.CategoryTheory.FilteredDerivedOperationStructures

/-!
# Exact functors on finite filtered objects

Source: Stacks Tag 05RX, exact termwise construction in Step 1 of
lem-trf-filtered-derived-operation-lifts
(blueprint: lem-trf-exact-filtered-object-action).
-/

@[expose] public section
set_option autoImplicit false

universe wA vA uA wB vB uB
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Exact functors act on finite filtered objects and commute with their evaluations.
Source: Stacks Tag 05RX; Step 1 of lem-trf-filtered-derived-operation-lifts.

Proof: send (M,F) to H(M) with steps the subobjects represented by H(F^p M → M).
Left exactness preserves these monomorphisms; the relation between successive steps
is H of the original relation. H preserves zero objects and isomorphisms, so both
finite bounds and every prescribed interval are preserved. For a filtered map apply
H to its underlying arrow and each restriction square. Functoriality and additivity
follow on underlying arrows. The comparison with forgetting is the identity; the
step comparison is the inverse of the canonical underlyingIso for the represented
subobject. Exactness preserves the cokernel of F^(p+1) → F^p, giving the grade
comparison. Its naturality follows by the cokernel universal property. The step
inclusion equation is the defining underlyingIso equation. These constructions also
apply to zero objects, empty intervals (which contain only zero objects), and unrestricted
finite filtrations; no injectivity or splitting is required.
(blueprint: lem-trf-exact-filtered-object-action). -/
theorem exactFilteredObjectAction
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (bounds : Option (ℤ × ℤ)) :
    ∃ action : FiniteFilteredObjects A bounds false ⥤ FiniteFilteredObjects B bounds false,
    ∃ additive : action.Additive,
    ∃ evaluation : ∀ p : Option ℤ,
      action ⋙ filteredEvaluation B bounds false p ≅
        filteredEvaluation A bounds false p ⋙ H,
    ∃ step : ∀ (K : FiniteFilteredObjects A bounds false) (p : ℤ),
      (((action.obj K).obj.filtration.step p : B)) ≅ H.obj (K.obj.filtration.step p : A),
    ∀ (K : FiniteFilteredObjects A bounds false) (p : ℤ),
      ((action.obj K).obj.filtration.step p).arrow ≫ (evaluation none).hom.app K =
        (step K p).hom ≫ H.map (K.obj.filtration.step p).arrow := by
  sorry

end CategoryTheory
