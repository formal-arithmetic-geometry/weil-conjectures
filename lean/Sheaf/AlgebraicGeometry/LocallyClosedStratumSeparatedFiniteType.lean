/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Reduced locally closed strata are separated and of finite type

Source: Stacks Project, Tags 01J3, 01J4, 01KU(1), 01T3, 01T5, 01T6, 01OX, and 035C.
(blueprint: lem-dl-a1-locally-closed-stratum-separated-finite-type)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme.IdealSheafData

-- The chosen containing open already implies the locally-closed hypothesis.
set_option linter.unusedVariables false in
/-- The reduced induced stratum inside an open containing `S` is an immersion with image
`S`, and its composite structure morphism is separated and of finite type over the field.
For an empty subset, the stratum is isomorphic to the empty scheme.

Source: Stacks Project, Tags 01J3, 01J4, 01KU(1), 01T3, 01T5, 01T6, 01OX, and 035C.
(blueprint: lem-dl-a1-locally-closed-stratum-separated-finite-type)

Proof:
1. The closed immersion cut out by the vanishing ideal has range `U.ι ⁻¹' S`, by
   Mathlib's `range_subschemeι` and `coe_support_vanishingIdeal`. Composing with the
   open immersion gives an immersion with range `S`, since `S` is contained in `U`.
2. The field spectrum is locally Noetherian. By locally finite type permanence, `T`
   is locally Noetherian, so the open immersion `U.ι` is quasi-compact (Tag 01OX).
3. Closed and open immersions are separated and locally of finite type; the closed
   immersion is also quasi-compact. Compose these properties with the assumed
   properties of the structure morphism to obtain all three asserted properties.
4. If `S` is empty, the range calculation makes the stratum's underlying space empty.
   A scheme with empty underlying space is initial, hence isomorphic to `Scheme.empty`. -/
theorem locallyClosedStratum_separated_finiteType
    (k : Type u) [Field k] (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (S : Set T) (hS : IsLocallyClosed S) (U : T.Opens) (hSU : S ⊆ (U : Set T))
    (hclosed : IsClosed (U.ι ⁻¹' S)) :
    IsImmersion ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι ≫ U.ι) ∧
    Set.range ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι ≫ U.ι) = S ∧
    IsSeparated
      ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι ≫ U.ι ≫ T ↘ Spec (.of k)) ∧
    LocallyOfFiniteType
      ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι ≫ U.ι ≫ T ↘ Spec (.of k)) ∧
    QuasiCompact
      ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι ≫ U.ι ≫ T ↘ Spec (.of k)) ∧
    (S = ∅ → Nonempty ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subscheme ≅ Scheme.empty)) := by
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have hrange :
      Set.range ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι ≫ U.ι) = S := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      range_subschemeι, coe_support_vanishingIdeal]
    exact Set.image_preimage_eq_of_subset (by simpa using hSU)
  refine ⟨inferInstance, hrange, inferInstance, inferInstance, inferInstance, ?_⟩
  intro hSempty
  have : IsEmpty (vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subscheme := by
    refine ⟨fun x ↦ ?_⟩
    have hx := Set.mem_range_self
      (f := ((vanishingIdeal ⟨U.ι ⁻¹' S, hclosed⟩).subschemeι ≫ U.ι)) x
    exact (Set.eq_empty_iff_forall_notMem.mp hSempty) _ (hrange ▸ hx)
  exact ⟨isInitialOfIsEmpty.uniqueUpToIso emptyIsInitial⟩

end AlgebraicGeometry
