/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.IntegralCanonicalTruncations
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! # The bounded standard integral t-structure

Source: blueprint, smooth base change, order 1431; BBD 1.3.1--1.3.6
(blueprint: prop-weil-pbc-integral-tstructure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable [hNoeth : IsNoetherian T] [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
include hNoeth hDim hInv

/-- The actual integral category has the inherited triangulated structure.
Source: order 1431 (blueprint: prop-weil-pbc-integral-tstructure).
Proof: intrinsic completion is invariant under isomorphisms, shifts and triangles.
Refine the two finite stratifications and take common local models. Their cones remain
bounded complexes with adic-lisse finite-type terms; the finite coefficient categories
are abelian, and their finite-lisse cohomology is stable under kernels, cokernels and
extensions. Exact comparison inverse image transports the cone and its retained origins.
Their normalizations satisfy the quotient cocycle by functoriality. Zero satisfies all
three conditions. Thus the full subcategory is triangulated with inherited triangles. -/
@[instance] theorem pbcIntegralProperty_isTriangulated :
    ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) := by
  exact (pbcIntegralUniformComplete_isTriangulated l E T hDim.out hInv.out).2

/-- Ambient canonical truncation induces the standard integral t-structure.
Source: order 1431 (blueprint: prop-weil-pbc-integral-tstructure).
Proof: pbcIntegralCanonicalTruncations_mem gives closure under both ambient truncations.
The ambient canonical truncation triangle has its two terms in the integral category,
so HasInducedTStructure.mk' supplies the required truncation triangles. Fullness gives
orthogonality, and the inherited shifts give the two shift axioms. -/
@[instance] theorem pbcIntegralProperty_hasInducedTStructure :
    ObjectProperty.HasInducedTStructure
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
      (pbcAmbientTStructure T l E) := by
  exact ObjectProperty.HasInducedTStructure.mk'
    (fun X hX m ↦ pbcIntegralCanonicalTruncations_mem T l E ⟨X, hX⟩ m)

/-- The induced standard integral t-structure, using Mathlib's actual construction.
Source: order 1431 (blueprint: prop-weil-pbc-integral-tstructure). -/
def pbcIntegralTStructure :=
  ObjectProperty.tStructure
    (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
    (pbcAmbientTStructure T l E)

/-- The inherited shifts are linear for the actual constant-section scalar action.
Source: order 1431 (blueprint: prop-weil-pbc-integral-tstructure).
Proof: the full inclusion is faithful and linear, its comparison with shift is induced
by the ambient shift, and the ambient derived shift is linear. Faithfulness tests the
scalar equation and gives it in the full subcategory. -/
@[instance] theorem pbcIntegralShift_isLinear (n : ℤ) :
    (shiftFunctor (PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) n).Linear
      (PbcIntegralRing l E) := by
  let P : ObjectProperty (PbcCompletedDerived T (pbcIntegralDatum l E)) :=
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
  have : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear (PbcIntegralRing l E) :=
    Functor.linear_of_iso (PbcIntegralRing l E) (P.ι.commShiftIso n).symm
  refine ⟨fun f r ↦ P.ι.map_injective ?_⟩
  simpa only [Functor.map_smul, Functor.comp_map] using
    (shiftFunctor P.FullSubcategory n ⋙ P.ι).map_smul r f

/-- The standard integral structure is bounded, its heart is cohomology in degree zero,
and its canonical truncations are the ambient ones. Uniformizer torsion is preserved
with the same exponent. Source: order 1431; BBD 1.3.3
(blueprint: prop-weil-pbc-integral-tstructure).
Proof: the uniformly bounded local finite models give a finite cohomology interval
for each complete object. This proves boundedness. The induced aisle and coaisle are
ambient degree bounds, so their intersection says precisely that all nonzero-degree
cohomology vanishes. The ambient canonical truncation triangles lie in the subcategory;
uniqueness of truncation triangles supplies the two natural isomorphisms. On the domain
of pbc_integral_truncations those ambient truncations are the specified Roos limits,
so these identifications also compare the tower constructions. For torsion, compose
p^N id on a lower truncation with its counit, or precompose p^N id on an upper truncation
with its unit. Bilinearity makes the resulting map zero when p^N id_K is zero. The
respective adjunctions are injective on Hom, so both truncated identities are killed
by that same p^N. -/
theorem pbc_integral_tstructure :
    (pbcIntegralTStructure T l E).bounded = ⊤ ∧
    (∀ K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
      (pbcIntegralTStructure T l E).heart K ↔
        ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj)) ∧
    (∀ m : ℤ,
      Nonempty ((pbcIntegralTStructure T l E).truncLE m ⋙
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ≅
        (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
          (pbcAmbientTStructure T l E).truncLE m) ∧
      Nonempty ((pbcIntegralTStructure T l E).truncGE m ⋙
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ≅
        (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
          (pbcAmbientTStructure T l E).truncGE m)) ∧
    ∀ (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
      (N : ℕ), 1 ≤ N → (pbcUniformizer l E) ^ N • 𝟙 K = 0 →
      ∀ m : ℤ,
        (pbcUniformizer l E) ^ N •
          𝟙 (((pbcIntegralTStructure T l E).truncLE m).obj K) = 0 ∧
        (pbcUniformizer l E) ^ N •
          𝟙 (((pbcIntegralTStructure T l E).truncGE m).obj K) = 0 := by
  let P : ObjectProperty (PbcCompletedDerived T (pbcIntegralDatum l E)) :=
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
  let t := pbcIntegralTStructure T l E
  let s := pbcAmbientTStructure T l E
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_antisymm le_top
    intro K _
    have hl : IsUnit (l : Γ(T, ⊤)) :=
      T.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ (by
        intro x hx
        simpa using hInv.out x)
    obtain ⟨a, b, hab, ha, hb⟩ :=
      (((integralStratifiedPerfectCharacterization T l E hDim.out hl K.obj).2).mp
        (((integralStratifiedPerfectCharacterization T l E hDim.out hl K.obj).1).mp
          K.property)).1
    exact ⟨⟨a, (ObjectProperty.tStructure_isGE_iff P s K a).mpr ha⟩,
      ⟨b, (ObjectProperty.tStructure_isLE_iff P s K b).mpr hb⟩⟩
  · intro K
    change (P.tStructure s).heart K ↔ _
    rw [(P.tStructure s).mem_heart_iff, ObjectProperty.tStructure_isLE_iff,
      ObjectProperty.tStructure_isGE_iff]
    change K.obj.IsLE 0 ∧ K.obj.IsGE 0 ↔ _
    rw [DerivedCategory.isLE_iff, DerivedCategory.isGE_iff]
    constructor
    · rintro ⟨hle, hge⟩ i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact hge i hi
      · exact hle i hi
    · intro h
      exact ⟨fun i hi ↦ h i (by omega), fun i hi ↦ h i (by omega)⟩
  · have : P.ι.IsTExact t s :=
      { isLE := fun K n h ↦ (ObjectProperty.tStructure_isLE_iff P s K n).mp h
        isGE := fun K n h ↦ (ObjectProperty.tStructure_isGE_iff P s K n).mp h }
    intro m
    exact ⟨⟨P.ι.eTruncLTIso t s (m + 1 : ℤ)⟩, ⟨P.ι.eTruncGEIso t s m⟩⟩
  · intro K N hN hK m
    change (pbcUniformizer l E) ^ N • 𝟙 ((t.truncLE m).obj K) = 0 ∧
      (pbcUniformizer l E) ^ N • 𝟙 ((t.truncGE m).obj K) = 0
    constructor
    · apply t.to_truncLE_obj_ext
      simpa using
        congrArg (fun f ↦ (t.truncLEι m).app K ≫ f) hK
    · apply t.from_truncGE_obj_ext
      simpa using
        congrArg (fun f ↦ f ≫ (t.truncGEπ m).app K) hK

end AlgebraicGeometry.Scheme
