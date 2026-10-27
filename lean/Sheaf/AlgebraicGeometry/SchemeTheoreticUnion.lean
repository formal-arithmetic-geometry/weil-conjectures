/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Scheme-theoretic union of two closed subschemes

Source: Stacks Project, Morphisms, Definition 0C4H and Lemma 0C4J,
and Lemma 01QP; Algebra, Lemma 00E0 (9)
(blueprint: lem-weil-pbc-scheme-theoretic-union).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Morphisms, Definition 0C4H and Lemma 0C4J (first sentence and
its affine-local description), Lemma 01QP; Algebra, Lemma 00E0 (9).
(blueprint: lem-weil-pbc-scheme-theoretic-union)

The quasi-coherent ideal sheaves of the two closed immersions are `i'.ker` and `i''.ker`.
Their infimum is again quasi-coherent by the type `X.IdealSheafData`, and on every affine
open its ideal is the intersection of the two ideals (`IdealSheafData.ideal_inf`). Its
canonical closed subscheme is the scheme-theoretic union, locally the quotient spectrum.

Proof:
1. Apply the closed-immersion instance and `IdealSheafData.ker_subschemeι` to the
   intersection ideal. The source lemma `IdealSheafData.isPullback_subschemeCover_map`
   gives the affine quotient pullback square.
2. The intersection and the product of the two kernels have the same radical, by
   `IdealSheafData.radical_inf` and `radical_mul`. Their supports therefore agree by
   `support_radical`, and `support_mul` identifies this support with the union of the
   two kernel supports. By `Hom.support_ker` and closedness of the two images, these
   supports are the original images.
3. The intersection is contained in each kernel. Use `IsClosedImmersion.lift` and
   `lift_fac` to factor each original immersion through the union. Each factor is a
   closed immersion by `IsClosedImmersion.of_comp_isClosedImmersion`. -/
theorem scheme_theoretic_union
    {X Z' Z'' : Scheme.{u}} (i' : Z' ⟶ X) (i'' : Z'' ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i''] :
    IsClosedImmersion (i'.ker ⊓ i''.ker).subschemeι ∧
      (i'.ker ⊓ i''.ker).subschemeι.ker = i'.ker ⊓ i''.ker ∧
      (∀ U : X.affineOpens,
        IsPullback ((i'.ker ⊓ i''.ker).subschemeCover.f U)
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk ((i'.ker ⊓ i''.ker).ideal U))))
          (i'.ker ⊓ i''.ker).subschemeι U.2.fromSpec) ∧
      Set.range (i'.ker ⊓ i''.ker).subschemeι.base =
        Set.range i'.base ∪ Set.range i''.base ∧
      (∃ a' : Z' ⟶ (i'.ker ⊓ i''.ker).subscheme,
        IsClosedImmersion a' ∧
          a' ≫ (i'.ker ⊓ i''.ker).subschemeι = i') ∧
      (∃ a'' : Z'' ⟶ (i'.ker ⊓ i''.ker).subscheme,
        IsClosedImmersion a'' ∧
          a'' ≫ (i'.ker ⊓ i''.ker).subschemeι = i'') := by
  let I := i'.ker ⊓ i''.ker
  refine ⟨inferInstance, I.ker_subschemeι,
    fun U ↦ I.isPullback_subschemeCover_map U, ?_, ?_, ?_⟩
  · have hs : I.support = i'.ker.support ⊔ i''.ker.support := by
      calc
        I.support = I.radical.support := I.support_radical.symm
        _ = (i'.ker * i''.ker).radical.support := by
          rw [Scheme.IdealSheafData.radical_mul, Scheme.IdealSheafData.radical_inf]
        _ = (i'.ker * i''.ker).support := Scheme.IdealSheafData.support_radical _
        _ = i'.ker.support ⊔ i''.ker.support := Scheme.IdealSheafData.support_mul _ _
    change Set.range I.subschemeι = Set.range i' ∪ Set.range i''
    rw [I.range_subschemeι, hs, TopologicalSpace.Closeds.coe_sup,
      Scheme.Hom.support_ker, Scheme.Hom.support_ker,
      i'.isClosedEmbedding.isClosed_range.closure_eq,
      i''.isClosedEmbedding.isClosed_range.closure_eq]
  · have h : I.subschemeι.ker ≤ i'.ker := by
      rw [I.ker_subschemeι]
      exact inf_le_left
    let a := IsClosedImmersion.lift I.subschemeι i' h
    have ha : a ≫ I.subschemeι = i' := IsClosedImmersion.lift_fac _ _ _
    have : IsClosedImmersion (a ≫ I.subschemeι) := ha ▸ inferInstance
    exact ⟨a, IsClosedImmersion.of_comp_isClosedImmersion a I.subschemeι, ha⟩
  · have h : I.subschemeι.ker ≤ i''.ker := by
      rw [I.ker_subschemeι]
      exact inf_le_right
    let a := IsClosedImmersion.lift I.subschemeι i'' h
    have ha : a ≫ I.subschemeι = i'' := IsClosedImmersion.lift_fac _ _ _
    have : IsClosedImmersion (a ≫ I.subschemeι) := ha ▸ inferInstance
    exact ⟨a, IsClosedImmersion.of_comp_isClosedImmersion a I.subschemeι, ha⟩

end AlgebraicGeometry
