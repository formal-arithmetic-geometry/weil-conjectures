/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import all Sheaf.Paper.AdicResidueExtensionClosure

/-!
# Triangulated closure of the residue condition

Source: Bhatt--Scholze, Definition 6.5.1, Remark 6.3.2 and Proposition 6.6.11.
(blueprint: lem-sfb-adic-residue-triangulated).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] completedAdicDerivedChange

/-- The bounded constructible etale residue condition is triangulated and invariant
under isomorphisms, independently of the completeness of the original complex.
Source: Bhatt--Scholze, Definition 6.5.1 and Remark 6.3.2; Stacks Tag 09AL.
(blueprint: lem-sfb-adic-residue-triangulated).

Proof: Exact fixed-scalar restriction composed with derived reduction gives the residue
functor, with value canonically isomorphic to Q(sfbResidueComplex). The preceding
residue-extension module identifies its bounded constructible etale essential-image
condition with IsSfbResidueConstructible. The reverse direction uses flatness of every
residue-field module sheaf to supply the Tor interval. The etale bounded constructible
subcategory is triangulated, and its bounded-below comparison is fully faithful, so
its image in the unbounded pro-etale derived category is triangulated. Pull back this
isomorphism-invariant object property along the triangulated residue functor -/
theorem sfb_adic_residue_triangulated
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    : ObjectProperty.IsClosedUnderIsomorphisms (IsSfbResidueConstructible X I) ∧
      ObjectProperty.IsTriangulated (IsSfbResidueConstructible X I) := by
  let k := A ⧸ I ^ (0 + 1)
  have : (I ^ (0 + 1)).IsMaximal := by simpa using hI.1
  let : Field k := Ideal.Quotient.field (I ^ (0 + 1))
  have : (residueFunctor X I).IsTriangulated := by
    dsimp only [residueFunctor]
    infer_instance
  let : (etaleImageFunctor X k).CommShift ℤ := by
    dsimp only [etaleImageFunctor]
    infer_instance
  have : (etaleImageFunctor X k).IsTriangulated := by
    dsimp only [etaleImageFunctor]
    infer_instance
  let P := (etaleImageFunctor X k).essImage.inverseImage (residueFunctor X I)
  have heq : IsSfbResidueConstructible X I = P := by
    funext K
    apply propext
    exact ⟨residue_mem_image X I K, residue_of_mem_image X I hI.1 K⟩
  rw [heq]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
