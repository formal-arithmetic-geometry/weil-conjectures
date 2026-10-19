/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Kernel of a thick Verdier quotient

Source: Stacks Project, Derived Categories, Tags 05RG, 05RI, 05RK
(blueprint: lem-per-thick-verdier-quotient-kernel).
-/

@[expose] public section

universe u v uE vE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The Verdier quotient by a thick triangulated subcategory is exact, is the localization
at the morphisms with cone in that subcategory, and kills exactly its objects.
Source: Stacks Project, Derived Categories, Tags 05RG, 05RI, 05RK
(blueprint: lem-per-thick-verdier-quotient-kernel).

Proof:
1. Let W = S.trW. The cone-system lemma (lem-trf-triangulated-subcategory-cone-system)
   gives identities, composition, both calculi of fractions and triangulation compatibility.
   Take the canonical localization W.Q, as in def-pur-saturated-triangulated-localization.
2. By lem-pur-localization-triangles-05r6 its target has the induced triangulated structure
   and the quotient functor is exact, hence additive and preserves zero morphisms.
3. If S A, the inverse rotation of the contractible triangle shows that 0 : 0 ⟶ A
   has cone A and is in W. Its image is invertible and zero, so the identity of Q(A)
   is zero. Thus Q(A) is a zero object.
4. If Q(A) is zero, the identity and zero endomorphisms of A have equal images.
   Apply lem-pc-right-fraction-common-refinement to their right fractions with identity
   denominators. A common refinement gives a zero morphism R ⟶ A belonging to W.
5. Choose its distinguished triangle R ⟶ A ⟶ C ⟶ R[1] with S C. Clause (iii) of
   lem-weil-pbc-hom-into-triangle-exact gives a section k of C ⟶ R[1]. Applying clause
   (ii) to the rotated triangle factors id_C - k h through A ⟶ C, giving q : C ⟶ A.
   Exactness for the original triangle makes A ⟶ C monic: a map killed by it factors
   through R ⟶ A = 0. Consequently q g = id_A and q k = 0, while h g = 0 and h k = id.
   Hence (g,k) and (q,h) identify C with A ⊕ R[1]. Retract closure gives S A.
-/
theorem thick_verdier_quotient_kernel {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (S : ObjectProperty C) [S.IsTriangulated] [S.IsStableUnderRetracts] :
    S.trW.Q.IsTriangulated ∧
      Functor.IsStrictLocalizationAt.{u, v, u, max u v, uE, vE} S.trW.Q S.trW ∧
      ∀ A : C, IsZero (S.trW.Q.obj A) ↔ S A := by
  sorry

end CategoryTheory
