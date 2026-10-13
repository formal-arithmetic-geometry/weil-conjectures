/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # Vertical filtration of a finite-strip augmentation cone

Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

/-- The cone has a degreewise finite vertical filtration with graded homology
identified with that of the individual horizontal augmentation cones.
No quasi-isomorphism hypothesis is made on the row maps.

Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), finite diagonal filtration.
(blueprint: lem-sc-finite-strip-cone-filtration)

Proof: In cone degree n filter by vertical degree at least p. Include the source
summand A.X (n+1) exactly when p ≤ n+1; include the (i,n-i) target summands exactly
when p ≤ n-i. Define the step as the finite sum of their images, and use the cone
inclusions and total inclusions for the maps. Horizontal differentials preserve
vertical degree; vertical differentials increase it. The off-diagonal cone map
lands in column zero by hb, so these steps are subcomplexes. The support hypothesis
bounds the target vertical degrees between n-r+1 and n. Thus step n-r is full and
step n+2 is zero, including when r=0. In the p-th graded quotient the vertical
part vanishes. The remaining objects and horizontal differential are the row
cone of f p, translated by p. At its initial term this uses hf and the canonical
single-term identification. The horizontal total sign is 1. The off-diagonal cone block is positive;
the negative source differential raises vertical degree and vanishes in the
quotient. Thus the three-term short complex of the graded object in degree n
is isomorphic to that of the row cone in degree n-p, using the canonical
single-complex identifications for its source summand. These short-complex
isomorphisms induce the stated homology isomorphisms. -/
theorem finite_strip_cone_filtration
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone b),
      (∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
          if p ≤ n - i then imageSubobject
            (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
              (CochainComplex.mappingCone.inr b).f n) else ⊥)) ∧
      (∀ n : ℤ, F.complexStep (n - (r : ℤ)) n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      (∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone (f p)).homology (n - p))) := by sorry

end HomologicalComplex₂
