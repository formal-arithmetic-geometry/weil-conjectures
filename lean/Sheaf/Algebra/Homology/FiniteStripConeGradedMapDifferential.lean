/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Homology.FiniteStripConeGradedMap

/-! # Differentials on the surviving diagonal
Source: Stacks Project, Homology, Tag 0133; finite-strip cone refinement, step 3.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The surviving diagonal maps commute with the adjacent differentials.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), second-variable variant;
explicit diagonal quotient argument of lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-graded-map-differential)

Proof: use the biproduct decomposition of the row cone and check on its source
and target inclusions. For the target `(n-p,p)` summand, the horizontal total
term is the row differential with coefficient one. The vertical term has index
`p+1`, hence factors through the next tail and is killed by the quotient
projection. For the source summand, which is nonzero only at `n=p-1`, the cone
formula has the negative source differential and the augmentation block. The
source differential raises the vertical index and vanishes modulo the next tail.
The augmentation block equals `a p` followed by the `(0,p)` total inclusion by
`hb`; its row-cone counterpart equals the same map under the single-object
identification by `hf`. Away from this source degree its domain is zero. Finally
use the filtration inclusion and quotient projection being chain maps to identify
the resulting ambient-cone calculation with the graded differential. This proves
commutation without assuming the diagonal maps are invertible. -/
theorem finiteStripGradedMap_differential
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
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) :
    finiteStripGradedMap K r hsupport A b f F hsteps p n ≫
      (F.gradedPiece p).d n (n + 1) =
    (CochainComplex.mappingCone (f p)).d (n - p) (n + 1 - p) ≫
      finiteStripGradedMap K r hsupport A b f F hsteps p (n + 1) := by
  sorry

end HomologicalComplex₂
