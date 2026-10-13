module

public import Sheaf.Algebra.Homology.FiniteStripConeGradedMap

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The row map jointly covers the current filtration step.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), diagonal quotient argument;
explicit cone refinement of lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-graded-map-split-epi)

The proof identifies the image of the row inclusion with the supremum prescribed
by `hsteps`; the induced map into that image subobject is therefore epic.
-/
theorem finiteStripGradedMap_factorThru_epi
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) : Epi ((F.complexStep p n).factorThru
      (finiteStripRowInclusion K A b f p n)
      (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p n)) := by
  sorry

end HomologicalComplex₂
