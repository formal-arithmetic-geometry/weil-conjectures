module

public import Sheaf.Algebra.Homology.FiniteStripConeGradedMap

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical finite-strip graded map is epic.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), diagonal quotient argument;
explicit cone refinement of lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-graded-map-epi)

Proof: write the ambient cone in degree n as the biproduct of A.X (n+1)
and the total diagonal coproduct. The given hsteps identifies the current tail
with the sum of its supported generators. Suppose two arrows out of its graded
quotient agree after the displayed map. Precompose their difference with the
quotient projection, which is epic. On target generators with vertical index p,
the difference vanishes by the assumed equality after the row inclusion. Target
generators with vertical index strictly greater than p lie in the next tail and
are killed by the quotient; these are all remaining target generators. The source
generator survives only when n+1=p and is then the source summand of the row cone;
when n+1>p it lies in the next tail. The source single object is zero in all other
degrees. Thus the difference vanishes on every generator of the current tail,
so the two arrows agree. Unsupported horizontal summands are zero by hsupport.
This proves epimorphy also for r=0 and when n-p lies outside the strip. -/
theorem finiteStripGradedMap_epi
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
    (p n : ℤ) : Epi (finiteStripGradedMap K r hsupport A b f F hsteps p n) := by
  sorry

end HomologicalComplex₂
