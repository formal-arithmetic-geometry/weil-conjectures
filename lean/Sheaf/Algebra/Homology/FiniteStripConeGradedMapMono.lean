module

public import Sheaf.Algebra.Homology.FiniteStripConeGradedMap

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical finite-strip graded map is monic.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), diagonal quotient argument;
explicit cone refinement of lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-graded-map-mono)

Proof: project the ambient cone in degree n onto its target diagonal summand
K.X (n-p).X p, using the total coproduct projection, and onto its source summand
A.X (n+1) only when n+1=p. Identify the latter with the degree n-p+1 object
of single(A.X p,0); in other degrees that single object is zero. Combine these
projections using the degreewise biproduct decomposition of Cone(f p). Restrict
to the current tail. Each target generator of the next tail has vertical index
at least p+1 and is killed by this projection. Its source generator is present
only when p+1<=n+1, which excludes n+1=p, so it too is killed. Hence the restricted
projection descends through the evaluated cokernel defining the graded quotient.
Its composite with finiteStripGradedMap is the identity: check the two row cone
summands using the biproduct projection-inclusion identities and the total
coproduct identities. If n-p is outside [0,r), that target object is zero by
hsupport; the identity there is zero. The source identity is checked at n+1=p,
and otherwise its object is zero. Thus this descended arrow is a left inverse,
which implies monomorphy. This includes r=0, where only the source can survive. -/
theorem finiteStripGradedMap_mono
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
    (p n : ℤ) : Mono (finiteStripGradedMap K r hsupport A b f F hsteps p n) := by
  sorry

end HomologicalComplex₂
