module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Fppf local square roots of global units

Source: Stacks Project, Tag 040N, `lemma-kummer-sequence-syntomic`, the local surjectivity
of the power map for exponent two (blueprint: lem-sfb-fppf-local-unit-square-root).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every global unit has a unit square root on an fppf covering, including in
characteristic two and on nonreduced schemes.

Source: Stacks Project, Tag 040N, `lemma-kummer-sequence-syntomic`, exponent two
(blueprint: lem-sfb-fppf-local-unit-square-root).

Proof:
1. Set A = Γ(T, O_T), B = A[x]/(x²-s), and let b be the class of x. The relation
   b² = α(s) follows from def-weil-pbc-algebra-hom-quotient. Apply
   lem-sfb-monic-quotient-faithful-tensor-coordinates with d = 2, a₀ = -s and a₁ = 0:
   the structure map α : A → B is faithfully flat, even if A is the zero ring.
2. Form q = Spec(α) using def-weil-affine-spectrum. Faithful flatness gives flatness
   by def-weil-pbc-faithfully-flat-ring-map and lem-weil-pbc-flat-ring-map-iff-flat-affine;
   lem-weil-pbc-faithfully-flat-surjective-spectrum gives surjectivity. The presentation
   with one generator and one relation gives local finite presentation by
   def-sbc-locally-finite-presentation. Thus {q} is a cover by def-pc-fppf-site.
3. By lem-weil-pbc-morphism-into-affine-scheme, the identity of A defines
   j : T → Spec(A), with j* ε_A = id_A for the canonical sections isomorphism ε_A.
   Form V = T ×_{Spec(A)} Spec(B) by def-pc-fibre-product, with projections
   f : V → T and h : V → Spec(B). The equality j f = q h and
   lem-trf-fppf-covering-base-change show that {f} is an fppf covering.
4. Set r = h* ε_B(b). By lem-weil-pbc-spec-map-global-sections and the pullback
   equality, r² = h* ε_B(α(s)) = h* q* ε_A(s) = f* j* ε_A(s) = f* s.
   Its inverse is r f*(s⁻¹), since r · r f*(s⁻¹) = f*(s s⁻¹) = 1.
   Use the singleton family (V,f,r). All calculations apply to the empty scheme
   and require neither invertibility of two nor reducedness.
-/
theorem exists_fppf_unit_square_root (T : Scheme.{u}) (s : Γ(T, ⊤)ˣ) :
    ∃ (I : Type u) (T' : I → Scheme.{u}) (f : ∀ i : I, T' i ⟶ T),
      Presieve.ofArrows T' f ∈ fppfPrecoverage T ∧
        ∃ r : ∀ i : I, Γ(T' i, ⊤)ˣ,
          ∀ i : I, (r i : Γ(T' i, ⊤)) ^ 2 = (f i).appTop (s : Γ(T, ⊤)) := by
  sorry

end AlgebraicGeometry.Scheme
