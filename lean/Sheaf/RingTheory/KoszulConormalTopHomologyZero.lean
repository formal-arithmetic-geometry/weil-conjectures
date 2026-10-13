module

public import Sheaf.RingTheory.KoszulConormalComparison

/-! Rank-zero top homology comparison.

(blueprint: lem-sc-koszul-conormal-top-homology-zero).

Proof in words: Evaluate the signed dual Koszul complex on the empty wedge; the incoming
differential is zero and the determinant normalization is the identity, hence the induced map is
an isomorphism.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext.
(blueprint: lem-sc-koszul-conormal-top-homology-zero).

The proof is the empty determinant calculation: the zero exterior power is the
coefficient module and both the incoming differential and determinant sign are
trivial.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- Rank-zero top homology determinant calculation. The empty signed dual Koszul wedge has zero
incoming differential, and determinant normalization is the identity, hence the induced map is an
isomorphism. (blueprint: lem-sc-koszul-conormal-top-homology-zero). -/
theorem koszul_conormal_comparison_isIso_top_homology_zero
    (A : Type u) [CommRing A] (I : Ideal A) (f : Fin 0 → A)
    (hf : Ideal.span (Set.range f) = I)
    (b : Module.Basis (Fin 0) (A ⧸ I) I.Cotangent)
    (hb : ∀ i, b i = koszulConormalVector A I 0 f hf (Finsupp.single i 1))
    (φ : koszulDualComplex A 0 f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) 0).obj
        (koszulNormalDeterminant A I 0))
    (hφ : IsKoszulConormalComparison A I 0 f hf φ) :
    IsIso (HomologicalComplex.homologyMap φ 0) := by sorry

end ExteriorAlgebra
