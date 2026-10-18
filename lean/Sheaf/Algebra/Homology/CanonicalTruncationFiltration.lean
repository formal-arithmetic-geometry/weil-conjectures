/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Canonical truncation filtration

Source: Stacks Project, `literature/stacks-project/homology.tex`, Tag 0118,
with Remark 08J5 (blueprint: lem-kun-canonical-truncation-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Canonical good-truncation filtration of a bounded complex, its graded pieces,
naturality, homotopies, and quasi-isomorphism invariance.

Source: Stacks Project, Homology Tag 0118 and Derived Categories Remark 08J5
(blueprint: lem-kun-canonical-truncation-filtration).

Proof steps: choose lower and upper degree bounds and use the canonical truncations;
pin the filtration steps to the canonical subobjects given by the truncation
inclusions; apply `CochainComplex.exists_upperTruncationStepSES` to identify each
quotient with the two-term image-to-kernel complex and to construct the comparison
family to shifted cohomology; use its naturality clause for chain maps; restrict a
chain homotopy degreewise to the truncations; and finally use that a quasi-isomorphism
induces an isomorphism on every cohomology object.
The filtration and filtered homotopy notions are those of
`CategoryTheory.DecreasingFiltration` and `CochainComplex.FiniteFilteredModuleHomotopy`.
-/
theorem exists_canonicalTruncationFiltration :
    ∃ (F : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      DecreasingFiltration K)
      (pi : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).gradedPiece i ⟶
          (singleFunctor (ModuleCat.{u} R) (-i)).obj (K.homology (-i))),
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (i : ℤ),
        (F K).step i = Subobject.mk (K.ιTruncLE (-i))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
        (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
          ∃ (a b : ℤ), a < b ∧ (F K).step a = ⊤ ∧ (F K).step b = ⊥) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (i : ℤ),
        ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ)
          (e : (F K).gradedPiece i ≅ M)
          (e₀ : M.X (-i - 1) ≅ cokernel (kernel.ι (K.d (-i - 1) (-i))))
          (e₁ : M.X (-i) ≅ K.cycles (-i)),
          (∀ (r : ℤ), r ≠ -i - 1 → r ≠ -i → IsZero (M.X r)) ∧
          Mono (M.d (-i - 1) (-i)) ∧
          cokernel.π (kernel.ι (K.d (-i - 1) (-i))) ≫ e₀.inv ≫
              M.d (-i - 1) (-i) ≫ e₁.hom ≫ K.iCycles (-i) =
            K.d (-i - 1) (-i) ∧
          (pi K i).f (-i) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-i)
                (K.homology (-i))).hom =
            e.hom.f (-i) ≫ e₁.hom ≫ K.homologyπ (-i) ∧
          QuasiIso (pi K i)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        ∃ (φ : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
          φ.hom = f ∧
          ∀ (i : ℤ),
            FilteredObject.gradedMapSteps φ i ≫ pi L i =
              pi K i ≫
                (singleFunctor (ModuleCat.{u} R) (-i)).map
                  (HomologicalComplex.homologyMap f (-i))) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f g : K ⟶ L),
        (h : Homotopy f g) →
          ∃ (hf : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
            hf.hom = f ∧
            ∃ (hg : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
              hg.hom = g ∧
              ∀ (i n m : ℤ),
                ∃ lift : ((F K).step i : CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
                  ((F L).step i : CochainComplex (ModuleCat.{u} R) ℤ).X m,
                  lift ≫ ((F L).step i).arrow.f m =
                    ((F K).step i).arrow.f n ≫ h.hom n m) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        (∀ (r : ℤ), IsIso (K.homologyMap f r)) →
          ∀ (i : ℤ), ∃ (φ : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
            φ.hom = f ∧ QuasiIso (FilteredObject.gradedMapSteps φ i)) := by
  sorry

end CochainComplex
