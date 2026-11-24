/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FiniteStripConeGradedMap
import WeilConjectures.Algebra.Homology.FiniteStripConeGradedMapEpi
import WeilConjectures.Algebra.Homology.FiniteStripConeGradedMapMono

/-! # Invertibility of the surviving diagonal map

## References

* Stacks Project, Tag 0133
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The surviving diagonal map is an isomorphism in each degree. -/
theorem finiteStripGradedMap_isIso
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
    (p n : ℤ) : IsIso (finiteStripGradedMap K r hsupport A b f F hsteps p n) := by
  have : Epi (finiteStripGradedMap K r hsupport A b f F hsteps p n) :=
    finiteStripGradedMap_epi K r hsupport A b f F hsteps p n
  have : Mono (finiteStripGradedMap K r hsupport A b f F hsteps p n) :=
    finiteStripGradedMap_mono K r hsupport A b f F hsteps p n
  apply isIso_of_mono_of_epi

end HomologicalComplex₂
