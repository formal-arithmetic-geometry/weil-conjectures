/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.FiniteStripConeGradedMap
import Sheaf.Algebra.Homology.FiniteStripConeGradedMapEpi

/-! # Compatibility name for the finite-strip graded epimorphism

The row covers the current tail modulo the next tail. Its epimorphy is proved
in `FiniteStripConeGradedMapEpi`; this module reuses that existing theorem.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

/-- Compatibility name for the row-to-graded-quotient epimorphism.
Source: Stacks Project, Homology, Tag 0133; explicit finite-strip cone refinement.
(blueprint: lem-sc-finite-strip-cone-graded-map-split-epi)

The original prequotient assertion was false. The corrected conclusion is
exactly `finiteStripGradedMap_epi`, so reuse that theorem without restating it. -/
theorem finiteStripGradedMap_factorThru_epi
    {C : Type u} [Category.{v} C] [Abelian C]
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
    (p n : ℤ) : Epi (finiteStripGradedMap K r hsupport A b f F hsteps p n) :=
  finiteStripGradedMap_epi K r hsupport A b f F hsteps p n

end HomologicalComplex₂
