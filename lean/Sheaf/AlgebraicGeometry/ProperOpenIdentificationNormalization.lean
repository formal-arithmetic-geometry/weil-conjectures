/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparison

/-!
# Unit normalization of the proper/open restriction identification

Source: blueprint thm-cbc-finite-torsion, refinement comparison argument;
Stacks Project, More on Etale Cohomology, Tags 0F7B and 0F7I
(blueprint: lem-weil-pbc-proper-open-identification-unit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The specified proper/open restriction identification is the canonical restriction map,
after identifying `K` with `j₁^* j₁! K` by the extension-by-zero unit.
Source: blueprint thm-cbc-finite-torsion, proof step 5; Stacks Project, Tags 0F7B and 0F7I
(blueprint: lem-weil-pbc-proper-open-identification-unit).

Proof:
1. Put `V = T₁ ×[T₂] X`, with projections `b : V → T₁` and `p : V → X`, and let
   `s : X → V` be the section `(j₁,id)`. Then `s ≫ b = j₁` and `s ≫ p = id`.
   The section is clopen by `properOpenSectionGeometry`. The identification in the statement
   is the derived exchange for this pullback, followed by `Rp_*` of extension-by-zero
   base change and then the component restriction `Rp_* s_! K → K`.
2. Use the characterization in `clopenSectionDirectImage`: component restriction followed
   by the unit `K → s^* s_! K` is `Rp_*` of the unit for `s^* ⊣ Rs_*`, followed by the
   direct-image compositor for `s,p` and the identity direct-image identification.
   The displayed termwise extension-by-zero unit equals the derived unit: check this on
   bounded-below complexes with the localization factorization equations. Naturality moves
   extension-by-zero base change through that unit. Its transpose is the inverse-image
   composition identification for `s ≫ b = j₁`, by the defining mate equation for open
   base change. Thus the left side is restriction of the derived pullback exchange along s.
3. Express the derived exchange as the mate of the inverse-image square isomorphism.
   Its counit equation identifies restriction along s with inverse-image composition for
   `j₁ ≫ f = j₂`, followed by `j₁^*` of the counit for `f^* ⊣ Rf_*`.
   Conjugacy of the direct-image compositor and the inverse-image compositor cancels the
   intermediate `Rs_*` and `Rp_*` factors because `s ≫ p = id`.
   These are precisely the two factors on the right. This proves equality of the specified
   maps, for arbitrary bounded-below K; it also applies to the empty scheme and zero ring. -/
theorem properOpenIdentification_unit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (properOpenIdentification Λ f j₁ j₂ h K).hom ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j₁).unit.app K =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j₁ f j₂ h.symm).hom.app
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.counit.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
              K)) := by sorry

end AlgebraicGeometry.Etale
