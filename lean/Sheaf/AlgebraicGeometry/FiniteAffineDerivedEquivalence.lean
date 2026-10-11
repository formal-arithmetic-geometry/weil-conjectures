/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Derived quasi-coherent equivalence for an affine morphism

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.5.4, Tag 0AVW
(blueprint: lem-sc-finite-affine-derived-equivalence).
-/

universe v wX wY wA

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine morphism gives an equivalence with quasi-coherent derived modules over
its direct-image algebra. Its functor is induced by `Rg_*` for the canonical morphism
`g : (X, O_X) → (Y, f_* O_X)`. Restricting scalars recovers `Rf_*`.
Source: Stacks Project, Tag 0AVW
(blueprint: lem-sc-finite-affine-derived-equivalence).

Proof:
1. The affine module correspondence (`lem-weil-pbc-affine-module-correspondence`)
   identifies quasi-coherent modules on X with quasi-coherent direct-image-algebra modules.
2. On affine stalks g is a localization map, hence flat. Its pullback is exact, and
   cohomology of its derived pullback is pullback of cohomology. The ringed-space derived
   adjunction (`lem-pc-ringed-spaces-derived-adjoint-general`) gives Lg-star left adjoint
   to Rg-star. First use Step 4 to identify scalar restriction of Rg-star with Rf-star.
   The affine cohomology formula (`lem-sc-affine-derived-cohomology`) then shows Rg-star
   has quasi-coherent cohomology over the direct-image algebra.
3. Lg-star also preserves quasi-coherent cohomology. Its underived functor agrees with
   the affine correspondence's two tensor operations by tensor associativity. Exactness
   identifies the cohomology maps of the derived unit and counit with the affine
   correspondence's beta and alpha, which are isomorphisms. Thus the restricted functors
   give mutually inverse equivalences.
4. Scalar restriction is exact: the underlying sheaves, kernels and cokernels are
   unchanged. Choose a K-injective representative I of K. Rg-star and Rf-star are the
   same complex f-star I with different scalar structures
   (`def-pc-ringed-spaces-derived-direct-image`, `def-pc-derived-direct-image`). Hence
   scalar restriction of the equivalence is naturally isomorphic to Rf-star. -/
theorem finite_affine_derived_equivalence {X Y : Scheme.{v}} (f : X ⟶ Y)
    [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ E : schemeDerivedQCohCategory X ≌ directImageAlgebraDerivedQCohCategory f,
      Nonempty (E.functor ⋙ (directImageAlgebraDerivedQCohProperty f).ι ≅
        (schemeDerivedQCohProperty X).ι ⋙
          RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)) ∧
      ∃ S : directImageAlgebraDerivedQCohCategory f ⥤ schemeDerivedQCohCategory Y,
        Nonempty (S ⋙ (schemeDerivedQCohProperty Y).ι ≅
          (directImageAlgebraDerivedQCohProperty f).ι ⋙
            (SheafOfModules.restrictScalars
              (R := moduleRings Y.toRingedSpace)
              (R' := moduleRings (directImageAlgebraSpace f))
              ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor) ∧
        Nonempty (E.functor ⋙ S ⋙ (schemeDerivedQCohProperty Y).ι ≅
          (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) := by
  sorry

end AlgebraicGeometry
