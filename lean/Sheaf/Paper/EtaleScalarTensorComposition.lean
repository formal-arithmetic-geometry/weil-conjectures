/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.ExceptionalCoefficientMaps
public import Sheaf.Paper.NormalizedOriginScalarComparisons

/-! # Tensor compatibility of the fixed scalar comparisons

Source: Stacks 07A4 and 0D6D, the tensor clause of the finite-Hom domain calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.ExceptionalCoefficients

/-- The published scalar tensor comparison respects the fixed scalar compositor.
Source: blueprint thm-coef-finite-hom, successive coefficient paragraph; Stacks 07A4, 0D6D
(blueprint: lem-coef-etale-scalar-tensor-composition).

Proof: choose flat-term K-flat complexes P,Q representing U,V. Ordinary scalar extension
preserves their flatness and K-flatness, including for nonflat ring maps. The compositor
is the adjunction mate of the actual restriction compositor; its normalized representative
is ordinary reassociation (x tensor b) tensor c mapped to x tensor psi(b)c. The normalized
tensorator sends (x tensor y) tensor b to (x tensor b) tensor (y tensor 1). Both routes in
the square send ((x tensor y) tensor b) tensor c to
(x tensor psi(b)c) tensor (y tensor 1). These are balanced maps on sheafified tensors,
and their degreewise equalities extend through the direct sums of the signed total
complex. Paste this ordinary square with the all-complex tensor normalization equations
and the scalar-compositor representative equation. All representative maps are
isomorphisms on these models, so cancellation proves the square there. Naturality along
the representing isomorphisms gives the equation for arbitrary unbounded U,V. -/
theorem scalarTensor_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u}) (U V : DerivedCategoryModule A T) :
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) T).obj U).obj V) ≫
      (tensorIso χ T).hom.app (U, V) =
    (scalarExtension ψ T).map ((tensorIso φ T).hom.app (U, V)) ≫
      (tensorIso ψ T).hom.app ((scalarExtension φ T).obj U, (scalarExtension φ T).obj V) ≫
      (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} C) T)).map
        (Prod.mkHom
          ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app U)
          ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app V)) := by
  sorry

end AlgebraicGeometry.Etale.ExceptionalCoefficients
