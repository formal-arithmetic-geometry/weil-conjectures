/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenScalarTensorData
import WeilConjectures.SixFunctors.OpenScalarCanonicalTransport

/-! The coefficient-composition field for scalar pullback coherence.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6 and 0D6D.
(blueprint: lem-sp-open-scalar-coefficient-coherence-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- Scalar pullback commutes with a chosen pair of coefficient extensions.
Source: Stacks 07A4, 07A6 and 0D6D.
(blueprint: lem-sp-open-scalar-coefficient-coherence-composition).

Proof: `scalarComp_transport` rewrites the compositor `scalarComp` at `X` and at `U` as the
canonical compositor transported through the presentation isomorphisms; the transported
equation is `scalar_pullback_coefficient_canonical_transport`, which reduces it to the
direct-image scalar cocycle by naturality. This is the composition field of the parent
structure.
-/
theorem scalar_pullback_coefficient_composition (m : Models.{u}) :
    ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
      {U X : Scheme.{u}} (j : U ⟶ X)
      (Q : proEtaleDerivedCategory X A),
      (scalar m ψ U).map ((lambda m φ j).inv.app Q) ≫
        (lambda m ψ j).inv.app ((scalar m φ X).obj Q) ≫
        (constantPullback (A := C) j).map ((scalarComp m φ ψ X).hom.app Q) =
      (scalarComp m φ ψ U).hom.app ((constantPullback (A := A) j).obj Q) ≫
        (lambda m (ψ.comp φ) j).inv.app Q := by
  intro A B C _ _ _ _ _ _ φ ψ U X j Q
  rw [scalarComp_transport m φ ψ X, scalarComp_transport m φ ψ U]
  exact scalar_pullback_coefficient_canonical_transport m φ ψ j Q

end AlgebraicGeometry.ProEtale.OpenScalarTensor
