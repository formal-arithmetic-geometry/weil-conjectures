/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.SixFunctors.OpenScalarTensorData

/-! # Coefficient coherence of scalar/open comparison 

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6, 0D6D and 0GL1;
sites-modules.tex, Tag 0E8I
(blueprint: lem-sp-open-scalar-coefficient-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- Coefficient coherence of scalar pullback before taking any open adjunct.
Source: Stacks 07A6 and 0D6D
(blueprint: lem-sp-open-scalar-coefficient-coherence). -/
structure ScalarPullbackCoefficientCoherence (m : Models.{u}) where
  composition : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Q : proEtaleDerivedCategory X A),
    (scalar m ψ U).map ((lambda m φ j).inv.app Q) ≫
      (lambda m ψ j).inv.app ((scalar m φ X).obj Q) ≫
      (constantPullback (A := C) j).map ((scalarComp m φ ψ X).hom.app Q) =
    (scalarComp m φ ψ U).hom.app ((constantPullback (A := A) j).obj Q) ≫
      (lambda m (ψ.comp φ) j).inv.app Q
  identity : ∀ (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Q : proEtaleDerivedCategory X A),
    (lambda m (RingHom.id A) j).inv.app Q ≫
      (constantPullback (A := A) j).map ((scalarId m A X).hom.app Q) =
    (scalarId m A U).hom.app ((constantPullback (A := A) j).obj Q)

/-- Scalar pullback commutes with coefficient composition and identities.
This result involves no extension-by-zero functor or beta comparison.
Source: Stacks, sites-cohomology.tex, Tags 07A6 and 0D6D.
(blueprint: lem-sp-open-scalar-coefficient-coherence).

Proof: the right-adjoint square is the identity on the underlying inverse-image
sheaf, with its action restricted by the coefficient map. For a tower, restricting
an action twice is restricting it by the composite; for an identity map it is
the same action. These identities give the coefficient cocycle and identity
for the ordinary restriction/inverse-image comparisons, including their scalar
restriction associators and unitors. Exact localization preserves these diagrams
with precisely the recorded `mapDerivedCategoryCompIso` and identity comparisons.
Take scalar adjunction mates of the resulting diagrams. The pasting laws for
mates identify their scalar compositors with `scalarHomExtensionComp` and their
identity comparison with `scalarHomExtensionId`: both are the conjugates of the
same restriction associator or identity. Naturality of the scalar adjunction
units gives the transported comparison for arbitrary `m`. Finally the constant
sheaf functor's composition and identity laws are the equality transports in
`scalarComp` and `scalarId`, so inserting them yields the two displayed equations.
This is the coefficient composition theorem for derived ringed-topos pullback,
applied to the inverse-image/coefficient square; no open projection formula,
boundedness or coefficient-flatness assumption is involved. -/
theorem scalar_pullback_coefficient_coherence (m : Models.{u}) :
    Nonempty (ScalarPullbackCoefficientCoherence m) := by
  sorry

end AlgebraicGeometry.ProEtale.OpenScalarTensor
