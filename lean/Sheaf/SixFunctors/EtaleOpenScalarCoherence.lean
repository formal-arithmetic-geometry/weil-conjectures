/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.SixFunctors.EtaleOpenTensorDefs

/-! # Normalization and tensor coherence of scalar change across an open immersion

Source: Stacks Tags 0E8I, 03EL, 06YY, and 0E8J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The coefficient part of the open projection formula, with all maps fixed by
adjunction and by their K-flat model normalizations.
Source: Stacks 0E8I, 03EL, 06YY, 0E8J
(blueprint: lem-coef-etale-open-scalar-coherence). -/
structure EtaleOpenScalarComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop where
  q_normalized : OpenScalarExtensionNormalization φ j (openScalarExtension φ j)
  q_unique : ∀ q : derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j,
    OpenScalarExtensionNormalization φ j q → q = openScalarExtension φ j
  r_normalized : OpenScalarRestrictionNormalization φ j (openScalarRestriction φ j)
  r_unique : ∀ r : derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j,
    OpenScalarRestrictionNormalization φ j r → r = openScalarRestriction φ j
  successive_scalar : ∀ {C : Type (u + 1)} [CommRing C] (ψ : B →+* C)
      (P : DerivedCategoryModule A U),
    (scalarExtension ψ X).map ((openScalarExtension φ j).hom.app P) ≫
        (openScalarExtension ψ j).hom.app ((scalarExtension φ U).obj P) ≫
        (derivedExtension (A := C) j).map
          ((ProEtale.pbcFixedScalarExtensionComp U.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).hom.app P) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app ((derivedExtension (A := A) j).obj P) ≫
        (openScalarExtension (ψ.comp φ) j).hom.app P
  mixed_tensor_scalar : ∀ (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X),
    canonicalGammaExact (ModuleCat.{u + 1} B) j
        ((scalarExtension φ U).obj P) ((scalarExtension φ X).obj T) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).map
          ((openScalarExtension φ j).inv.app P)).app ((scalarExtension φ X).obj T) ≫
        (etaleHomTensorComparison X φ ((derivedExtension (A := A) j).obj P) T).hom =
      (derivedExtension (A := B) j).map
          (((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
              ((openScalarRestriction φ j).inv.app T) ≫
            (etaleHomTensorComparison U φ P ((derivedRestriction j).obj T)).hom) ≫
        (openScalarExtension φ j).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj P).obj ((derivedRestriction j).obj T)) ≫
        (scalarExtension φ X).map (canonicalGammaExact (ModuleCat.{u + 1} A) j P T)

/-- Scalar change commutes canonically with open extension and restriction,
with the prescribed K-flat normalizations and coefficient and tensor composition laws.
Source: Stacks, Modules on Sites, Tags 0E8I and 03EL; Cohomology on Sites,
Tags 06YY and 0E8J (blueprint: lem-coef-etale-open-scalar-coherence).

Proof: Apply the ordinary open/scalar adjunctions to the balancing map on tensor
products. Uniqueness of the left adjoint identifies this map with q-zero; the
same argument for inverse image identifies it with r-zero. Apply these maps
in every degree of a complex. Transpose by the scalar adjunctions. The defining
scalar representative transposes to the localized ordinary scalar unit, and the
exact open adjunction units localize the ordinary units. Naturality of the exact
localization factors and their composition coherence therefore give the two
representative equations, in particular for every K-flat complex. Equivalently,
one can first check flat K-flat models and then resolve an arbitrary K-flat
complex by such a model; ordinary scalar extension preserves quasi-isomorphisms
between K-flat complexes, so naturality transports the same equation. On K-flat
complexes the scalar representative maps are invertible. Every derived object
has a flat K-flat resolution, transported through the constant-module
equivalence. Naturality on such a resolution and cancellation of the invertible
representative maps determine each component of q and r, hence prove the two
uniqueness assertions. In a tower A to B to C, both scalar paths act on a local
generator by ((p tensor b) tensor c) mapped to p tensor bc. The chosen scalar
composition isomorphism is the conjugate of the same restriction identity and
therefore has this formula. For the mixed square, use flat K-flat resolutions
of P and T and the uniquely normalized scalar tensor comparison. Both paths
send (p tensor b1) tensor (t tensor b2) to (p tensor t) tensor (b1*b2), followed
by extension by zero. These maps are balanced and natural; sheafification and
the direct-sum totalization preserve the equalities and their Koszul signs.
Local tensor generators generate the sheafified tensor, so the equalities
hold on the models and descend to the unbounded derived categories. No
flatness of B over A or quasi-compactness of the open immersion is used. -/
theorem etaleOpenScalarComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    EtaleOpenScalarComparisons φ j := by sorry

end AlgebraicGeometry.Etale
