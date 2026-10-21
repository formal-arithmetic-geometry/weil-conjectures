/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P9
-/
module

public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.OrdinaryKunnethMap
import Sheaf.AlgebraicGeometry.SupportedProductForgetSupports
import Sheaf.AlgebraicGeometry.SupportSiteComparison

/-! # Full-support normalization of the exterior product

Source: blueprint `def-pur-supported-exterior-product`, full-support specialization.
(blueprint: lem-pur-supported-full-support-product).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] HomologicalComplex₂.total
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

private theorem iso_complement_eq {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIso i] :
    i.openComplement = ((𝟙 X) : X ⟶ X).openComplement := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_openComplement, range_eq_univ]

private theorem full_forget_isIso (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsIso i]
    (K : DerivedCategoryModule A X) :
    IsIso ((Functor.rightDerivedFunctorNatTrans
      (supportedEtaleSectionsι A X i.openComplement)).app K) := by
  rw [iso_complement_eq i]
  have := (ProEtale.fullSupportForget_isIso A X).1
  exact inferInstance

/-- For full closed supports the supported exterior product is invertible whenever the
canonical ordinary exterior product is invertible.
Source: blueprint `def-pur-supported-exterior-product`, full-support specialization, and
`lem-pur-kunneth-supported`, proof paragraph 1.
(blueprint: lem-pur-supported-full-support-product).

Proof: the complement of an isomorphism has empty underlying set, just as for
identity support. Hence its forgetful map is the identity-support forgetful map,
which is an isomorphism by fullSupportForget_isIso. Apply this to both factors and
the product immersion, which is again an isomorphism. The equation
supportedExteriorProduct_forget identifies the supported product followed by its
forgetful isomorphism with the tensor of the two source forgetful isomorphisms
followed by the given ordinary map. The latter composite is invertible. Cancel
the target forgetful isomorphism to obtain invertibility of the actual pairing.
The same calculation includes empty schemes and arbitrary unbounded complexes.
-/
theorem isIso_supportedExteriorProduct_of_fullSupport
    (A : Type (u + 1)) [CommRing A] {S X Y Z W : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsIso i] [IsIso j]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y)
    (h : IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A)
      (pullback.fst f g) (pullback.snd f g) K L)) :
    IsIso (supportedExteriorProduct A f g i j K L) := by
  have : IsIso (supportedProductImmersion f g i j) := by
    unfold supportedProductImmersion
    infer_instance
  have := full_forget_isIso A i K
  have := full_forget_isIso A j L
  have := full_forget_isIso A (supportedProductImmersion f g i j)
    (externalProduct (ModuleCat.{u + 1} A) f g K L)
  have := h
  have hc : IsIso (supportedExteriorProduct A f g i j K L ≫
      (Functor.rightDerivedFunctorNatTrans
        (supportedEtaleSectionsι A (pullback f g)
          (supportedProductImmersion f g i j).openComplement)).app
            (externalProduct (ModuleCat.{u + 1} A) f g K L)) := by
    rw [supportedExteriorProduct_forget A f g i j K L]
    apply IsIso.comp_isIso'
    · infer_instance
    · exact h
  exact IsIso.of_isIso_comp_right _
    ((Functor.rightDerivedFunctorNatTrans
      (supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g i j).openComplement)).app
          (externalProduct (ModuleCat.{u + 1} A) f g K L))

end AlgebraicGeometry.Etale
