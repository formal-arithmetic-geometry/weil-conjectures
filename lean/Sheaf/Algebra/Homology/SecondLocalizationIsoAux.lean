module

public import Sheaf.Algebra.Homology.SecondLocalizationMap

/-! Auxiliary interfaces for the second localization isomorphism.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-iso-aux)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[R] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[R] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

/-- The canonical characterized coefficient map exists before proving it invertible.
Source: Stacks Project, Tag 0DJ8, affine localization identity; Tag 06Y6.
(blueprint: lem-pc-second-localization-iso-aux-hom)

Proof: choose an R-K-flat resolution used by the two model counits.  Flat
extension from B to Bp identifies the homology after extension with the
homology of the extended resolution.  The associator for iterated tensor
products and the counit comparison then give a morphism between the two
cohomology modules.  The comparison is natural in the A-module structure;
the tensor generator formula follows from the adjunction for scalar
extension.  This is exactly the predicate `IsSecondLocalizationMap`.
-/
 theorem exists_secondLocalization_hom
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
    ∃ f : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i),
      IsSecondLocalizationMap R A B Bp D hflat Q L K i f := by
  sorry

/-- A characterized second-localization map is invertible.
Source: Stacks Project, Tag 0DJ8, affine localization identity; Tag 06Y6.
(blueprint: lem-pc-second-localization-iso-aux-isIso)

Proof: use the same flat resolution and comparison as for
`exists_secondLocalization_hom`.  Localization makes every denominator of
B a unit after extension to Bp, hence the comparison is an isomorphism on
the localized homology.  Tensor associativity transports this inverse across
the further extension to D.  The generator formula in
`IsSecondLocalizationMap` identifies the transported map with the chosen
map, by `IsSecondLocalizationMap.ext`; consequently the chosen map is an
isomorphism.
-/
 theorem secondLocalization_hom_isIso
    (T : Submonoid B) [IsLocalization T Bp] (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (f : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i))
    (hf : IsSecondLocalizationMap R A B Bp D hflat Q L K i f) : IsIso f := by
  sorry

end RingTensorCohomology
