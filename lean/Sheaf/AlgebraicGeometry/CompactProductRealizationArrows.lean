/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.ProperSupportCompactMaps
public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness

/-! # Finite site realization arrows

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]

/-- The pro-etale compact sections of the same specified compactification.
Source: blueprint Step 1, pro-etale realization
(blueprint: def-pur-compact-product-realization-arrows). -/
abbrev compactProductProSections {X B : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) :=
  (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ⋙
    (Sheaf.Γ (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)).rightDerivedFunctor

/-- The exact ordinary open-comparison mate, transported termwise to the unbounded
categories. Source: blueprint Step 1, compact-support site comparison
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductOpenSiteIso {X B : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategory ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) c.i) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The finite compact-support site comparison in absolute global-section coordinates:
apply the finite global comparison to the zero extension, then the canonical open mate.
Source: blueprint Step 1, compact-support site comparison
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductGlobalSiteMap [Finite A] {X B : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} A) c.Z).map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
        c.i).mapDerivedCategoryPlusCompatibility.inv.app K) ≫
    ProEtale.supportGlobalComparison A
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj K) ≫
    (Sheaf.Γ (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} A)).rightDerivedFunctor.map
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategory.map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
            c.i).mapDerivedCategoryPlusCompatibility.hom.app K) ≫
        (compactProductOpenSiteIso A c).hom.app K.obj)

/-- Invertibility of the specified finite compact comparison.
Source: blueprint Step 1, finite comparison clause
(blueprint: def-pur-compact-product-realization-arrows).
Proof: both bounded-below inclusion comparisons and the open mate are isomorphisms.
The remaining map is finiteComparisonGlobalSections on the zero-extended object,
conjugated by terminal evaluation, and hence is an isomorphism. -/
@[instance]
theorem compactProductGlobalSiteMap_isIso [Finite A] {X B : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (compactProductGlobalSiteMap A c K) := by
  sorry

/-- Insert the retained witness isomorphism into the compact-support comparison.
Source: blueprint Step 1, specified pro-etale realization
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductWitnessComparison [Finite A] {X B : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (w : Scheme.FixedEtaleOriginWitness X A K) :
    (compactProductSections (ModuleCat.{u + 1} A) c).obj w.complex.obj ≅
      (compactProductProSections A c).obj K.obj :=
  asIso (compactProductGlobalSiteMap A c w.complex) ≪≫
    (compactProductProSections A c).mapIso w.iso

/-- The support comparison with the same retained witness, using the recorded
canonical support-site map and functoriality in its specified isomorphism.
Source: blueprint Step 1, specified pro-etale realization
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductSupportWitness [Finite A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (w : Scheme.FixedEtaleOriginWitness X A K) :=
  ProEtale.supportComparisonUnbounded A i w.complex ≫
    (ProEtale.supportSections i A).rightDerivedFunctor.map w.iso.hom

/-- Canonical transport on the exterior product under the two specified witnesses,
using precisely the tensor/pullback comparison theta of the support-site node.
Source: blueprint Step 1, specified pro-etale realization
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductExteriorWitness [Finite A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (wK : Scheme.FixedEtaleOriginWitness X A K)
    (wL : Scheme.FixedEtaleOriginWitness Y A L) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
      (pullback f g)).mapDerivedCategory.obj
        (externalProduct (ModuleCat.{u + 1} A) f g wK.complex.obj wL.complex.obj) ≅
      ProEtale.externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj :=
  ProEtale.supportExteriorCoefficientIso A f g wK.complex.obj wL.complex.obj ≪≫
    (eqToIso (ProEtale.supportedExternalProduct_eq A f g
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        wK.complex.obj)
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        wL.complex.obj))).symm ≪≫
    ProEtale.supportBifunctorIso (ProEtale.derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.mapIso
        wK.iso)
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.mapIso
        wL.iso) ≪≫
    eqToIso (ProEtale.supportedExternalProduct_eq A f g K.obj L.obj)

/-- The map on the existing pro-etale exterior product induced by two morphisms.
Use the defining tensor-object equality at both endpoints to avoid unfolding the
entire derived monoidal structure when checking its type.
Source: blueprint Step 1, naturality of the exterior product
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductProExternalMap {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (α : K ⟶ K') (β : L ⟶ L') :
    ProEtale.externalProduct (ModuleCat.{u + 1} A) f g K L ⟶
      ProEtale.externalProduct (ModuleCat.{u + 1} A) f g K' L' :=
  eqToHom (ProEtale.supportedExternalProduct_eq A f g K L).symm ≫
    ProEtale.supportedDerivedTensorMap A (pullback f g)
      ((ProEtale.upperStar (ModuleCat.{u + 1} A)
        (pullback.fst f g)).leftDerivedFunctor.map α)
      ((ProEtale.upperStar (ModuleCat.{u + 1} A)
        (pullback.snd f g)).leftDerivedFunctor.map β) ≫
    eqToHom (ProEtale.supportedExternalProduct_eq A f g K' L')

/-- The finite compact exterior product on the specified pro-etale realizations.
All transport is through the canonical finite compact comparison and the specified
witnesses; the output uses the canonical theta, rather than an arbitrary isomorphism.
Source: blueprint Step 1, finite site agreement
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductProMap [Finite A] {B X Y : Scheme.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} (c : Compactification f) (d : Compactification g)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (wK : Scheme.FixedEtaleOriginWitness X A K)
    (wL : Scheme.FixedEtaleOriginWitness Y A L)
    (F : DerivedCategory.Plus (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (eF : F.obj ≅ externalProduct (ModuleCat.{u + 1} A) f g wK.complex.obj wL.complex.obj) :
    (compactProductProSections A c).obj K.obj ⊗ (compactProductProSections A d).obj L.obj ⟶
      (compactProductProSections A (compactProductCompactification c d)).obj
        (ProEtale.externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj) :=
  tensorHom (compactProductWitnessComparison A c K wK).inv
      (compactProductWitnessComparison A d L wL).inv ≫
    compactProductMap (ModuleCat.{u + 1} A) c d wK.complex.obj wL.complex.obj ≫
    (compactProductSections (ModuleCat.{u + 1} A) (compactProductCompactification c d)).map eF.inv ≫
    compactProductGlobalSiteMap A (compactProductCompactification c d) F ≫
    (compactProductProSections A (compactProductCompactification c d)).map
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.map
        eF.hom ≫ (compactProductExteriorWitness A f g K L wK wL).hom)

/-- The canonical retained witness for exact comparison inverse image of a
specified bounded-below etale object.
Source: blueprint Step 1, finite site agreement
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductCanonicalWitness (T : Scheme.{u})
    (G : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Scheme.FixedEtaleOriginWitness T A
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj G) where
  complex := G
  iso := ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
    T).mapDerivedCategoryPlusCompatibility.app G).symm

/-- The canonical identification of the bounded-below comparison product with
the actual external product of the two specified pro-etale realizations.
Source: blueprint Step 1, the comparison theta
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductOutputIso [Finite A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (wK : Scheme.FixedEtaleOriginWitness X A K)
    (wL : Scheme.FixedEtaleOriginWitness Y A L)
    (F : DerivedCategory.Plus (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (eF : F.obj ≅ externalProduct (ModuleCat.{u + 1} A) f g wK.complex.obj wL.complex.obj) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f
    g)).mapDerivedCategoryPlusCompatibility.app F ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.mapIso eF
      ≪≫ compactProductExteriorWitness A f g K L wK wL

/-- The proper-support map on a specified pro-etale realization. Its support
comparison is inverted only with a proof of the finite comparison theorem, never
with an arbitrary chosen map. Source: blueprint Step 1, finite site agreement
(blueprint: def-pur-compact-product-realization-arrows). -/
def compactProductProSupportMap [Finite A] {B X Z : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (w : Scheme.FixedEtaleOriginWitness X A K)
    (h : IsIso (compactProductSupportWitness A i K w)) :=
  @inv _ _ _ _ (compactProductSupportWitness A i K w) h ≫
    compactSupportFromProperSupport A c i w.complex.obj ≫
    (compactProductWitnessComparison A c K w).hom

end AlgebraicGeometry.Etale
