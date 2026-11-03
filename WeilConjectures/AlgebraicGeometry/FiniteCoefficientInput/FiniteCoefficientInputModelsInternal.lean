/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel

/-! # Finite coefficient input models in internal modules

Source: current blueprint, det-sp-reduction-exceptional, proof paragraph Charts,
finite coefficient extension on bounded flat inputs.
(blueprint: lem-sp-finite-coefficient-input-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.FiniteCoefficientInput

open ProEtale ProEtale.FiniteDiscreteOrdinary

variable {A B : Type u} [CommRing A] [CommRing B]
  [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
  [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]

/-- Postcomposition by the given coefficient homomorphism, on condensed ring sections.
Source: current blueprint, Charts, induced finite coefficient map
(blueprint: lem-sp-finite-coefficient-input-models). -/
def pointRingMap (φ : A →+* B) :
    Profinite.continuousCoefficientRingSheaf A ⟶
      Profinite.continuousCoefficientRingSheaf B :=
  Profinite.continuousMapRingSheafMapOfUniverse.{u, u} φ continuous_of_discreteTopology

/-- The same specified map as a morphism of internal condensed rings.
Source: current blueprint, Charts, induced finite coefficient map
(blueprint: lem-sp-finite-coefficient-input-models). -/
def pointMap (φ : A →+* B) : coefficient A ⟶ coefficient B :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (pointRingMap φ)

/-- Bundle the actual postcomposition map, retaining its commutative ring structure.
Source: current blueprint, Charts, induced finite coefficient map
(blueprint: lem-sp-finite-coefficient-input-models). -/
def coefficientHom (φ : A →+* B) :
    (⟨coefficient A⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨coefficient B⟩ :=
  CommMon.homMk (Mon.Hom.mk (pointMap φ))

/-- The specified section-action equivalence, followed by restriction to constant scalars.
Source: current blueprint, Charts, finite discrete coefficient identification
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev heart {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {X : Scheme.{u}} (E : Encoding R X) := E.ordinary.trans E.fixed

/-- The exact ordinary site comparison, in the fixed-coefficient universe convention.
Source: current blueprint, Charts (blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev ordinaryPull (R : Type u) [CommRing R] (X : Scheme.{u}) :=
  comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) X

/-- The internal comparison inverse image is the exact ordinary comparison followed
by the inverse of the specified section-action equivalence.
Source: current blueprint, Charts, etale-origin input
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev site {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {X : Scheme.{u}} (E : Encoding R X) :=
  ordinaryPull R X ⋙ (heart E).inverse

/-- Internal scalar extension is the published balanced tensor with the target ring,
which acts on its own factor. Symmetry exchanges its displayed first-factor convention.
Source: current blueprint, Charts, extension of finite coefficients
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev extension (φ : A →+* B) (X : Scheme.{u}) :=
  Mod.extendScalars (coefficientMap (pointMap φ) X)

/-- The actual unbounded left derived internal scalar extension.
Source: current blueprint, Charts, extension of finite coefficients
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev derivedExtension (φ : A →+* B) (X : Scheme.{u}) :=
  CondensedRing.scalarSixChange (coefficientHom φ) X

/-- The section-normalized scalar comparison on the heart is the unique comparison
of composite left adjoints conjugate to the identity-on-sections restriction square.
Source: current blueprint, Charts, pure-tensor coefficient comparison
(blueprint: lem-sp-finite-coefficient-input-models). -/
def heartExtension {X : Scheme.{u}} {EA : Encoding A X} {EB : Encoding B X}
    {φ : A →+* B}
    (s : FiniteInputScalarCoordinates φ (coefficientHom φ) X EA EB) :
    extension φ X ⋙ (heart EB).functor ≅
      (heart EA).functor ⋙
        CoefficientScalarRepresentatives.ordinaryExtension (Scheme.ProEt.topology X)
        (RingHom.ulift.{u + 1, u + 1} φ) :=
  let V := Mod.comap (coefficientMap (pointMap φ) X)
  let W := Sheaf.restrictScalars (Scheme.ProEt.topology X)
    (RingHom.ulift.{u + 1, u + 1} φ)
  let k : ((heart EB).inverse ⋙ V) ⋙ (heart EA).functor ≅ W :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (heart EB).inverse s.restriction ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (heart EB).counitIso W ≪≫ Functor.leftUnitor W
  let r := Iso.isoCompInverse (H := heart EA) k
  ((Mod.extendRestrictAdjunction (coefficientMap (pointMap φ) X)).comp
    (heart EB).toAdjunction).leftAdjointUniq
      (((heart EA).toAdjunction.comp
        (CoefficientScalarRepresentatives.ordinaryAdjunction (Scheme.ProEt.topology X)
        (RingHom.ulift.{u + 1, u + 1} φ))).ofNatIsoRight
          r.symm)

/-- The ordinary tensor/site comparison, conjugate to the composite restriction identity.
Source: Stacks 03D2, 03EK and 03EL; current blueprint, Charts
(blueprint: lem-sp-finite-coefficient-input-models). -/
def ordinaryHeartComparison (X : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    CoefficientScalarRepresentatives.ordinaryExtension X.smallEtaleTopology φ ⋙
        comparisonUpperStar (ModuleCat.{u + 1} S) X ≅
      comparisonUpperStar (ModuleCat.{u + 1} R) X ⋙
        CoefficientScalarRepresentatives.ordinaryExtension (Scheme.ProEt.topology X) φ :=
  (conjugateIsoEquiv
    ((comparisonAdjunction (ModuleCat.{u + 1} R) X).comp
      (CoefficientScalarRepresentatives.ordinaryAdjunction (Scheme.ProEt.topology X) φ))
    ((CoefficientScalarRepresentatives.ordinaryAdjunction X.smallEtaleTopology φ).comp
      (comparisonAdjunction (ModuleCat.{u + 1} S) X))).symm (Iso.refl _)

/-- The termwise internal comparison, specified on each sheaf before passing to complexes.
Source: current blueprint, Charts, canonical tensor/site comparison
(blueprint: lem-sp-finite-coefficient-input-models). -/
def heartComparison {X : Scheme.{u}} {EA : Encoding A X} {EB : Encoding B X}
    {φ : A →+* B}
    (s : FiniteInputScalarCoordinates φ (coefficientHom φ) X EA EB)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (extension φ X).obj ((site EA).obj M) ≅
      (site EB).obj ((CoefficientScalarRepresentatives.ordinaryExtension X.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1} φ)).obj M) :=
  (heart EB).unitIso.app _ ≪≫ (heart EB).inverse.mapIso
    ((heartExtension s).app _ ≪≫
      (CoefficientScalarRepresentatives.ordinaryExtension (Scheme.ProEt.topology X)
        (RingHom.ulift.{u + 1, u + 1} φ)).mapIso
        ((heart EA).counitIso.app _) ≪≫
      (ordinaryHeartComparison X
        (RingHom.ulift.{u + 1, u + 1} φ)).symm.app M)

/-- Canonical internal scalar representative, the transpose of the ordinary scalar unit.
Source: current blueprint, Charts, K-flat computation of internal extension
(blueprint: lem-sp-finite-coefficient-input-models). -/
def extensionRepresentative (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Internal A X) ℤ) :
    (derivedExtension φ X).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((extension φ X).mapHomologicalComplex (.up ℤ)).obj P) :=
  let F := extension φ X
  let R := Mod.comap (coefficientMap (pointMap φ) X)
  let adj := Mod.extendRestrictAdjunction (coefficientMap (pointMap φ) X)
  let ad := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (pointMap φ) X)
  (ad.homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).inv.app P) ≫
      R.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P))

/-- The ordinary comparison complex, in the published fixed-scalar presentation.
Source: current blueprint, Charts, ordinary-coordinate input
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev ordinarySiteComplex (R : Type u) [CommRing R] (X : Scheme.{u}) :=
  (ordinaryPull R X).mapHomologicalComplex (.up ℤ)

/-- The ordinary scalar tensor on pro-etale complexes, with its specified target action.
Source: current blueprint, Charts, ordinary-coordinate input
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev ordinaryExtensionComplex (φ : A →+* B) (X : Scheme.{u}) :=
  (CoefficientScalarRepresentatives.ordinaryExtension (Scheme.ProEt.topology X)
        (RingHom.ulift.{u + 1, u + 1} φ)).mapHomologicalComplex (.up ℤ)

end AlgebraicGeometry.FiniteCoefficientInput
