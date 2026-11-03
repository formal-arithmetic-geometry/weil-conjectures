/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives

/-! # Finite-coefficient internal-Hom site descent

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, final site-comparison sentence
(blueprint: def-coef-finite-hom-site-descent-models).
The helper definitions specialize the existing scalar adjunction and its derived
pure-tensor comparison. All categories are ordinary, uncompleted derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.FiniteHomSiteDescent

/-- Countable coproducts are supplied by the existing colimits of module sheaves.
Source: Stacks 06YY (blueprint: def-coef-finite-hom-site-descent-models). -/
instance scalarCountableCoproducts
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (R : Type (u + 1)) [CommRing R] :
    HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0}
    (Sheaf J (ModuleCat.{u + 1} R))).has_colimits_of_shape _⟩

section Scalar
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Scalar tensor preserves K-flat quasi-isomorphisms, by restriction to the original
ring and the ordinary tensor identity. Source: Stacks 06YY
(blueprint: def-coef-finite-hom-site-descent-models). -/
instance scalarPreservesKFlat : (Sheaf.extendScalars J φ).PreservesKFlatQuasiIso := by
  let := φ.toAlgebra
  constructor
  intro P Q hP hQ f hf
  exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
    (Sheaf.extendScalarsCompRestrictScalarsIso J A B) f hP hQ

/-- The unique adjunction-compatible identification of the recorded coefficient
extension with the K-flat total derived scalar functor. Source: Stacks 06YY
(blueprint: def-coef-finite-hom-site-descent-models). -/
def scalarResolutionIso :
    (Sheaf.extendScalars J φ).leftDerivedFunctor ≅
      Sheaf.fixedCoefficientDerivedScalarExtension J φ :=
  letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint J φ
  ((Sheaf.extendScalarsAdjunction J φ).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars J φ).rightDerivedFunctorIsoMapDerivedCategory).leftAdjointUniq
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ))

/-- The counit comparison with ordinary scalar extension on a homotopy representative.
It is the K-flat derived counit transported through the specified scalar adjoint.
Source: Stacks 06YY (blueprint: def-coef-finite-hom-site-descent-models). -/
def scalarRepresentativeComparison
    (P : HomotopyCategory (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj (DerivedCategory.Qh.obj P) ⟶
      DerivedCategory.Qh.obj (((Sheaf.extendScalars J φ).mapHomotopyCategory (.up ℤ)).obj P) :=
  (scalarResolutionIso J φ).inv.app (DerivedCategory.Qh.obj P) ≫
    (Sheaf.extendScalars J φ).leftDerivedFunctorCounit.app P

/-- Naturality of the fixed scalar representative comparison on homotopy morphisms.
Source: Stacks 06YY (blueprint: def-coef-finite-hom-site-descent-models).
Proof: naturality of the inverse resolution isomorphism followed by naturality
of the left-derived counit. -/
theorem scalarRepresentativeComparison_naturality
    {P Q : HomotopyCategory (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)} (f : P ⟶ Q) :
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ).map (DerivedCategory.Qh.map f) ≫
        scalarRepresentativeComparison J φ Q =
      scalarRepresentativeComparison J φ P ≫
        DerivedCategory.Qh.map
          (((Sheaf.extendScalars J φ).mapHomotopyCategory (.up ℤ)).map f) := by
  simp only [scalarRepresentativeComparison, Category.assoc]
  rw [(scalarResolutionIso J φ).inv.naturality_assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ (scalarResolutionIso J φ).inv.app (DerivedCategory.Qh.obj P) ≫ z)
      ((Sheaf.extendScalars J φ).leftDerivedFunctorCounit.naturality f)

/-- The representative comparison is invertible on K-flat inputs.
Source: Stacks 06YY (blueprint: def-coef-finite-hom-site-descent-models).
Proof: the K-flat derived counit and the resolution isomorphism are invertible. -/
theorem scalarRepresentativeComparison_isIso
    (P : HomotopyCategory (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))
    (hP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (scalarRepresentativeComparison J φ P) := by
  have := (Sheaf.extendScalars J φ).isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP
  unfold scalarRepresentativeComparison
  infer_instance

/-- The canonical scalar tensorator, transported through the unique scalar-adjunction
identification. Source: Stacks 07A4 (blueprint: def-coef-finite-hom-site-descent-models). -/
def scalarTensor (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj (K ⊗ M) ≅
      (Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj K ⊗
        (Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj M :=
  (scalarResolutionIso J φ).symm.app (K ⊗ M) ≪≫
    ((Sheaf.extendScalars J φ).leftDerivedTensorIso K).app M ≪≫
    tensorIso ((scalarResolutionIso J φ).app K) ((scalarResolutionIso J φ).app M)

/-- The specified coefficient-Hom comparison is the closed transpose of scalar
extension of evaluation, with the canonical tensorator. We use the symmetry-equivalent
convention with K first, as in the existing site evaluation comparison.
Source: thm-coef-finite-hom.proof.md, first paragraph; Stacks 08J9
(blueprint: def-coef-finite-hom-site-descent-models). -/
def scalarHom (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj ((ihom K).obj M) ⟶
      (ihom ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj K)).obj
        ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj M) :=
  MonoidalClosed.curry
    ((scalarTensor J φ K ((ihom K).obj M)).inv ≫
      (Sheaf.fixedCoefficientDerivedScalarExtension J φ).map ((ihom.ev K).app M))

/-- The evaluation, tensor-Hom transpose and composition identities for the specified
coefficient comparison on a full domain. Source: thm-coef-finite-hom.proof.md,
penultimate sentence (blueprint: def-coef-finite-hom-site-descent-models). -/
def EvaluationLaw
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) : Prop :=
  (∀ K M, P K → P M →
    ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj K ◁ scalarHom J φ K M) ≫
      (ihom.ev ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj K)).app
        ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj M) =
    (scalarTensor J φ K ((ihom K).obj M)).inv ≫
      (Sheaf.fixedCoefficientDerivedScalarExtension J φ).map ((ihom.ev K).app M))

/-- Tensor-Hom transposes for the specified scalar comparison, with arbitrary tensor
argument. Source: thm-coef-finite-hom.proof.md
(blueprint: def-coef-finite-hom-site-descent-models). -/
def TransposeLaw
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) : Prop :=
  (∀ K M, P K → P M →
    ∀ (T : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) (f : K ⊗ T ⟶ M),
      (Sheaf.fixedCoefficientDerivedScalarExtension J φ).map (MonoidalClosed.curry f) ≫
        scalarHom J φ K M =
      MonoidalClosed.curry ((scalarTensor J φ K T).inv ≫
        (Sheaf.fixedCoefficientDerivedScalarExtension J φ).map f))

/-- Internal-Hom composition identity for the scalar comparison.
Source: thm-coef-finite-hom.proof.md
(blueprint: def-coef-finite-hom-site-descent-models). -/
def CompositionLaw
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) : Prop :=
  (∀ K L M, P K → P L → P M →
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ).map (MonoidalClosed.comp K L M) ≫
      scalarHom J φ K M =
    (scalarTensor J φ ((ihom K).obj L) ((ihom L).obj M)).hom ≫
      (scalarHom J φ K L ⊗ₘ scalarHom J φ L M) ≫
      MonoidalClosed.comp
        ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj K)
        ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj L)
        ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj M))

/-- Canonical successive scalar associator, obtained from the restriction adjunctions.
Source: Stacks 07A4 (blueprint: def-coef-finite-hom-site-descent-models). -/
def scalarAssoc {R : Type (u + 1)} [CommRing R] (ψ : B →+* R) :
    Sheaf.fixedCoefficientDerivedScalarExtension J φ ⋙
      Sheaf.fixedCoefficientDerivedScalarExtension J ψ ≅
        Sheaf.fixedCoefficientDerivedScalarExtension J (ψ.comp φ) :=
  FiniteCoefficientOrdinary.scalarComposition J φ ψ

/-- The successive-change identity, including arbitrary unital maps and identity maps,
with the canonical adjunction associator. Source: thm-coef-finite-hom.proof.md,
penultimate sentence (blueprint: def-coef-finite-hom-site-descent-models). -/
def SuccessiveLaw {R : Type (u + 1)} [CommRing R] (ψ : B →+* R)
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) : Prop :=
  ∀ K M, P K → P M →
    (Sheaf.fixedCoefficientDerivedScalarExtension J ψ).map (scalarHom J φ K M) ≫
      scalarHom J ψ
        ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj K)
        ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj M) ≫
      (MonoidalClosed.internalHom.map ((scalarAssoc J φ ψ).inv.app K).op).app
        ((Sheaf.fixedCoefficientDerivedScalarExtension J ψ).obj
          ((Sheaf.fixedCoefficientDerivedScalarExtension J φ).obj M)) ≫
      (ihom ((Sheaf.fixedCoefficientDerivedScalarExtension J (ψ.comp φ)).obj K)).map
        ((scalarAssoc J φ ψ).hom.app M) =
    (scalarAssoc J φ ψ).hom.app ((ihom K).obj M) ≫ scalarHom J (ψ.comp φ) K M
end Scalar

/-- The strong monoidal structure with cotensorator exactly `scalarTensor`.
It is transported from K-flat derived scalar extension, using the already specified
adjunction-compatible resolution isomorphism. No new comparison is chosen.
Source: Stacks 07A4 (blueprint: def-coef-finite-hom-site-descent-models). -/
@[irreducible]
noncomputable def scalarMonoidal
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ).Monoidal := by
  letI := (Sheaf.extendScalars J φ).leftDerivedFunctorMonoidal
  exact Functor.Monoidal.transport (scalarResolutionIso J φ)

/-- The fixed-coefficient ordinary derived site inverse image.
Source: Stacks 03EL (blueprint: def-coef-finite-hom-site-descent-models). -/
abbrev sitePullback (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory

/-- Restriction of scalars commutes with site inverse image. Its canonical
identification is conjugate to the sectionwise identity between coextension followed
by site restriction and site restriction followed by coextension.
Source: Stacks 03D2 and the node's Step 2
(blueprint: def-coef-finite-hom-site-descent-models). -/
def comparisonRestrictIso (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X ⋙
      Sheaf.restrictScalars (ProEt.topology X) φ ≅
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X :=
  ((conjugateIsoEquiv
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).comp
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ))
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X))).symm (Iso.refl _)).symm

/-- Exact derived transport of the canonical restriction/site comparison.
Source: Stacks 03D2, 06YY; exact comparison pullback, Step 2
(blueprint: def-coef-finite-hom-site-descent-models). -/
def derivedComparisonRestrictIso (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    sitePullback X B ⋙ Sheaf.derivedRestrictScalars (ProEt.topology X) φ ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙ sitePullback X A :=
  (Functor.mapDerivedCategoryCompIso
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (Sheaf.restrictScalars (ProEt.topology X) φ)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonRestrictIso X φ) ≪≫
    Functor.mapDerivedCategoryCompIso (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)

/-- The scalar/site natural transformation is the left mate of the specified derived
restriction comparison, with the actual scalar adjunctions. No map is chosen by existence.
Source: Stacks 07A4; canonical ringed pullback composition, Step 2
(blueprint: def-coef-finite-hom-site-descent-models). -/
def scalarSiteMate (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    sitePullback X A ⋙ Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ ⋙ sitePullback X B :=
  ((mateEquiv (G := sitePullback X A) (H := sitePullback X B)
    (FiniteCoefficientOrdinary.scalarAdjunction X.smallEtaleTopology φ)
    (FiniteCoefficientOrdinary.scalarAdjunction (ProEt.topology X) φ)).symm
      (TwoSquare.mk _ _ _ _ (derivedComparisonRestrictIso X φ).inv)).natTrans

/-- The canonical scalar/site mate is invertible for the node's finite coefficient rings.
Source: Stacks 07A4 and the node's Step 2; exact comparison pullback and canonical
ringed-derived monoidal comparisons (blueprint: def-coef-finite-hom-site-descent-models).

Proof: inverse image identifies constant coefficient rings and is exact. On ordinary
module sheaves its scalar-extension mate is the sectionwise canonical tensor/pullback
identification. One can check its mate under the two geometric adjunctions: restriction
of the site commutes sectionwise with scalar restriction; the coextension unit and
counit triangle makes the twice-transposed comparison that identity. Thus the ordinary
scalar mate is invertible. Compute derived scalar extension on K-flat resolutions.
Comparison inverse image preserves flat objects and commutes with the exact localization;
its derived tensor comparison identifies the derived mate with localization of that
ordinary scalar mate on these resolutions. Hence each derived component is invertible.
The uniqueness of scalar adjoints identifies these computed adjunctions with the fixed
ones used in scalarSiteMate, preserving the mate. This proves the stated IsIso for
that particular natural transformation, not merely existence of some isomorphism. -/
theorem scalarSiteMate_isIso (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    IsIso (scalarSiteMate X φ) := by
  change IsIso (CoefficientScalarRepresentatives.comparisonMap X φ)
  infer_instance

/-- The specified h_T is the inverse of the constructed canonical scalar/site mate.
Only its invertibility proof is postponed; its morphism was constructed explicitly.
Source: Stacks 07A4 and the node's Step 2
(blueprint: def-coef-finite-hom-site-descent-models). -/
def scalarSiteIso (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ ⋙ sitePullback X B ≅
      sitePullback X A ⋙ Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ :=
  letI := scalarSiteMate_isIso X φ
  (asIso (scalarSiteMate X φ)).symm

/-- The existing intrinsic etale finite-Tor constructible domain.
Source: blueprint final site-comparison sentence
(blueprint: def-coef-finite-hom-site-descent-models). -/
abbrev etaleCtf (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [Finite R] :=
  ProEtale.exceptionalTransportEtaleObjects R X

/-- The existing intrinsic pro-etale finite-Tor constructible domain.
Source: blueprint final site-comparison sentence
(blueprint: def-coef-finite-hom-site-descent-models). -/
abbrev proetaleCtf (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [Finite R] :=
  ProEtale.exceptionalTransportProEtaleObjects R X

/-- Identification of the two full ctf domains, including fullness, faithfulness,
essential surjectivity, and preservation and reflection of every Tor interval for
bounded constructible etale witnesses. Source: the item's domain assertion
(blueprint: def-coef-finite-hom-site-descent-models). -/
def SiteDomain (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [Finite R] : Prop :=
  (∀ K, etaleCtf X R K ↔ proetaleCtf X R ((sitePullback X R).obj K)) ∧
  (∀ K L, etaleCtf X R K → etaleCtf X R L →
    Function.Bijective ((sitePullback X R).map :
      (K ⟶ L) → ((sitePullback X R).obj K ⟶ (sitePullback X R).obj L))) ∧
  (∀ P, proetaleCtf X R P → ∃ K, etaleCtf X R K ∧
    Nonempty ((sitePullback X R).obj K ≅ P)) ∧
  (∀ K, Etale.DerivedCategory.isBoundedConstructible R X K → ∀ a b : ℤ,
    Etale.DerivedCategory.hasTorAmplitudeIn R X a b K ↔
      _root_.DerivedCategory.torAmplitudeIn
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) a b ((sitePullback X R).obj K))

/-- The typed square relating the two specified evaluation-transpose coefficient maps.
The contravariant factor is h_K inverse. Source: the item's displayed equation
(blueprint: def-coef-finite-hom-site-descent-models). -/
def ComparisonSquare (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (K M : Etale.DerivedCategoryModule A X) : Prop :=
  (scalarSiteIso X φ).hom.app ((ihom K).obj M) ≫
    (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).map
      (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M) ≫
    scalarHom (ProEt.topology X) φ ((sitePullback X A).obj K) ((sitePullback X A).obj M) =
  (sitePullback X B).map (scalarHom X.smallEtaleTopology φ K M) ≫
    ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} B) X
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj K)
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) ≫
    (MonoidalClosed.internalHom.map ((scalarSiteIso X φ).inv.app K).op).app
      ((sitePullback X B).obj
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M)) ≫
    (ihom ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj
      ((sitePullback X A).obj K))).map ((scalarSiteIso X φ).hom.app M)

end AlgebraicGeometry.FiniteHomSiteDescent
