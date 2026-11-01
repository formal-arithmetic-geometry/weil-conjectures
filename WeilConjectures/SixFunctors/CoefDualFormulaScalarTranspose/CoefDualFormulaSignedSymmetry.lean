/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import all WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierSignedCalculus
import all WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierSignedKFlat
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # The uniquely natural normalized signed symmetry -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

/-- The naturality required of the normalized signed symmetry.
Source: the native braiding and K-flat localization
(blueprint: def-coef-dual-formula-signed-symmetry). -/
def SignedNatural (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (s : IntegralVerdier.SignedSymmetry X R a) : Prop :=
  ∀ (K L K' L' : IntegralHom.Derived.{u, u} X R) (f : K ⟶ K') (g : L ⟶ L'),
    a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
      (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f)

private def swapNat (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (s : IntegralVerdier.SignedSymmetry X R a) (hs : SignedNatural X R a s) :
    a.tensor ⟶ CategoryTheory.Prod.swap _ _ ⋙ a.tensor where
  app Z := (s.swap Z.1 Z.2).hom
  naturality _ _ f := by
    rcases f with ⟨f, g⟩
    exact hs _ _ _ _ f g

/-- The representative Koszul swap has exactly one natural extension.
Source: Stacks 06YL and 08J9, K-flat localization
(blueprint: def-coef-dual-formula-signed-symmetry).
Proof: transport the native braiding along the unique normalized comparison to
obtain a natural signed symmetry. Two such symmetries have equal components on
literal K-flat pairs by the homogeneous tensor formula. Full faithfulness of
restriction along the product K-flat localization identifies their natural
transformations, hence all their swap isomorphisms. Proof irrelevance identifies
the remaining representative fields. -/
theorem naturalSignedSymmetry_existsUnique (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) :
    ∃! s : IntegralVerdier.SignedSymmetry X R a, SignedNatural X R a s := by
  obtain ⟨s, hs⟩ := IntegralVerdier.presentation_symmetry X R a
  refine ⟨s, hs, ?_⟩
  intro t ht
  let : HasDerivedCategory.{u + 2}
      (RingedTensorModules.{u + 1, u, u} (ProEt.topology X) R) :=
    HasDerivedCategory.standard _
  let q : (IntegralHom.flat.{u, u} X R).FullSubcategory ⥤
      IntegralHom.Derived.{u, u} X R :=
    coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (IntegralHom.Modules.{u, u} X R) (.up ℤ)).inverseImage
    (coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R)
  have : q.IsLocalization W :=
    RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2} (ProEt.topology X) R
  let FF := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (W.prod W)
    (IntegralHom.Derived.{u, u} X R)
  have hn : swapNat X R a t ht = swapNat X R a s hs := by
    apply FF.map_injective
    ext Z
    exact RationalVerdier.signed_swap_eq X R a t s Z.1.obj Z.2.obj
      Z.1.property Z.2.property
  have he (K L : IntegralHom.Derived.{u, u} X R) : t.swap K L = s.swap K L := by
    apply Iso.ext
    exact congrArg (fun z ↦ z.app (K, L)) hn
  cases t with
  | mk ts tr =>
    cases s with
    | mk ss sr =>
      have h : ts = ss := funext fun K ↦ funext fun L ↦ he K L
      cases h
      rfl

/-- The natural signed symmetry, determined uniquely by its representative values.
Source: Stacks 06YL, 08J9
(blueprint: def-coef-dual-formula-signed-symmetry). -/
def naturalSignedSymmetry (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) :=
  (naturalSignedSymmetry_existsUnique X R a).exists.choose

/-- Interpret a representative-normalized family by its uniquely natural extension.
Source: Stacks 06YL, 08J9
(blueprint: def-coef-dual-formula-signed-symmetry). -/
def normalizedSignedSymmetry (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (_s : IntegralVerdier.SignedSymmetry X R a) := naturalSignedSymmetry X R a

end WeilConjectures.CoefDualFormulaScalarTranspose
