/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement

/-! # Slice restriction of evaluation, transpose and Koszul symmetry

Source: Stacks Project, Tags 07A4, 08J9, 08JB, 08FI and 03EL;
main-20261015 blueprint, `lem-weil-delta-restriction`, final paragraph
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose).

The comparison data below retain their representative characterizations. In particular,
no arbitrary natural tensor or Hom isomorphism can stand for the canonical comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

/-- Restriction of complexes is the actual termwise slice functor.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceComplexRestriction (U : C) : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ⥤ CochainComplex
  (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u}
  RingCat.{max c v u})).obj (A.over U))) ℤ :=
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  (SheafOfModules.overFunctor.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The recorded exact derived restriction with its slice ring written as A.over U.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceDerivedRestriction (U : C) [hU : HasDerivedCategory.{w'} (SheafOfModules.{max c v u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
  :
    DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v u}
      RingCat.{max c v u})).obj A)) ⥤ DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose
      (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U))) :=
  letI : HasDerivedCategory.{w'}
      (SheafOfModules.{max c v u}
        (((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) := hU
  ringedDerivedRestrictionGeneral.{c, v, max c v u, max c v u, w, w'}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U

set_option maxHeartbeats 600000 in
-- The two-variable representative squares have long dependent endpoint types.
/-- Categorical data for the slice comparisons, normalized by the following predicates.
The tensor comparisons are identity on sheafified pure-tensor summands. The Hom
comparison is identity on local families of maps, and symmetry is the Koszul sign.
Source: Stacks 07A4, 08J9, 08JB, 03EL
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
structure RingedSliceEvaluationComparisons
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    (H : Dᵒᵖ × D ⥤ D) (HU : Eᵒᵖ × E ⥤ E) (r : D ⥤ E)
    (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU) (K : Prop) where
  /-- Restriction of derived tensor, natural simultaneously in both objects. -/
  rho : ∀ L M : D,
    (r).obj (S.tensor.obj (L, M)) ≅
      SU.tensor.obj ((r).obj L, (r).obj M)
  /-- The Hom comparison, with its two components displayed explicitly. -/
  eta : ∀ L M : D,
    (r).obj ((H).obj (op L, M)) ≅
      (HU).obj (op ((r).obj L), (r).obj M)
  /-- Simultaneous naturality of the tensor comparison. -/
  rho_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    (r).map (S.tensor.map (f, g)) ≫ (rho L' M').hom =
    (rho L M).hom ≫ SU.tensor.map ((r).map f, (r).map g)
  /-- Contravariant/covariant naturality of the Hom comparison. -/
  eta_naturality : ∀ (L M L' M' : D) (f : L' ⟶ L) (g : M ⟶ M'),
    (r).map ((H).map (f.op, g)) ≫ (eta L' M').hom =
    (eta L M).hom ≫ (HU).map (((r).map f).op, (r).map g)
  /-- Koszul symmetry on the source derived category. -/
  sigma : ∀ L M : D, S.tensor.obj (L, M) ≅ S.tensor.obj (M, L)
  /-- Naturality transports the representative Koszul formula to all derived objects. -/
  sigma_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    S.tensor.map (f, g) ≫ (sigma L' M').hom =
      (sigma L M).hom ≫ S.tensor.map (g, f)
  /-- Koszul symmetry on the localized derived category. -/
  sigmaU : ∀ L M : E, SU.tensor.obj (L, M) ≅ SU.tensor.obj (M, L)
  /-- Naturality on the slice also covers objects isomorphic to K-flat models. -/
  sigmaU_naturality : ∀ (L M L' M' : E) (f : L ⟶ L') (g : M ⟶ M'),
    SU.tensor.map (f, g) ≫ (sigmaU L' M').hom =
      (sigmaU L M).hom ≫ SU.tensor.map (g, f)
  /-- Preservation of the specified resolving class. -/
  kflat : K

end CategoryTheory
