/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients
public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Normalized tensor and scalar comparisons at the finite condensed point

Source: blueprint, sec-six-functors/sk-thm-sf-package/thm-pod-finite-reduction.proof.md,
first paragraph; Stacks Project, Tags 07A4, 07A6 and 0D6D.

## Main statements

* `TensorComparison` records the normalized tensor and unit comparisons.
* `ScalarComparison` records the adjunction-normalized scalar comparison.
* `ComparisonFamily` retains their identity and composition equations.
* `condensed_point_derived_scalar_comparison` asserts existence of this canonical family.

(blueprint: lem-sf-condensed-point-derived-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.FinitePointComparison

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The finite discrete coefficient hypothesis, invariant under presentation of the
reconstructed section ring. Source: finite condensed point normalization
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def IsFiniteCoefficient
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : Finite A),
    Nonempty (B ≅ (constantSheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{u + 1}).obj (CommRingCat.of (ULift.{u + 1} A)))

variable (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})

/-- The ordinary sectionwise module category of the coefficient sheaf.
Source: the ordinary-module convention of the node
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
abbrev Modules := SheafOfModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)

/-- The ordinary ring of final-object sections, canonically the finite coefficient ring.
Source: the finite condensed point calculation
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
abbrev SectionRing := B.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

/-- Exactness of the actual evaluation functor, as supplied by the point-sections theorem.
Source: Stacks 03CW, 0946
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance sections_limits : PreservesFiniteLimits (pointModuleSections k B) :=
  ((point_proEtale_sections_exact.{u, u + 1, u + 1} k).2 B).1

/-- Exactness of the actual evaluation functor, as supplied by the point-sections theorem.
Source: Stacks 03CW, 0946
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance sections_colimits : PreservesFiniteColimits (pointModuleSections k B) :=
  ((point_proEtale_sections_exact.{u, u + 1, u + 1} k).2 B).2.1

/-- The site is small in the already specified coefficient universe.
Source: Stacks 098H (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) pointSmall :
    EssentiallySmall.{u + 1} (Spec (.of k)).ProEt :=
  CategoryTheory.essentiallySmallSelf.{0, u, u + 1} _

/-- Sheafification in the coefficient universe of the small pro-etale site.
Source: Stacks 00W1 (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) pointSheafify : HasSheafify (Scheme.ProEt.topology (Spec (.of k)))
    AddCommGrpCat.{u + 1} := SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

/-- The usual local characterization of sheafification equivalences.
Source: Stacks 00W1 (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) pointLocalEquivalences :
    (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

/-- Mathlib's abelian structure with its coefficient universe specified.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) modulesAbelian : Abelian (Modules k B) :=
  SheafOfModules.instAbelian _

variable [∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
  HasDerivedCategory.{u + 1} (Modules k R)]

/-- The relative K-flat monoidal structure already constructed for ringed sites.
Source: Stacks 07A4
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance derivedMonoidal : MonoidalCategory (DerivedCategory.{u + 1} (Modules k B)) :=
  CategoryTheory.RingedDerivedNative.monoidal.{u + 1, u, 0, u + 1}
    (Scheme.ProEt.topology (Spec (.of k))) B

/-- Its signed symmetry, from the existing K-flat localization.
Source: Stacks 07A4
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance derivedSymmetric : SymmetricCategory (DerivedCategory.{u + 1} (Modules k B)) :=
  CategoryTheory.RingedDerivedNative.symmetric.{u + 1, u, 0, u + 1}
    (Scheme.ProEt.topology (Spec (.of k))) B

/-- The signed braiding on ordinary module derived tensor products.
Source: Stacks 0FPT (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance ordinaryBraiding :
    BraidedCategory (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (SectionRing k B))) :=
  DerivedMonoidal.braidedCategory' DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u + 1} (SectionRing k B)) (.up ℤ))

/-- The native localization comparison for the existing relative derived tensor.
Source: Stacks 06YT (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance localizationLax : (DerivedCategory.Q : CochainComplex (Modules k B) ℤ ⥤
    DerivedCategory.{u + 1} (Modules k B)).LaxMonoidal :=
  RingedDerivedNative.lax.{u + 1, u, 0, u + 1}
    (Scheme.ProEt.topology (Spec (.of k))) B

/-- Exact termwise point sections on the ordinary derived category.
Source: Stacks 0946 and the exact-functor localization convention
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
abbrev sections : DerivedCategory.{u + 1} (Modules k B) ⥤
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} (SectionRing k B)) :=
  (pointModuleSections k B).mapDerivedCategory

set_option maxHeartbeats 2000000 in
-- Elaborating the representative and coherence equations uses the native derived tensors.
/-- The canonical K-flat point tensor comparison. The family is indexed by the usual
upper-cohomology bounds; no assertion on unbounded operands is imposed. Its inverse on
resolving complexes is the actual section-tensor map on each total-complex summand.
The unit comparison is pinned by both unitor equations and this tensor normalization.
Source: Stacks 07A4, 03EL
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
structure TensorComparison where
  tau : ∀ (P Q : DerivedCategory.{u + 1} (Modules k B)),
    (∃ b : ℤ, P.IsLE b) → (∃ c : ℤ, Q.IsLE c) →
    CategoryTheory.Iso ((sections k B).obj (P ⊗ Q))
      (@tensorObj (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (SectionRing k B))) _ _
        ((sections k B).obj P) ((sections k B).obj Q))
  unit : (sections k B).obj (𝟙_ _) ≅ 𝟙_ _
  naturality : ∀ (P Q P' Q' : DerivedCategory.{u + 1} (Modules k B))
    (hP : ∃ b : ℤ, P.IsLE b) (hQ : ∃ b : ℤ, Q.IsLE b)
    (hP' : ∃ b : ℤ, P'.IsLE b) (hQ' : ∃ b : ℤ, Q'.IsLE b)
    (f : P ⟶ P') (g : Q ⟶ Q'),
    (sections k B).map (f ⊗ₘ g) ≫ (tau P' Q' hP' hQ').hom =
      (tau P Q hP hQ).hom ≫ ((sections k B).map f ⊗ₘ (sections k B).map g)
  bounded_tensor : ∀ (P Q : DerivedCategory.{u + 1} (Modules k B)),
    (∃ b : ℤ, P.IsLE b) → (∃ b : ℤ, Q.IsLE b) → ∃ b : ℤ, (P ⊗ Q).IsLE b
  bounded_sections : ∀ P : DerivedCategory.{u + 1} (Modules k B),
    (∃ b : ℤ, P.IsLE b) → ∃ b : ℤ, ((sections k B).obj P).IsLE b
  associativity : ∀ (P Q R : DerivedCategory.{u + 1} (Modules k B))
    (hP : ∃ b : ℤ, P.IsLE b) (hQ : ∃ b : ℤ, Q.IsLE b) (hR : ∃ b : ℤ, R.IsLE b),
    (tau (P ⊗ Q) R (bounded_tensor P Q hP hQ) hR).hom ≫
        ((tau P Q hP hQ).hom ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom =
      (sections k B).map (α_ P Q R).hom ≫
        (tau P (Q ⊗ R) hP (bounded_tensor Q R hQ hR)).hom ≫
        (𝟙 _ ⊗ₘ (tau Q R hQ hR).hom)
  symmetry : ∀ (P Q : DerivedCategory.{u + 1} (Modules k B))
    (hP : ∃ b : ℤ, P.IsLE b) (hQ : ∃ b : ℤ, Q.IsLE b),
    (tau P Q hP hQ).hom ≫ (β_ _ _).hom =
      (sections k B).map (β_ P Q).hom ≫ (tau Q P hQ hP).hom
  bounded_unit : ∃ b : ℤ, (𝟙_ (DerivedCategory.{u + 1} (Modules k B))).IsLE b
  left_unit : ∀ (P : DerivedCategory.{u + 1} (Modules k B)) (hP : ∃ b : ℤ, P.IsLE b),
    (tau (𝟙_ _) P bounded_unit hP).hom ≫ (unit.hom ⊗ₘ 𝟙 _) ≫ (λ_ _).hom =
      (sections k B).map (λ_ P).hom
  right_unit : ∀ (P : DerivedCategory.{u + 1} (Modules k B)) (hP : ∃ b : ℤ, P.IsLE b),
    (tau P (𝟙_ _) hP bounded_unit).hom ≫ (𝟙 _ ⊗ₘ unit.hom) ≫ (ρ_ _).hom =
      (sections k B).map (ρ_ P).hom
  representative : ∀ (P Q : CochainComplex (Modules k B) ℤ)
    (hP : ∃ b : ℤ, (DerivedCategory.Q.obj P).IsLE b)
    (hQ : ∃ b : ℤ, (DerivedCategory.Q.obj Q).IsLE b),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) Q →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (Q.X i)) →
    ∃ b : ((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P ⊗
          ((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q),
      (∀ (p q n : ℤ) (h : p + q = n)
        (x : (P.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
        (y : (Q.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
        (b.hom.f n)
          (WeilConjectures.coefficientTensorGenerator.{0, u + 1, u}
            (Scheme.ProEt.topology (Spec (.of k))) B P Q p q n h
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y) =
          (CochainComplex.ιMapBifunctor
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P)
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q)
            (curriedTensor _) p q n h) (x ⊗ₜ[SectionRing k B] y)) ∧
      (sections k B).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          (pointModuleSections k B).mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map b.hom =
        (tau (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) hP hQ).hom ≫
          ((pointModuleSections k B).mapDerivedCategoryFactors.hom.app P ⊗ₘ
            (pointModuleSections k B).mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P)
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj Q)

variable {B}
variable {C : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}

/-- Evaluation of the actual coefficient morphism at the final object.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
abbrev sectionMap (a : B ⟶ C) : SectionRing k B →+* SectionRing k C :=
  (a.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).hom

/-- The existing restriction/coextension adjunction with all universes specified.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) restrictionLeftAdjoint
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.restrictScalars.{u, u, u} φ).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} φ).isLeftAdjoint

/-- The existing extension/restriction adjunction with all universes specified.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) restrictionRightAdjoint
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.restrictScalars.{u, u, u} φ).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).isRightAdjoint

/-- Additivity of the actual ordinary extension, with no flatness hypothesis.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) extensionAdditive
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  ModuleCat.extendScalars_additive.{u} (f := φ)

/-- Finite-limit preservation in the fixed ordinary module universe.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) restrictionFiniteLimits
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u} φ) :=
  letI : PreservesLimitsOfSize.{0, 0} (ModuleCat.restrictScalars.{u, u, u} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Finite-colimit preservation in the fixed ordinary module universe.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
instance (priority := 30000) restrictionFiniteColimits
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u} φ) :=
  letI : PreservesColimitsOfSize.{0, 0} (ModuleCat.restrictScalars.{u, u, u} φ) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} φ).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The restriction/evaluation square is literally the identity on sections and maps.
Source: Stacks 03DA (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def restrictionSections (a : B ⟶ C) :
    SheafOfModules.scalarRestriction
        (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := C) a ⋙ pointModuleSections k B ≅
      pointModuleSections k C ⋙ ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (sectionMap k a) :=
  Iso.refl _

/-- Localization of the identity restriction/evaluation square.
Source: Stacks 07A6 (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def derivedRestrictionSections (a : B ⟶ C) :
    SheafOfModules.scalarDerivedRestriction
        (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := C) a ⋙ sections k B ≅
      sections k C ⋙ ModuleCat.derivedRestrictScalars (sectionMap k a) :=
  (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.scalarRestriction
        (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := C) a) (pointModuleSections k
          B)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (restrictionSections k a) ≪≫
  Functor.mapDerivedCategoryCompIso (pointModuleSections k C)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (sectionMap k a))

/-- The adjoint transpose of the actual sheaf extension unit. No comparison map is chosen.
Source: Stacks 07A6 (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def scalarComparison (a : B ⟶ C) (s : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := C) a)
    (d : ModuleCat.OrdinaryDerivedChangeOfRings (sectionMap k a))
    (adj : d.F ⊣ ModuleCat.derivedRestrictScalars (sectionMap k a))
    (N : DerivedCategory.{u + 1} (Modules k B)) :
    d.F.obj ((sections k B).obj N) ⟶ (sections k C).obj (s.derived.obj N) :=
  (adj.homEquiv _ _).symm
    ((sections k B).map (s.adjunction.unit.app N) ≫
      (derivedRestrictionSections k a).hom.app (s.derived.obj N))

set_option maxHeartbeats 2000000 in
-- Elaborating the representative and coherence equations uses the native derived tensors.
/-- The normalized scalar comparison, including its canonical representative and
its monoidal square. The ordinary derived pair and its adjunction are not arbitrary:
the universal pair computes on K-flat complexes and the chain unit equation fixes
its adjunction. The sheaf pair retains the corresponding existing normalization.
Source: Stacks 07A4 and 07A6
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
structure ScalarComparison (a : B ⟶ C)
    (tB : TensorComparison k B) (tC : TensorComparison k C) where
  sheaf : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := C) a
  ordinary : ModuleCat.OrdinaryDerivedChangeOfRings (sectionMap k a)
  adjunction : ordinary.F ⊣ ModuleCat.derivedRestrictScalars (sectionMap k a)
  ordinary_unit : ∀ P : CochainComplex (ModuleCat.{u + 1} (SectionRing k B)) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (SectionRing k B)) (.up ℤ)).kFlat P →
    adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.derivedRestrictScalars (sectionMap k a)).map (ordinary.counit.app P) ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (sectionMap k
          a)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (sectionMap k a)).mapHomologicalComplex
            (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (sectionMap k
          a)).mapHomologicalComplex
          (.up ℤ)).unit.app P)
  bounded_sheaf : ∀ N : DerivedCategory.{u + 1} (Modules k B),
    (∃ b : ℤ, N.IsLE b) → ∃ b : ℤ, (sheaf.derived.obj N).IsLE b
  bounded_ordinary : ∀ N : DerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (SectionRing k B)),
    (∃ b : ℤ, N.IsLE b) → ∃ b : ℤ, (ordinary.F.obj N).IsLE b
  invertible : ∀ (N : DerivedCategory.{u + 1} (Modules k B)),
    (∃ b : ℤ, N.IsLE b) →
      IsIso (scalarComparison k a sheaf ordinary adjunction N)
  naturality : ∀ (N N' : DerivedCategory.{u + 1} (Modules k B))
    (_hN : ∃ b : ℤ, N.IsLE b) (_hN' : ∃ b : ℤ, N'.IsLE b) (f : N ⟶ N'),
    ordinary.F.map ((sections k B).map f) ≫
        scalarComparison k a sheaf ordinary adjunction N' =
      scalarComparison k a sheaf ordinary adjunction N ≫
        (sections k C).map (sheaf.derived.map f)
  unit_equation : ∀ (N : DerivedCategory.{u + 1} (Modules k B)),
    (∃ b : ℤ, N.IsLE b) →
    adjunction.unit.app ((sections k B).obj N) ≫
        (ModuleCat.derivedRestrictScalars (sectionMap k a)).map
          (scalarComparison k a sheaf ordinary adjunction N) =
      (sections k B).map (sheaf.adjunction.unit.app N) ≫
        (derivedRestrictionSections k a).hom.app (sheaf.derived.obj N)
  unique : ∀ (N : DerivedCategory.{u + 1} (Modules k B))
    (_hN : ∃ b : ℤ, N.IsLE b)
    (f : ordinary.F.obj ((sections k B).obj N) ⟶ (sections k C).obj (sheaf.derived.obj N)),
    adjunction.unit.app ((sections k B).obj N) ≫
        (ModuleCat.derivedRestrictScalars (sectionMap k a)).map f =
      (sections k B).map (sheaf.adjunction.unit.app N) ≫
        (derivedRestrictionSections k a).hom.app (sheaf.derived.obj N) →
    f = scalarComparison k a sheaf ordinary adjunction N
  representative : ∀ (P : CochainComplex (Modules k B) ℤ)
    (_hP : ∃ b : ℤ, (DerivedCategory.Q.obj P).IsLE b),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (P.X n)) →
    ∃ κ : ((pointModuleSections k C).mapHomologicalComplex (.up ℤ)).obj
          ((SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj P) ≅
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (sectionMap k a)).mapHomologicalComplex
          (.up ℤ)).obj
          (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (n : ℤ) (c : SectionRing k C)
        (x : (P.X n).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
        (κ.hom.f n)
            (c • (@id ((sheaf.extension.obj (P.X n)).val.obj
                (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
              ((sheaf.ordinaryAdjunction.unit.app (P.X n)).val.app
                (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x))) =
          c • (@id ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
              (sectionMap k a)).obj ((pointModuleSections k B).obj (P.X n)))
            ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
              (sectionMap k a)).unit.app ((pointModuleSections k B).obj (P.X n)) x))) ∧
      scalarComparison k a sheaf ordinary adjunction (DerivedCategory.Q.obj P) ≫
          (sections k C).map (SheafOfModules.scalarPairComplexComparison
            sheaf.extension sheaf.extension_additive sheaf.derived sheaf.counit P) ≫
          (pointModuleSections k C).mapDerivedCategoryFactors.hom.app
            ((SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj P) =
        ordinary.F.map ((pointModuleSections k B).mapDerivedCategoryFactors.hom.app P) ≫
          ordinary.counit.app
            (((pointModuleSections k B).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map κ.inv
  tensor : ∀ (P Q : DerivedCategory.{u + 1} (Modules k B)),
    (∃ b : ℤ, P.IsLE b) → (∃ b : ℤ, Q.IsLE b) →
      CategoryTheory.Iso (sheaf.derived.obj (P ⊗ Q))
        (@tensorObj (DerivedCategory.{u + 1} (Modules k C)) _ _
          (sheaf.derived.obj P) (sheaf.derived.obj Q))
  tensor_naturality : ∀ (P Q P' Q' : DerivedCategory.{u + 1} (Modules k B))
    (hP : ∃ n : ℤ, P.IsLE n) (hQ : ∃ n : ℤ, Q.IsLE n)
    (hP' : ∃ n : ℤ, P'.IsLE n) (hQ' : ∃ n : ℤ, Q'.IsLE n)
    (f : P ⟶ P') (g : Q ⟶ Q'),
    sheaf.derived.map (f ⊗ₘ g) ≫ (tensor P' Q' hP' hQ').hom =
      (tensor P Q hP hQ).hom ≫ (sheaf.derived.map f ⊗ₘ sheaf.derived.map g)
  tensor_representative : ∀ (P Q : CochainComplex (Modules k B) ℤ)
    (hP : ∃ b : ℤ, (DerivedCategory.Q.obj P).IsLE b)
    (hQ : ∃ b : ℤ, (DerivedCategory.Q.obj Q).IsLE b),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) Q →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (Q.X n)) →
    ∃ e : (SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj
          (P ⊗ Q) ≅
        ((SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj P ⊗
          (SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj Q),
      (∀ (p q n : ℤ) (h : p + q = n)
        (V : (Spec (.of k)).ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        ((e.hom.f n).val.app V)
          (((sheaf.ordinaryAdjunction.unit.app ((P ⊗ Q).X n)).val.app V)
            (WeilConjectures.coefficientTensorGenerator.{0, u + 1, u}
              (Scheme.ProEt.topology (Spec (.of k))) B P Q p q n h V x y)) =
          WeilConjectures.coefficientTensorGenerator.{0, u + 1, u}
            (Scheme.ProEt.topology (Spec (.of k))) C
            ((SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj P)
            ((SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj Q)
            p q n h V
            (((sheaf.ordinaryAdjunction.unit.app (P.X p)).val.app V) x)
            (((sheaf.ordinaryAdjunction.unit.app (Q.X q)).val.app V) y)) ∧
      sheaf.derived.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          SheafOfModules.scalarPairComplexComparison
            sheaf.extension sheaf.extension_additive sheaf.derived sheaf.counit (P ⊗ Q) ≫
          DerivedCategory.Q.map e.hom =
        (tensor (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) hP hQ).hom ≫
          (SheafOfModules.scalarPairComplexComparison
              sheaf.extension sheaf.extension_additive sheaf.derived sheaf.counit P ⊗ₘ
            SheafOfModules.scalarPairComplexComparison
              sheaf.extension sheaf.extension_additive sheaf.derived sheaf.counit Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            ((SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj P)
            ((SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj Q)
  monoidal : ∀ (P Q : DerivedCategory.{u + 1} (Modules k B))
    (hP : ∃ b : ℤ, P.IsLE b) (hQ : ∃ b : ℤ, Q.IsLE b),
    scalarComparison k a sheaf ordinary adjunction (P ⊗ Q) ≫
        (sections k C).map (tensor P Q hP hQ).hom ≫
        (tC.tau _ _ (bounded_sheaf P hP) (bounded_sheaf Q hQ)).hom =
      ordinary.F.map (tB.tau P Q hP hQ).hom ≫
        Functor.OplaxMonoidal.δ ordinary.F ((sections k B).obj P) ((sections k B).obj Q) ≫
        (scalarComparison k a sheaf ordinary adjunction P ⊗ₘ
          scalarComparison k a sheaf ordinary adjunction Q)
  coefficient : sheaf.derived.obj (𝟙_ _) ≅ 𝟙_ _
  coefficient_representative :
    ∃ e : (SheafOfModules.scalarComplex sheaf.extension sheaf.extension_additive).obj
        (𝟙_ (CochainComplex (Modules k B) ℤ)) ≅
          𝟙_ (CochainComplex (Modules k C) ℤ),
      (∀ (V : (Spec (.of k)).ProEtᵒᵖ) (b : B.obj.obj V),
        ((e.hom.f 0).val.app V)
          (((sheaf.ordinaryAdjunction.unit.app
            ((𝟙_ (CochainComplex (Modules k B) ℤ)).X 0)).val.app V)
              (ringedTensorUnitSection.{u + 1, u, 0}
                (Scheme.ProEt.topology (Spec (.of k))) B V b)) =
          ringedTensorUnitSection.{u + 1, u, 0}
            (Scheme.ProEt.topology (Spec (.of k))) C V (a.hom.app V b)) ∧
      sheaf.derived.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
          SheafOfModules.scalarPairComplexComparison
            sheaf.extension sheaf.extension_additive sheaf.derived sheaf.counit (𝟙_ _) ≫
          DerivedCategory.Q.map e.hom =
        coefficient.hom ≫ Functor.LaxMonoidal.ε DerivedCategory.Q
  coefficient_equation :
    scalarComparison k a sheaf ordinary adjunction (𝟙_ _) ≫
        (sections k C).map coefficient.hom ≫ tC.unit.hom =
      ordinary.F.map tB.unit.hom ≫ Functor.OplaxMonoidal.η ordinary.F

/-- The derived identity associator for sheaf extension, fixed by the specified units.
Source: Stacks 07A6 (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def sheafIdentity (s : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := B) (𝟙 B)) :
    s.derived ≅ 𝟭 (DerivedCategory.{u + 1} (Modules k B)) :=
  Adjunction.leftAdjointUniq
    (s.adjunction.ofNatIsoRight
      (CategoryTheory.scalarHomRestrictionId.{u + 1, u, 0, u + 1} B)) Adjunction.id

/-- The derived identity associator for ordinary extension, fixed by its specified unit.
Source: Stacks 07A6 (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def ordinaryIdentity (d : ModuleCat.OrdinaryDerivedChangeOfRings (sectionMap k (𝟙 B)))
    (adj : d.F ⊣ ModuleCat.derivedRestrictScalars (sectionMap k (𝟙 B))) :
    d.F ≅ 𝟭 (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (SectionRing k B))) :=
  Adjunction.leftAdjointUniq
    (adj.ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsId _) ≪≫
        Functor.mapDerivedCategoryIdIso _)) Adjunction.id

variable {D : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}

/-- The sheaf derived tensor associator is the canonical comparison of left adjoints
of the actual restriction compositor, rather than an unspecified isomorphism.
Source: Stacks 0D6D (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def sheafComposition (a : B ⟶ C) (b : C ⟶ D)
    (s : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := C) a) (t :
        SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := C) (S := D) b)
    (v : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k))) (R := B) (S := D) (a ≫ b)) :
    s.derived ⋙ t.derived ≅ v.derived :=
  Adjunction.leftAdjointUniq (s.adjunction.comp t.adjunction)
    (v.adjunction.ofNatIsoRight
      (CategoryTheory.scalarHomRestrictionComp.{u + 1, u, 0, u + 1} a b))

/-- The ordinary derived tensor associator is the comparison of the normalized adjoints.
Source: Stacks 0D6D (blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
def ordinaryComposition (a : B ⟶ C) (b : C ⟶ D)
    (s : ModuleCat.OrdinaryDerivedChangeOfRings (sectionMap k a))
    (t : ModuleCat.OrdinaryDerivedChangeOfRings (sectionMap k b))
    (v : ModuleCat.OrdinaryDerivedChangeOfRings (sectionMap k (a ≫ b)))
    (as : s.F ⊣ ModuleCat.derivedRestrictScalars (sectionMap k a))
    (adjT : t.F ⊣ ModuleCat.derivedRestrictScalars (sectionMap k b))
    (av : v.F ⊣ ModuleCat.derivedRestrictScalars (sectionMap k (a ≫ b))) :
    s.F ⋙ t.F ≅ v.F :=
  Adjunction.leftAdjointUniq (as.comp adjT)
    (av.ofNatIsoRight (ModuleCat.derivedRestrictScalarsCompIso (f := sectionMap k a)
      (g := sectionMap k b) (gf := sectionMap k (a ≫ b)) rfl).symm)

set_option maxHeartbeats 2000000 in
-- Elaborating the representative and coherence equations uses the native derived tensors.
/-- All finite coefficient maps simultaneously, with the identity and composition
normalizations of their canonical comparisons. Finiteness is imposed on coefficients,
never on a module and never as a flatness condition on a coefficient map.
Source: blueprint finite reduction, Stacks 07A4, 07A6 and 0D6D
(blueprint: lem-sf-condensed-point-derived-scalar-comparison). -/
structure ComparisonFamily where
  tensor : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
    IsFiniteCoefficient k B → TensorComparison k B
  scalar : ∀ (B C : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (hB : IsFiniteCoefficient k B) (hC : IsFiniteCoefficient k C) (a : B ⟶ C),
    ScalarComparison k a (tensor B hB) (tensor C hC)
  identity : ∀ (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (hB : IsFiniteCoefficient k B),
    ∀ (N : DerivedCategory.{u + 1} (Modules k B)), (∃ n : ℤ, N.IsLE n) →
    scalarComparison k (𝟙 B) (scalar B B hB hB (𝟙 B)).sheaf
        (scalar B B hB hB (𝟙 B)).ordinary (scalar B B hB hB (𝟙 B)).adjunction N =
      (ordinaryIdentity k (scalar B B hB hB (𝟙 B)).ordinary
          (scalar B B hB hB (𝟙 B)).adjunction).hom.app ((sections k B).obj N) ≫
        (sections k B).map ((sheafIdentity k
          (scalar B B hB hB (𝟙 B)).sheaf).inv.app N)
  composition : ∀ (B C D : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (hB : IsFiniteCoefficient k B) (hC : IsFiniteCoefficient k C)
    (hD : IsFiniteCoefficient k D) (a : B ⟶ C) (b : C ⟶ D)
    (N : DerivedCategory.{u + 1} (Modules k B)) (_hN : ∃ n : ℤ, N.IsLE n),
    (ordinaryComposition k a b
        (scalar B C hB hC a).ordinary (scalar C D hC hD b).ordinary
        (scalar B D hB hD (a ≫ b)).ordinary
        (scalar B C hB hC a).adjunction (scalar C D hC hD b).adjunction
        (scalar B D hB hD (a ≫ b)).adjunction).hom.app ((sections k B).obj N) ≫
        scalarComparison k (a ≫ b) (scalar B D hB hD (a ≫ b)).sheaf
          (scalar B D hB hD (a ≫ b)).ordinary
          (scalar B D hB hD (a ≫ b)).adjunction N =
      (scalar C D hC hD b).ordinary.F.map
          (scalarComparison k a (scalar B C hB hC a).sheaf
            (scalar B C hB hC a).ordinary (scalar B C hB hC a).adjunction N) ≫
        scalarComparison k b (scalar C D hC hD b).sheaf
          (scalar C D hC hD b).ordinary (scalar C D hC hD b).adjunction
          ((scalar B C hB hC a).sheaf.derived.obj N) ≫
        (sections k D).map ((sheafComposition k a b
          (scalar B C hB hC a).sheaf (scalar C D hC hD b).sheaf
          (scalar B D hB hD (a ≫ b)).sheaf).hom.app N)

  internal_tensor : ∀
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R],
    IsFiniteCoefficient k (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (Spec (.of k))) R) →
    exactFunctor _ _ (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) R).functor ∧
    ∃ e : (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) R).functor.Monoidal,
      (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k)))
          AddCommGrpCat.{u + 1}) R)
        (V : (Spec (.of k)).ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        ((e.δ M N).val.app V)
          (InternalAbelianSheafModule.comparison_internalTmul
            (Scheme.ProEt.topology (Spec (.of k))) R M N V x y) =
          InternalAbelianSheafModule.comparison_sectionTmul
            (Scheme.ProEt.topology (Spec (.of k)))
            R
            ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
              (Scheme.ProEt.topology (Spec (.of k))) R).functor.obj M)
            ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
              (Scheme.ProEt.topology (Spec (.of k))) R).functor.obj N) V x y) ∧
      (∀ (V : (Spec (.of k)).ProEtᵒᵖ) (r : R.obj.obj V),
        (e.η.val.app V) r = r) ∧
      ∀ M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}) R,
        e.δ M N ≫ (β_ _ _).hom =
          (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
            (Scheme.ProEt.topology (Spec (.of k))) R).functor.map (β_ M N).hom ≫ e.δ N M
  internal_scalar : ∀
    (R S : Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [HasDerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}) R)]
    [HasDerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}) S)],
    IsFiniteCoefficient k (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (Spec (.of k))) R) →
    IsFiniteCoefficient k (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (Spec (.of k))) S) →
    InternalAbelianSheafModule.InternalSectionScalarAdjunction.{u + 1, u + 1, u, u + 1}
      (Scheme.ProEt.topology (Spec (.of k))) (R := R) (S := S) a

/-- Exact point sections commute with the relative K-flat tensor and with every finite
change of discrete condensed coefficients, with their canonical units and associators.
The sectionwise categories are also the chosen presentation of the internal-module
assertion: `sectionModuleEquivalence`, `internal_section_tensor_comparison`, and
`internal_section_scalar_adjunction` identify the actual objects, maps, tensors and
adjunctions. This convention does not replace an internal tensor by an arbitrary one.

Source: blueprint, sec-six-functors/sk-thm-sf-package/thm-pod-finite-reduction.proof.md,
first paragraph; Stacks 03EK, 03EL, 06YS, 07A4, 07A6 and 0D6D
(blueprint: lem-sf-condensed-point-derived-scalar-comparison).

Proof:
1. `point_proEtale_sections_exact` makes final-object evaluation exact, hence termwise
localization gives the stated sections functor. `condensed_point_coefficients`
identifies the pulled-back finite discrete condensed rings with the constant sheaves.
Consequently evaluating a coefficient morphism gives its original finite ring map.
2. Choose flat-term K-flat representatives by lem-pc-kflat-resolution. The ordinary
section tensor map is invertible at this point; on each homogeneous summand it takes
x tensor y to the actual sheafified tensor of sections. Localize its inverse to obtain
`tau`. Its associativity, Koszul symmetry and both unitor identities are the corresponding
identities on these total-complex summands, independent of the representatives.
3. Good upper truncation and lem-pc-kflat-bounded-flat-replacement give bounded-above
flat replacements; lem-pc-bounded-above-flat-kflat-site makes them K-flat. Tensor total
has upper bound the sum of the two bounds, scalar extension preserves an upper term
bound, and exact sections preserve the cohomology bound. This restricts every functor
to D-minus without any Tor-dimension assumption on the coefficient map.
4. On a flat-term K-flat representative P, the scalar comparison kappa sends the
sheafification-unit generator c tensor x to c tensor x. Its inverse, localized using
the universal derived-pair comparisons, is eta. The specified ordinary and sheaf
adjunction units are 1 tensor x. Thus eta satisfies the displayed unit equation;
the adjunction Hom bijection proves uniqueness and naturality.
5. On each homogeneous summand the two monoidal paths send (x tensor y) tensor c
to (x tensor 1) tensor (y tensor c). Coefficients have degree zero, so moving a
coefficient introduces no sign. Localization gives the asserted monoidal square.
6. Apply the same calculation to the coefficient ring in degree zero: eta is the
multiplication map 1 tensor c to c, and identity extension is the identity under
its unit-normalized associators. For A to C to D, both composite and direct maps
send d tensor (c tensor x) to d times b(c) tensor x. Extension preserves K-flat
resolutions, so the calculation computes the derived composition even for nonflat maps.
The canonical comparison of the normalized left adjoints is this very associator.
7. Finally the exact internal-module equivalence preserves sections and their maps.
The recorded tensor comparison preserves the total differential, K-flatness and all
constraints; the scalar-adjunction comparison preserves the specified units and
counits. Transporting the preceding statement therefore gives the identical internal
assertion under the identifications stipulated in the node. -/
theorem condensed_point_derived_scalar_comparison : Nonempty (ComparisonFamily k) := by
  sorry

end AlgebraicGeometry.ProEtale.FinitePointComparison
