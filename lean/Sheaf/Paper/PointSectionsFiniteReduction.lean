/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.PointSectionsFiniteness
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

import Sheaf.Paper.ConstantModuleSectionProperties
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-!
# Point sections and finite coefficient reduction

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
`sk-prop-trace-adic/prop-trf-adic-coefficient-morphism-systems.proof.md`, Proof (1)
(blueprint: lem-trf-point-sections-finite-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- The standard small model of the point site in the coefficient universe.
Source: Stacks Tag 0982 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSiteSmall (k : Type u) [Field k] :
    EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Ring sheafification in the standard coefficient universe.
Source: Stacks Tag 00W1 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance (priority := 2000) pointFiniteReductionRingSheafify
    (k : Type u) [Field k] :
    HasSheafify (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _

/-- Additive sheafification in the same coefficient universe.
Source: Stacks Tag 00W1 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance (priority := 2000) pointFiniteReductionGroupSheafify
    (k : Type u) [Field k] :
    HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _

/-- The standard local-bijection characterization for additive sheafification.
Source: Stacks Tag 00W1 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance (priority := 2000) pointFiniteReductionLocalBijections
    (k : Type u) [Field k] :
    (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1} _

/-- The constant coefficient ring sheaf at an algebraically closed point.
Source: Stacks Tags 093J and 0982 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionRingSheaf (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))

/-- The quotient map between finite coefficient levels.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionRingMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n j : ℕ) (h : j ≤ n) :
    ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n) →+*
      ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j) :=
  RingHom.ulift (Ideal.Quotient.factor (Ideal.pow_le_pow_right h))

/-- The ordinary derived tensor functor for a finite coefficient quotient.
Source: Stacks Tags 06Y6 and 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionModuleTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n j : ℕ) (h : j ≤ n) :
    DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ⥤
    DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))) :=
  (Classical.choose (DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointFiniteReductionRingMap l E n j h)).2).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E j))
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))))

/-- Exactness of finite coefficient sections at kernels.
Source: Stacks Tags 0982 and 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSectionsLimits (k : Type u) [Field k]
    [IsAlgClosed k] (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    PreservesFiniteLimits (pointFiniteSections k (Padic.coefficientExtensionRing l E n)) := by
  let A := (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
  letI : PreservesFiniteLimits (pointModuleSections k A) :=
    ((@point_proEtale_sections_exact.{u, u + 1, u + 1} k).2 A).1
  exact inferInstanceAs (PreservesFiniteLimits
    (pointModuleSections k _ ⋙ ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointConstantSectionMap k (Padic.coefficientExtensionRing l E n))))

/-- Exactness of finite coefficient sections at cokernels.
Source: Stacks Tags 0982 and 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSectionsColimits (k : Type u) [Field k]
    [IsAlgClosed k] (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    PreservesFiniteColimits (pointFiniteSections k (Padic.coefficientExtensionRing l E n)) := by
  let A := (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
  letI : PreservesFiniteColimits (pointModuleSections k A) :=
    ((@point_proEtale_sections_exact.{u, u + 1, u + 1} k).2 A).2.1
  letI : PreservesFiniteColimits
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (pointConstantSectionMap k (Padic.coefficientExtensionRing l E n))) := by
    infer_instance
  exact inferInstanceAs (PreservesFiniteColimits
    (pointModuleSections k _ ⋙ ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointConstantSectionMap k (Padic.coefficientExtensionRing l E n))))

/-- Derived sections at the final point with the canonical finite coefficient action.
Source: Stacks Tags 0946 and 0982 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSections (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    DerivedCategory
      (SheafOfModules.{u + 1}
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
          (Scheme.ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E n))) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory

/-- The existing coefficient module category, with the point-site size lift.
Source: Stacks Tag 06Y6 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionModules (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))

/-- The existing module-sheaf category on the small pro-etale point site.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionSheaves (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  SheafOfModules.{u + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E n))

variable (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical map of constant coefficient sheaves.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafMap (n j : ℕ) (h : j ≤ n) :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (pointFiniteReductionRingMap l E n j h))

set_option linter.defProp false in
/-- The universal derived-change-of-rings witness; both its objects and maps are fixed.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafExistence (n j : ℕ) (h : j ≤ n) :=
  letI : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) :=
    essentiallySmallSelf.{0, u, u + 1} _
  letI : HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  letI : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  letI := HasDerivedCategory.standard (pointFiniteReductionSheaves k l E n)
  letI := HasDerivedCategory.standard (pointFiniteReductionSheaves k l E j)
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := Scheme.ProEt.topology (Spec (.of k)))
    (O := pointFiniteReductionRingSheaf k l E n)
    (O' := pointFiniteReductionRingSheaf k l E j)
    (pointFiniteReductionSheafMap k l E n j h)

/-- Ordinary sheaf scalar extension from the universal witness.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafExtension (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionSheaves k l E n ⥤ pointFiniteReductionSheaves k l E j :=
  (pointFiniteReductionSheafExistence k l E n j h).choose

/-- Additivity is part of the universal scalar-extension witness.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSheafExtensionAdditive (n j : ℕ) (h : j ≤ n) :
    (pointFiniteReductionSheafExtension k l E n j h).Additive :=
  (pointFiniteReductionSheafExistence k l E n j h).choose_spec.choose_spec.choose_spec.choose

/-- Derived scalar extension, retaining the same universal witness as its counit.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafTensor (n j : ℕ) (h : j ≤ n) :
    DerivedCategory (pointFiniteReductionSheaves k l E n) ⥤
      DerivedCategory (pointFiniteReductionSheaves k l E j) :=
  (((pointFiniteReductionSheafExistence k l E n j h).choose_spec
    ).choose_spec.choose_spec.choose_spec).2.2.choose

/-- The universal sheaf-tensor computation map on a complex.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafCounit (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) :
    (pointFiniteReductionSheafTensor k l E n j h).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (pointFiniteReductionSheafTensor k l E n j h).map
      ((DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E n)).inv.app P) ≫
    ((((pointFiniteReductionSheafExistence k l E n j h).choose_spec
      ).choose_spec.choose_spec.choose_spec).2.2.choose_spec.choose).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E j)).hom.app
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex (.up ℤ)).obj P)

/-- The quotient coefficient complex in degree zero.
Source: Stacks Tag 06Y6 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionCoefficientComplex (j : ℕ) :
    CochainComplex (pointFiniteReductionModules l E j) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj
    (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j)))

/-- The actual mixed total-tensor complex computing ordinary reduction.
Source: Stacks Tag 06Y6 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionComplexTensor (n j : ℕ) (h : j ≤ n) :
    CochainComplex (pointFiniteReductionModules l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionModules l E j) ℤ :=
  (((ModuleCat.mixedTensor (pointFiniteReductionRingMap l E n j h)).flip
    ).map₂CochainComplex).flip.obj (pointFiniteReductionCoefficientComplex l E j)

/-- The universal ordinary-tensor computation map, retained with the chosen functor.
Source: Stacks Tag 06Y6 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionModuleCounit (n j : ℕ) (h : j ≤ n) :
    DerivedCategory.Q ⋙ pointFiniteReductionModuleTensor l E n j h ⟶
      pointFiniteReductionComplexTensor l E n j h ⋙ DerivedCategory.Q :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointFiniteReductionRingMap l E n j h)).2.choose_spec.choose
    (pointFiniteReductionCoefficientComplex l E j)

/-- Termwise scalar extension, using the recorded ordinary sheaf extension.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafComplexTensor (n j : ℕ) (h : j ≤ n) :
    CochainComplex (pointFiniteReductionSheaves k l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionSheaves k l E j) ℤ :=
  (pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex (.up ℤ)

/-- Termwise point sections, with the fixed quotient-coefficient action.
Source: Stacks Tag 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSectionComplex (n : ℕ) :
    CochainComplex (pointFiniteReductionSheaves k l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionModules l E n) ℤ :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex (.up ℤ)

/-- The specified tensor generator in the degree-a summand of the mixed total complex.
Source: Stacks Tag 06Y6 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionTensorGenerator (n j : ℕ) (h : j ≤ n)
    (C : CochainComplex (pointFiniteReductionModules l E n) ℤ) (a : ℤ)
    (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j)) (x : C.X a) :
    ((pointFiniteReductionComplexTensor l E n j h).obj C).X a :=
  (HomologicalComplex.ιMapBifunctorOrZero C
    (pointFiniteReductionCoefficientComplex l E j)
    (ModuleCat.mixedTensor (pointFiniteReductionRingMap l E n j h)).flip
    (.up ℤ) a 0 a)
    (b ⊗ₜ (c ⊗ₜ[_, pointFiniteReductionRingMap l E n j h] x))

/-- The image of a section under the actual sheaf quotient unit, not a chosen map.
Source: Stacks Tag 03EK (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSectionGenerator (n j : ℕ) (h : j ≤ n)
    (M : pointFiniteReductionSheaves k l E n)
    (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M) :
    (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).obj
      ((pointFiniteReductionSheafExtension k l E n j h).obj M) := by
  letI : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) :=
    essentiallySmallSelf.{0, u, u + 1} _
  letI : HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  letI : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  let y := (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E j))
      (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (pointFiniteReductionSheafMap k l E n j h) M)).app
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        ((pointFiniteReductionSheafMap k l E n j h).hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).hom).unit.app
            (M.val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))) x)
  exact (eqToHom
    ((pointFiniteReductionSheafExistence k l E n j h).choose_spec.choose M).symm).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) y

/-- The exact-sections localization comparison at a complex.
Source: Stacks Tag 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSectionFactors [IsAlgClosed k] (n : ℕ)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) :
    (pointFiniteReductionSections k l E n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((pointFiniteReductionSectionComplex k l E n).obj P) :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapDerivedCategoryFactors.app P

/-- Mathlib's bounded-above object property, specialized to the point sheaf category.
Source: blueprint Proof (1), Stacks Tag 064L
(blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionBoundedAbove (n : ℕ) :
    ObjectProperty (DerivedCategory (pointFiniteReductionSheaves k l E n)) :=
  (DerivedCategory.TStructure.t (C := pointFiniteReductionSheaves k l E n)).minus

variable [IsAlgClosed k]

/-- Natural comparison on the bounded-above derived subcategory.
Source: Steps 4--6 of the parent proof.
(blueprint: lem-trf-point-sections-finite-reduction-iso).

Proof: resolve bounded-above objects by functorial bounded-above flat complexes. Exact point
sections identify the degreewise quotient complex with sections after sheaf scalar extension.
The derived change-of-rings universal counits and localization universal property descend this
comparison to a natural isomorphism on the bounded-above subcategory.
-/
theorem point_sections_finite_reduction_iso (_hl : IsUnit (l : k)) :
    Nonempty (∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙
            pointFiniteReductionSections k l E j) := by
  sorry

/-- Boundedness and vanishing after finite coefficient reduction.
Source: Steps 4 and 7 of the parent proof.
(blueprint: lem-trf-point-sections-finite-reduction-bounded).

Proof: finite scalar extension of a bounded-above flat model remains bounded above and termwise
flat. Exact point sections preserve the resulting complexes and their homology, so the reduced
sheaf object and the module tensor object have the asserted upper vanishing bound.
-/
theorem point_sections_finite_reduction_bounded (_hl : IsUnit (l : k)) :
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      (∀ N : (pointFiniteReductionBoundedAbove k l E n).FullSubcategory,
        pointFiniteReductionBoundedAbove k l E j
          ((pointFiniteReductionSheafTensor k l E n j hjn).obj N.obj) ∧
        ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pointFiniteReductionModuleTensor l E n j hjn).obj
              ((pointFiniteReductionSections k l E n).obj N.obj)))) := by
  sorry

/-- Flat-complex model, generator normalization, and counit compatibility.
Source: Steps 5, 6 and 8 of the parent proof.
(blueprint: lem-trf-point-sections-finite-reduction-complex).

Proof: apply the degreewise quotient-to-sections map to a bounded-above termwise flat complex.
The balanced tensor associator proves the pure tensor generator equation, while the universal
counits and localization factors give the displayed counit square.
-/
theorem point_sections_finite_reduction_complex (_hl : IsUnit (l : k))
    (e : ∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙ pointFiniteReductionSections k l E j) :
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      ∀ (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
        (_hbound : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (P.X q))
        (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pointFiniteReductionRingSheaf k l E n) (P.X q)),
      ∃ hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P),
      ∃ q :
        (pointFiniteReductionComplexTensor l E n j hjn).obj
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≅
        (pointFiniteReductionSectionComplex k l E j).obj
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P),
      (∀ (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
        (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj (P.X a)),
        q.hom.f a
          (pointFiniteReductionTensorGenerator l E n j hjn
            ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x) =
          (b * c) • pointFiniteReductionSectionGenerator k l E n j hjn (P.X a) x) ∧
      (pointFiniteReductionModuleTensor l E n j hjn).map
          (pointFiniteReductionSectionFactors k l E n P).hom ≫
        (pointFiniteReductionModuleCounit l E n j hjn).app
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≫
        DerivedCategory.Q.map q.hom =
      (e n j hn hj hjn).hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≫
        (pointFiniteReductionSections k l E j).map
          (pointFiniteReductionSheafCounit k l E n j hjn P) ≫
        (pointFiniteReductionSectionFactors k l E j
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P)).hom := by
  sorry


/-- Sections at an algebraically closed point commute canonically with finite reduction.
Source: blueprint `prop-trf-adic-coefficient-morphism-systems.proof.md`, Proof (1);
Stacks Tags 093J, 00HD, 064L, 06YY and 06Y6
(blueprint: lem-trf-point-sections-finite-reduction).

The tensor-generator normalization specifies the canonical comparison on every
bounded-above flat representative. It encodes the unit and successive-reduction
clauses without introducing arbitrary unit or associativity isomorphisms: for j=n
it sends x to x; for n >= j >= i both iterated and direct reductions send the class
of x to its quotient section. The universal counits transport these equalities to
D(A_i), under the usual tensor unit and associativity identifications.

Proof (the node's eight steps):
1. The DVR theorem (lem-weil-l-adic-extension-integers-dvr) shows every ideal is (pi^r),
   with presentation
   A_n/(pi^(n-r)); this includes the whole and zero ideals and proves Noetherianity.
2. Use lem-cbc-continuous-functions-fpqc-sheaf and
   lem-weil-pbc-constant-module-section-properties. Continuous functions to a discrete
   ring form the constant ring sheaf by gluing
   on their open fibres. Its sections on Spec k are the coefficient ring itself.
   Constant exactness and the balanced tensor maps identify reduction with F/pi^j F.
   Exact sections of the image and cokernel sequences identify Gamma(F)/pi^j Gamma(F)
   with Gamma(F/pi^j F), by the actual quotient-section map.
3. Use def-pc-flat-sheaf-modules and lem-weil-pbc-flat-fg-ideal-criterion.
   For each ideal (pi^r), flatness of F and exact sections give injectivity of
   (pi^r) tensor Gamma(F) into Gamma(F). The finitely generated ideal criterion
   proves flatness of Gamma(F).
4. Use lem-pc-kflat-bounded-flat-replacement, lem-pc-bounded-above-flat-kflat-site
   and lem-pc-module-bounded-flat-kflat. Good truncation gives a bounded-above
   representative. Bounded flat replacement
   gives P with flat terms; P and Gamma(P) are K-flat by the site and module criteria.
5. Use lem-pur-derived-change-of-rings and lem-pc-derived-tensor-second-factor-functor.
   Both derived reductions are computed by their universal counits on these models.
   The degreewise quotient-section map is a chain isomorphism and preserves A_j actions.
6. Use lem-weil-pbc-bounded-below-cochain-localization and
   lem-weil-pbc-localization-universal-property. Functorial flat replacement and its
   natural augmentation give commuting squares
   for chain maps and inverted quasi-isomorphisms. Bounded-above localization, obtained
   by opposite-category degree reversal from bounded-below localization, descends
   these squares. Comparing any other flat model through its replacement proves
   resolution independence and the displayed normalization on every flat model.
7. P tensor A_j stays bounded above and termwise flat over (A_j)_t; the balanced
   tensor associator proves flatness. Its sections remain flat. Thus successive
   reductions use the same flat model and stay in the bounded-above domain.
8. For j=n the quotient-section map is the identity. For n >= j >= i the tensor
   associator sends ((x tensor b) tensor c) to x tensor bc. Both paths send [[x]]
   to the same quotient section. They agree degreewise and descend through the
   canonical counits to the claimed identity and successive-reduction compatibility.
-/
theorem point_sections_finite_reduction (_hl : IsUnit (l : k)) :
    ∃ e : ∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙ pointFiniteReductionSections k l E j,
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      (∀ N : (pointFiniteReductionBoundedAbove k l E n).FullSubcategory,
        pointFiniteReductionBoundedAbove k l E j
          ((pointFiniteReductionSheafTensor k l E n j hjn).obj N.obj) ∧
        ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pointFiniteReductionModuleTensor l E n j hjn).obj
              ((pointFiniteReductionSections k l E n).obj N.obj)))) ∧
      ∀ (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
        (_hbound : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (P.X q))
        (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pointFiniteReductionRingSheaf k l E n) (P.X q)),
      ∃ hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P),
      ∃ q :
        (pointFiniteReductionComplexTensor l E n j hjn).obj
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≅
        (pointFiniteReductionSectionComplex k l E j).obj
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P),
      (∀ (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
        (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj (P.X a)),
        q.hom.f a
          (pointFiniteReductionTensorGenerator l E n j hjn
            ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x) =
          (b * c) • pointFiniteReductionSectionGenerator k l E n j hjn (P.X a) x) ∧
      (pointFiniteReductionModuleTensor l E n j hjn).map
          (pointFiniteReductionSectionFactors k l E n P).hom ≫
        (pointFiniteReductionModuleCounit l E n j hjn).app
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≫
        DerivedCategory.Q.map q.hom =
      (e n j hn hj hjn).hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≫
        (pointFiniteReductionSections k l E j).map
          (pointFiniteReductionSheafCounit k l E n j hjn P) ≫
        (pointFiniteReductionSectionFactors k l E j
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P)).hom := by
  obtain ⟨e⟩ := point_sections_finite_reduction_iso k l E _hl
  refine ⟨e, ?_⟩
  intro n j hn hj hjn
  constructor
  · exact point_sections_finite_reduction_bounded k l E _hl n j hn hj hjn
  · exact point_sections_finite_reduction_complex k l E _hl e n j hn hj hjn


end WeilConjectures
