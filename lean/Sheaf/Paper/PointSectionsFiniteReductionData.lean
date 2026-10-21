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
set_option linter.unusedVariables false
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
noncomputable abbrev pointFiniteReductionRingSheaf (k : Type u) [Field k]
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

/-- The standard localization in the established point-sheaf Hom universe.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-finite-reduction-sheaf-model). -/
local instance (priority := 30000) pointFiniteReductionDataDerived (n : ℕ) :
    HasDerivedCategory.{u + 2} (pointFiniteReductionSheaves k l E n) :=
  HasDerivedCategory.standard _

/-- The canonical map of constant coefficient sheaves.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafMap (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionRingSheaf k l E n ⟶ pointFiniteReductionRingSheaf k l E j :=
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

attribute [local irreducible] pointFiniteReductionSheafExistence

/-- A typed presentation of the chosen ordinary and derived coefficient change.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction).
The fields retain the prescribed ordinary objects and maps, and the universal
derived pair with its K-flat computations. -/
structure PointFiniteReductionSheafModel (n j : ℕ) (h : j ≤ n) where
  /-- Ordinary extension. -/
  F : pointFiniteReductionSheaves k l E n ⥤ pointFiniteReductionSheaves k l E j
  /-- Its actual sheafified tensor objects. -/
  objEq : ∀ M, F.obj M = SheafOfModules.changeOfRings
    (pointFiniteReductionSheafMap k l E n j h) M
  /-- Its actual sheafified tensor maps. -/
  mapEq : ∀ {M N} (a : M ⟶ N), F.map a = eqToHom (objEq M) ≫
    SheafOfModules.changeOfRingsHom (pointFiniteReductionSheafMap k l E n j h) M a ≫
      eqToHom (objEq N).symm
  /-- Ordinary extension is additive. -/
  [additive : F.Additive]
  /-- Derived extension. -/
  T : DerivedCategory (pointFiniteReductionSheaves k l E n) ⥤
    DerivedCategory (pointFiniteReductionSheaves k l E j)
  /-- Its homotopy-category counit. -/
  ε : DerivedCategory.Qh ⋙ T ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  /-- The universal left-derived property. -/
  universal : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))
  /-- Derived extension is triangulated. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated
  /-- Computation on any K-flat complex. -/
  computes : ∀ P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
      (R := pointFiniteReductionRingSheaf k l E n) P →
      IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

attribute [instance] PointFiniteReductionSheafModel.additive

/-- The prescribed ordinary functor and its derived universal pair have a typed model.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-finite-reduction-sheaf-model).
Proof: unpack the existing universal change-of-rings witness and put its ordinary
functor, derived functor, counit, universal property and computations into the record. -/
theorem nonempty_pointFiniteReductionSheafModel (n j : ℕ) (h : j ≤ n) :
    Nonempty (PointFiniteReductionSheafModel k l E n j h) := by
  obtain ⟨F, hobj, hmap, hadd, _, _, T, ε, hu, ht, hc⟩ :=
    pointFiniteReductionSheafExistence k l E n j h
  exact ⟨{
    F := F
    objEq := hobj
    mapEq := hmap
    additive := hadd
    T := T
    ε := ε
    universal := hu
    triangulated := ht
    computes := hc }⟩

/-- The ordinary functor is fixed by its objects and maps, and the derived pair is fixed
up to the unique isomorphism compatible with its universal counit.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafModel (n j : ℕ) (h : j ≤ n) :
    PointFiniteReductionSheafModel k l E n j h :=
  (nonempty_pointFiniteReductionSheafModel k l E n j h).some

attribute [local irreducible] pointFiniteReductionSheafModel

/-- Ordinary sheaf scalar extension from the universal witness.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafExtension (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionSheaves k l E n ⥤ pointFiniteReductionSheaves k l E j :=
  (pointFiniteReductionSheafModel k l E n j h).F

/-- Additivity is part of the universal scalar-extension witness.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSheafExtensionAdditive (n j : ℕ) (h : j ≤ n) :
    (pointFiniteReductionSheafExtension k l E n j h).Additive :=
  (pointFiniteReductionSheafModel k l E n j h).additive

/-- Derived scalar extension, retaining the same universal witness as its counit.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafTensor (n j : ℕ) (h : j ≤ n) :
    DerivedCategory (pointFiniteReductionSheaves k l E n) ⥤
      DerivedCategory (pointFiniteReductionSheaves k l E j) :=
  (pointFiniteReductionSheafModel k l E n j h).T

/-- The homotopy counit of the chosen universal pair.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSheafEpsilon (n j : ℕ) (h : j ≤ n) :
    DerivedCategory.Qh ⋙ pointFiniteReductionSheafTensor k l E n j h ⟶
      (pointFiniteReductionSheafExtension k l E n j h).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  (pointFiniteReductionSheafModel k l E n j h).ε

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
    (pointFiniteReductionSheafEpsilon k l E n j h).app
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
noncomputable abbrev pointFiniteReductionSheafComplexTensor (n j : ℕ) (h : j ≤ n) :
    CochainComplex (pointFiniteReductionSheaves k l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionSheaves k l E j) ℤ :=
  (pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex (.up ℤ)

/-- Termwise point sections, with the fixed quotient-coefficient action.
Source: Stacks Tag 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionSectionComplex (n : ℕ) :
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
    ((pointFiniteReductionSheafModel k l E n j h).objEq M).symm).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) y

/-- The typed natural localization comparison for finite point sections.
Source: Stacks Tags 0946 and 014X (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSectionFactorsNat [IsAlgClosed k] (n : ℕ) :
    DerivedCategory.Q ⋙ pointFiniteReductionSections k l E n ≅
      pointFiniteReductionSectionComplex k l E n ⋙ DerivedCategory.Q :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapDerivedCategoryFactors

/-- The exact-sections localization comparison at a complex.
Source: Stacks Tag 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionSectionFactors [IsAlgClosed k] (n : ℕ)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) :
    (pointFiniteReductionSections k l E n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((pointFiniteReductionSectionComplex k l E n).obj P) :=
  (pointFiniteReductionSectionFactorsNat k l E n).app P

/-- Mathlib's bounded-above object property, specialized to the point sheaf category.
Source: blueprint Proof (1), Stacks Tag 064L
(blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionBoundedAbove (n : ℕ) :
    ObjectProperty (DerivedCategory (pointFiniteReductionSheaves k l E n)) :=
  (DerivedCategory.TStructure.t (C := pointFiniteReductionSheaves k l E n)).minus

variable [IsAlgClosed k]

end WeilConjectures
