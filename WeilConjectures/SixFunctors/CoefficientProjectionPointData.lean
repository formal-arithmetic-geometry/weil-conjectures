/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
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
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.SixFunctors.CoefHomTowerScalarModel
public import WeilConjectures.SixFunctors.CoefficientProjectionAdjunctionData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! # Coefficient point tensor and sections data

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2;
Stacks 07A4, 07A6, 08J9, 0D6D, 0B56
(blueprint: def-sf-coefficient-projection-point-data).
-/

@[expose] public noncomputable section
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u a b v w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Commutative presentation of the actual quotient ring tower.
Source: Stacks 0941 (blueprint: def-sf-coefficient-projection-point-data). -/
def pointRing : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    (fun n ↦ CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift)

/-- Forgetting commutativity returns the prescribed quotient ring tower.
Source: Stacks 0941 (blueprint: def-sf-coefficient-projection-point-data).
Proof: objectwise both rings are the lifted quotient at exponent n + 1. On the
successor arrows both are the same lifted quotient homomorphism; functoriality
then proves equality on every arrow. -/
theorem pointRing_forget : pointRing l E ⋙ forget₂ CommRingCat RingCat =
    coefHomPointQuotientRing.{u, u} l E := by
  let τ : pointRing l E ⋙ forget₂ CommRingCat RingCat ⟶
      coefHomPointQuotientRing.{u, u} l E :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [Functor.comp_map, pointRing, coefHomPointQuotientRing,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp]
      rfl)
  refine CategoryTheory.Functor.ext
    (F := pointRing l E ⋙ forget₂ CommRingCat RingCat)
    (G := coefHomPointQuotientRing.{u, u} l E) (fun _ ↦ rfl) ?_
  intro i j f
  simpa [τ] using τ.naturality f

/-- Transport of the existing pointwise tensor along an equality of coefficient presheaves.
Source: Stacks 03EK (blueprint: def-sf-coefficient-projection-point-data). -/
@[instance_reducible]
def ringMonoidal (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (R : ℕᵒᵖ ⥤ RingCat.{u + 1})
    (h : Q ⋙ forget₂ CommRingCat RingCat = R) :
    MonoidalCategory (PresheafOfModules.{u + 1} R) := by
  subst R
  infer_instance

/-- Pointwise tensor on the actual quotient-semilinear point towers.
Source: Stacks 03EK, 0941 (blueprint: def-sf-coefficient-projection-point-data). -/
@[instance_reducible]
def pointMonoidal : MonoidalCategory (coefHomQuotientPointModules.{u, u} l E) :=
  ringMonoidal (pointRing l E) (coefHomPointQuotientRing l E) (pointRing_forget l E)

attribute [instance] pointMonoidal

/-- Bilinearity of the pointwise quotient tensor.
Source: Stacks 03EK (blueprint: def-sf-coefficient-projection-point-data).
Proof: evaluate at each n. The four bilinearity laws are those of ordinary
module tensor maps on pure tensors. Extensionality gives the diagram laws. -/
theorem pointPreadditive_exists :
    MonoidalPreadditive (coefHomQuotientPointModules.{u, u} l E) := by
  have transport (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (R : ℕᵒᵖ ⥤ RingCat.{u + 1})
      (h : Q ⋙ forget₂ CommRingCat RingCat = R) :
      @MonoidalPreadditive (PresheafOfModules.{u + 1} R) _ _ (ringMonoidal Q R h) := by
    subst R
    change @MonoidalPreadditive _ _ _ PresheafOfModules.monoidalCategory
    constructor
    all_goals
      dsimp only [autoParam]
      intros
      apply PresheafOfModules.hom_ext
      intro n
      simp
  exact transport (pointRing l E) _ (pointRing_forget l E)

/-- Bilinearity witness for the recorded point tensor.
Source: Stacks 03EK (blueprint: def-sf-coefficient-projection-point-data). -/
instance pointPreadditive : MonoidalPreadditive (coefHomQuotientPointModules.{u, u} l E) :=
  pointPreadditive_exists l E

/-- The actual constant integral ring tensor on point towers.
Source: Stacks 03EK, 0941 (blueprint: def-sf-coefficient-projection-point-data). -/
abbrev integralPointMonoidal : MonoidalCategory (coefHomPointModules.{u, u} l E) :=
  inferInstance

/-- The canonical ordinary quotient-system tensor.
Source: Stacks 03EK (blueprint: def-sf-coefficient-projection-point-data). -/
instance systemMonoidal (W : Scheme.{u}) :
    MonoidalCategory (coefficientSequenceModules.{u, u} l E W) :=
  cochainModulesMonoidal (coefficientSequenceCommRingSheaf l E W)

/-- Bilinearity of the canonical quotient-system tensor.
Source: Stacks 03EK (blueprint: def-sf-coefficient-projection-point-data). -/
instance systemPreadditive (W : Scheme.{u}) :
    MonoidalPreadditive (coefficientSequenceModules.{u, u} l E W) :=
  cochainModulesPreadditive (coefficientSequenceCommRingSheaf l E W)

/-- Actual pure tensors in the coefficient-presheaf tensor after ring transport.
Source: Stacks 03EK (blueprint: def-sf-coefficient-projection-point-data). -/
def ringTensorSection (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (R : ℕᵒᵖ ⥤ RingCat.{u + 1})
    (h : Q ⋙ forget₂ CommRingCat RingCat = R)
    (M N : PresheafOfModules.{u + 1} R) (n : ℕᵒᵖ) (x : M.obj n) (y : N.obj n) :
    ((ringMonoidal Q R h).tensorObj M N).obj n := by
  subst R
  exact x ⊗ₜ[Q.obj n] y

/-- Quotient-system point sections' actual ordinary lax tensor, specified on local
pure tensors at every positive coefficient level. The target retains quotient actions.
Source: Stacks 03EK, 0B56 (blueprint: def-sf-coefficient-projection-point-data). -/
structure SectionsTensor (W : Scheme.{u}) where
  map : ∀ M N : coefficientSequenceModules.{u, u} l E W,
    (coefHomQuotientSections l E W).obj M ⊗ (coefHomQuotientSections l E W).obj N ⟶
      (coefHomQuotientSections l E W).obj (M ⊗ N)
  pure : ∀ (M N : coefficientSequenceModules.{u, u} l E W) (n : ℕ)
    (x : ((coefHomQuotientSections l E W).obj M).obj (op n))
    (y : ((coefHomQuotientSections l E W).obj N).obj (op n)),
    HEq (((map M N).app (op n))
      (ringTensorSection (pointRing l E) (coefHomPointQuotientRing l E)
        (pointRing_forget l E) _ _ (op n) x y))
      (SemilinearSections.tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W) M N
        (op (n, ProEt.mk (𝟙 W))) x y)

/-- The actual direct-image lax tensor on the quotient sequence sites.
Its sections are pure tensors at the same base-changed object, including every
horizontal quotient-semilinear restriction.
Source: Stacks 03EK, 0B56 (blueprint: def-sf-coefficient-projection-point-data). -/
structure PushTensor {X Y : Scheme.{u}} (f : X ⟶ Y) where
  map : ∀ M N : coefficientSequenceModules.{u, u} l E X,
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f).obj M ⊗
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f).obj N ⟶
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f).obj (M ⊗ N)
  pure : ∀ (M N : coefficientSequenceModules.{u, u} l E X)
    (V : (ℕ × Y.ProEt)ᵒᵖ)
    (x : ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f).obj M).val.obj V)
    (y : ((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f).obj N).val.obj V),
    HEq (((map M N).val.app V)
      (SemilinearSections.tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf.{u, u} l E Y) _ _ V x y))
      (SemilinearSections.tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf.{u, u} l E X) M N
        ((ProEtale.VaryingRing.baseChange f).op.obj V) x y)

/-- The scalar-restriction lax tensor sends local pure tensors to their balanced
quotient tensor, preserving the point-tower transitions.
Source: Stacks 03EK, 0B56 (blueprint: def-sf-coefficient-projection-point-data). -/
structure RestrictionTensor where
  map : ∀ H B : coefHomQuotientPointModules.{u, u} l E,
    (coefHomPointRestriction l E).obj H ⊗ (coefHomPointRestriction l E).obj B ⟶
      (coefHomPointRestriction l E).obj (H ⊗ B)
  pure : ∀ (H B : coefHomQuotientPointModules.{u, u} l E) (n : ℕ)
    (x : ((coefHomPointRestriction l E).obj H).obj (op n))
    (y : ((coefHomPointRestriction l E).obj B).obj (op n)),
    HEq (((map H B).app (op n)) (x ⊗ₜ y))
      (ringTensorSection (pointRing l E) (coefHomPointQuotientRing l E)
        (pointRing_forget l E) H B (op n) x y)

/-- The exact scalar-restriction localization comparison, with its true point-tower values.
Source: Stacks 07A6 (blueprint: def-sf-coefficient-projection-point-data). -/
def restrictionUnit :
    (coefHomPointRestriction.{u, u} l E).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ coefHomPointDerivedRestriction l E :=
  (coefHomPointRestriction l E).mapDerivedCategoryFactors.inv

/-- The constant-integral tensor on point towers is bilinear.
Source: Stacks 03EK (blueprint: def-sf-coefficient-projection-point-data). -/
instance integralPointPreadditive : MonoidalPreadditive (coefHomPointModules.{u, u} l E) :=
  inferInstance

/-- Tensor on the quotient point derived category, fixed by localization of the actual
pointwise module tensor. The symmetry is required to be the signed swap on complexes.
Source: Stacks 06YN, 06YT, 0FPT (blueprint: def-sf-coefficient-projection-point-data). -/
structure PointTensor where
  [quotient : MonoidalCategory (DerivedCategory (coefHomQuotientPointModules.{u, u} l E))]
  quotientLocalization : TensorLocalization (MonoidalCategory.tensor
    (DerivedCategory (coefHomQuotientPointModules.{u, u} l E)))
  [integral : MonoidalCategory (DerivedCategory (coefHomPointModules.{u, u} l E))]
  integralLocalization : TensorLocalization (MonoidalCategory.tensor
    (DerivedCategory (coefHomPointModules.{u, u} l E)))


/-- Signed summand generator for quotient point complexes.
Source: Stacks 06YN (blueprint: def-sf-coefficient-projection-point-data). -/
def pointGenerator (P Q : CochainComplex (coefHomQuotientPointModules.{u, u} l E) ℤ)
    (p q n : ℤ) (h : p + q = n) (i : ℕᵒᵖ)
    (x : (P.X p).obj i) (y : (Q.X q).obj i) :
    ((total.obj (P, Q)).X n).obj i :=
  ((HomologicalComplex.ιTensorObj P Q p q n h).app i)
    (ringTensorSection (pointRing l E) (coefHomPointQuotientRing l E)
      (pointRing_forget l E) (P.X p) (Q.X q) i x y)

/-- The point symmetry is the localization of the signed swap, on every total summand.
Source: Stacks 06YN, 0FPT (blueprint: def-sf-coefficient-projection-point-data). -/
structure PointSymmetry (T : PointTensor l E) where
  symmetry : @SymmetricCategory
    (DerivedCategory (coefHomQuotientPointModules.{u, u} l E)) _ T.quotient
  chain : ∀ P Q : CochainComplex (coefHomQuotientPointModules.{u, u} l E) ℤ,
    total.obj (P, Q) ≅ total.obj (Q, P)
  signed : ∀ P Q (p q n : ℤ) (h : p + q = n) (h' : q + p = n) (i : ℕᵒᵖ)
    (x : (P.X p).obj i) (y : (Q.X q).obj i),
    (((chain P Q).hom.f n).app i) (pointGenerator l E P Q p q n h i x y) =
      (p * q).negOnePow • pointGenerator l E Q P q p n h' i y x
  localization : ∀ P Q,
    (symmetry.toBraidedCategory.braiding (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj Q)).hom ≫ T.quotientLocalization.comparison.app (Q, P) =
      T.quotientLocalization.comparison.app (P, Q) ≫ DerivedCategory.Q.map (chain P Q).hom

/-- Base change of the terminal pro-etale object is canonically terminal.
Source: Stacks 0D6D (blueprint: def-sf-coefficient-projection-point-data). -/
def terminalPullback {X Y : Scheme.{u}} (a : X ⟶ Y) :
    (proEtaleBaseChange a).obj (ProEt.mk (𝟙 Y)) ≅ ProEt.mk (𝟙 X) :=
  (IsTerminal.isTerminalObj (proEtaleBaseChange a) (ProEt.mk (𝟙 Y))
    (MorphismProperty.Over.mkIdTerminal _ Y)).uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal _ X)

/-- Additivity of the prescribed native system direct image, at the actual site sizes.
Source: Stacks 03DA (blueprint: def-sf-coefficient-projection-point-data). -/
instance (priority := 2000) systemPushAdditive {X Y : Scheme.{u}} (a : X ⟶ Y) :
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a).Additive :=
  ProEtale.VaryingRing.push_additive _ _ a


/-- Additivity at the fixed site and coefficient universes, using the recorded witness.
Source: Stacks 0941 (blueprint: def-sf-coefficient-projection-point-data). -/
instance (priority := 2000) sectionsAdditive (W : Scheme.{u}) :
    (coefHomQuotientSections.{u, u} l E W).Additive :=
  coefHomQuotientSectionsAdditive l E W

/-- Normalized whole-derived composition of quotient point sections with direct image.
The ordinary normalization uses the actual terminal-object base-change map; the
comparison equation fixes its derived transformation on the localization units.
Source: Stacks 0D6D, 0D6E (blueprint: def-sf-coefficient-projection-point-data). -/
structure SectionsComposition {X Y : Scheme.{u}} (a : X ⟶ Y) where
  ordinary : ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) a ⋙ coefHomQuotientSections l E Y ≅
      coefHomQuotientSections l E X
  sections : ∀ (M : coefficientSequenceModules.{u, u} l E X) (n : ℕ)
    (x : (((ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a ⋙ coefHomQuotientSections l E Y).obj M).obj
        (op n))),
    HEq (((ordinary.hom.app M).app (op n)) x)
      ((M.val.map (Prod.mkHom (𝟙 n) (terminalPullback a).inv).op) x)
  derived : ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) a ⋙ coefHomQuotientDerivedSections l E Y ≅
      coefHomQuotientDerivedSections l E X
  normalization : @DerivedCompositionNormalization
    (coefficientSequenceModules.{u, u} l E X) _ _ _
    (coefficientSequenceModules.{u, u} l E Y) _ _ _
    (coefHomQuotientPointModules.{u, u} l E) _ _ _
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a) (systemPushAdditive l E a)
    (coefHomQuotientSections l E Y) (sectionsAdditive l E Y)
    (coefHomQuotientSections l E X) (sectionsAdditive l E X)
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a)
    (coefHomQuotientDerivedSections l E Y) (coefHomQuotientDerivedSections l E X)
    (rightUnit (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a))
    (rightUnit (coefHomQuotientSections l E Y))
    (rightUnit (coefHomQuotientSections l E X)) ordinary derived


/-- The quotient-point derived tensor, with its recorded monoidal structure.
Source: Stacks 06YT (blueprint: def-sf-coefficient-projection-point-data). -/
abbrev PointTensor.qTensor (T : PointTensor l E) :=
  @MonoidalCategory.tensor _ _ T.quotient

/-- The integral-point derived tensor, with its recorded monoidal structure.
Source: Stacks 06YT (blueprint: def-sf-coefficient-projection-point-data). -/
abbrev PointTensor.rTensor (T : PointTensor l E) :=
  @MonoidalCategory.tensor _ _ T.integral

end WeilConjectures.CoefProjectionEvaluation
