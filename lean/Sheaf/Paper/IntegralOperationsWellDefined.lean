/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.IntegralReductionTowerUnrestricted
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import Mathlib.CategoryTheory.Localization.Prod
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # Well-definedness of integral pullback and completed tensor product

Source: Stacks Project, Tags 06YS, 06YT, 0G7E and 08TC; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9(4)
(blueprint: lem-pur-integral-operations-well-defined).

The natural-number level n denotes exponent n+1. All towers and their maps are
constructed before localization; the Roos complex uses termwise products and the
specified shifted cone. The final descent includes its natural comparison data.

## Main definitions

* `integralOperationsPullbackComplexFunctor`: strict finite pullback followed by Roos.
* `integralOperationsTensorComplexFunctor`: direct-sum finite tensor followed by Roos.

## Main statements

* `integralOperationsWellDefined`: quasi-isomorphism invariance and normalized descent.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 512

universe t u a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] constantSheaf HasDerivedCategory.standard

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The specified abelian sheafification in the coefficient universe.
Source: Stacks Tag 03DA (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance (priority := 2000) integralOperationsAbSheafify
    (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} W

/-- The corresponding locally bijective criterion in exactly the same coefficient size.
Source: Stacks Tag 03DA (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance (priority := 2000) integralOperationsAbLocallyBijective
    (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

/-- The finite module category at positive exponent n+1.
Source: Stacks Tag 06YL (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable abbrev integralOperationsFiniteModules (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) :=
  SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E W n)

/-- The pro-etale site is small relative to the coefficient universe.
Source: Stacks Tag 09A5 (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance integralOperationsSiteSmall (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _

/-- Standard localization for the commutative presentation of the same completed sheaf.
Source: Stacks Tag 05RU (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance integralOperationsCommHasDerivedCategory
    (W : AlgebraicGeometry.Scheme.{t}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (completedIntegralCommRingSheafUnrestricted l E W))) :=
  HasDerivedCategory.standard _

/-- The presheaf tensor structure for the same finite ring, with commutativity retained.
Source: Stacks Tag 03EK (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance integralOperationsFinitePresheafMonoidal
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    MonoidalCategory (PresheafOfModules.{max u (t + 1)}
      (integralCoefficientSheaf l E W n).obj) :=
  PresheafOfModules.monoidalCategory
    (R := (integralCoefficientCommRingSheaf l E W n).obj)

/-- The recorded sheaf tensor structure on finite coefficients.
Source: Stacks Tag 03EK (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance integralOperationsFiniteMonoidal (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
  letI : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  letI := integralCoefficientAbSheafify.{t, u} W
  letI := integralCoefficientAbLocallyBijective.{t, u} W
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E W n)

/-- Tensoring finite sheaves preserves zero maps in the first variable.
Source: Stacks Tag 03EK (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance integralOperationsFiniteTensorZero
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n)

/-- Tensoring finite sheaves preserves zero maps in the second variable.
Source: Stacks Tag 03EK (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance integralOperationsFiniteTensorObjZero
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) (M : integralOperationsFiniteModules l E W n) :
    ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (integralCoefficientCommRingSheaf l E W n) M

/-- Restriction along π_n, applied termwise, with unchanged underlying sheaves and maps.
Source: Stacks Tag 03DA (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsRestrict (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))).mapHomologicalComplex
          (ComplexShape.up ℤ)

/-- Finite-level pullback, along the canonical constant-section coefficient map.
Source: Stacks Tag 03D2 (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsLevelPullback {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :=
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- Additivity of the module inverse image.
Source: Stacks Tag 03D2 (blueprint: lem-pur-integral-operations-well-defined).
Proof: its right adjoint, sectionwise pushforward with restricted coefficient action,
is additive. The pullback/direct-image adjunction therefore makes the left adjoint
additive (the preadditive adjunction criterion). -/
@[instance]
theorem integralOperationsLevelPullback_additive {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) : (integralOperationsLevelPullback l E f n).Additive := by
  have : (AlgebraicGeometry.Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive := by
    constructor
    intro M N a b
    rfl
  exact (AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).left_adjoint_additive

/-- The nth pullback tower level Res_n f*(P_n), as a functor on complexes.
Source: Stacks Tags 03D2 and 06YT
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsPullbackLevel {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ) :=
  unrestrictedIntegralFiniteComplex l E Y n ⋙
    (integralOperationsLevelPullback l E f n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      integralOperationsRestrict l E X n

/-- The canonical generator in finite module pullback, given by its adjunction unit.
Source: Stacks Tag 03D2 (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsPullbackGenerator {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) (V : Y.ProEt) (x : M.val.obj (op V)) :=
  ((AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.app M).val.app
      (op V) x

/-- The pullback transitions are the unique natural chain maps carrying the generator
of a finite reduction to the generator of its next reduction. These are the maps
f⁻¹(x)⊗a ↦ f⁻¹(r_n)(f⁻¹(x))⊗ρ_n(a), with the completed scalar actions.
Source: Stacks Tags 03D2 and 06YT
(blueprint: lem-pur-integral-operations-well-defined).
Proof: on module Kan-extension generators use the given reduction r_n; reduce the
coefficient by ρ_n. The maps c_A commute with coefficient reduction because their
adjoints send each coefficient to its constant section. Thus the map is balanced,
linear over the completion, compatible with restrictions, and commutes with the
differential. Sheafification gives the chain maps. Naturality is the same equality
on generators. Conversely a completed-linear map with the unit equation has this
action on all scalar multiples of every Kan-extension generator: the completed
projection to A_(n+1) is locally surjective. Those generators locally generate the
sheafified pullback. Thus the unit equation determines the transition uniquely. -/
theorem integralOperationsPullbackTransition_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ∃! τ : integralOperationsPullbackLevel l E f (n + 1) ⟶
      integralOperationsPullbackLevel l E f n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i).val.obj (op V)),
        ((τ.app P).f i).val.app (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange f).obj V))
          (integralOperationsPullbackGenerator l E f (n + 1)
            (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i) V x) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
          ((((unrestrictedIntegralTransition l E Y n).app P).f i).val.app (op V) x) := by
  sorry

/-- The pullback transition, fixed uniquely by the module unit formula.
Source: Stacks Tag 03D2 (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsPullbackTransition
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsPullbackLevel l E f (n + 1) ⟶ integralOperationsPullbackLevel l E f n :=
  (integralOperationsPullbackTransition_existsUnique l E f n).exists.choose

/-- The direct-sum total tensor of the two finite reductions, with restricted action.
The total differential is d_P⊗1+(-1)^p 1⊗d_Q on the (p,q)-summand.
Source: Stacks Tags 012Z and 06YM
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsTensorLevel (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (CochainComplex (integralTowerModules l E W) ℤ) ×
      (CochainComplex (integralTowerModules l E W) ℤ) ⥤
        CochainComplex (integralTowerModules l E W) ℤ :=
  (unrestrictedIntegralFiniteComplex l E W n).prod
      (unrestrictedIntegralFiniteComplex l E W n) ⋙
    Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor
        (integralOperationsFiniteModules l E W n)).map₂CochainComplex) ⋙
        integralOperationsRestrict l E W n

/-- A sheafified pure tensor in the recorded finite-coefficient tensor product.
Source: Stacks Tag 03EK (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsTensorSection (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (M N : integralOperationsFiniteModules l E W n)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (MonoidalCategory.tensorObj M N).val.obj U :=
  letI : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  letI := integralCoefficientAbSheafify.{t, u} W
  letI := integralCoefficientAbLocallyBijective.{t, u} W
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  ((SheafOfModules.tensorObjIsoSheafification
    (R := integralCoefficientCommRingSheaf l E W n) M N).inv.val.app U)
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      ((MonoidalCategory.tensorObj M.val N.val).presheaf :
        W.ProEtᵒᵖ ⥤ AddCommGrpCat.{max u (t + 1)})).app U
        (x ⊗ₜ[(integralCoefficientCommRingSheaf l E W n).obj.obj U] y))

/-- A tensor generator in the (p,q)-summand of the direct-sum total tensor complex.
Source: Stacks Tags 012Z and 03EK
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsTotalTensorSection (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :=
  (CochainComplex.ιMapBifunctor
    ((unrestrictedIntegralFiniteComplex l E W n).obj P)
    ((unrestrictedIntegralFiniteComplex l E W n).obj Q)
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n))
    p q (p + q) rfl).val.app U
      (integralOperationsTensorSection l E W n
        (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p)
        (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q) U x y)

/-- The tensor tower transition is uniquely fixed on every direct-sum tensor generator.
Source: Stacks Tags 012Z, 03EK and 06YT
(blueprint: lem-pur-integral-operations-well-defined).
Proof: send x⊗y in degree (p,q) to r_n(x)⊗r_n(y). Coefficient compatibility makes
this balanced over A_(n+1) and linear over the completion. Form the direct-sum map
in each total degree; it commutes with d_P⊗1+(-1)^p 1⊗d_Q. Sheafification makes
it a chain map. Naturality in both input complexes is equality on generators.
Conversely pure tensors generate the presheaf tensor, sheafification extends their
equalities uniquely, and the coproduct injections jointly determine a map. This
proves uniqueness of the natural transformation. -/
theorem integralOperationsTensorTransition_existsUnique
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    ∃! τ : integralOperationsTensorLevel l E W (n + 1) ⟶
      integralOperationsTensorLevel l E W n,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (U : W.ProEtᵒᵖ)
        (x : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P).X p).val.obj U)
        (y : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q).X q).val.obj U),
        ((τ.app (P, Q)).f (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W (n + 1) P Q p q U x y) =
        integralOperationsTotalTensorSection l E W n P Q p q U
          ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)
          ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y) := by
  sorry

/-- The tensor transition with the uniquely prescribed pure-tensor formula.
Source: Stacks Tag 03EK (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsTensorTransition
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    integralOperationsTensorLevel l E W (n + 1) ⟶ integralOperationsTensorLevel l E W n :=
  (integralOperationsTensorTransition_existsUnique l E W n).exists.choose

section Roos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The transition maps of a strict tower of complexes.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined). -/
def integralOperationsTowerStep (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :=
  C.map (homOfLE (Nat.le_succ n)).op

/-- The Roos complex Cone(1-s)[-1], with products computed termwise.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsRoos (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  CochainComplex.mappingCocone
    (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C))

/-- A strict tower morphism gives the commutative square for 1-s.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined).
Proof: after the nth product projection both composites are
pr_n a_n - pr_(n+1) t_n a_n; naturality of a identifies t_n a_n with
 a_(n+1) t'_n. Product extensionality gives the square. -/
theorem integralOperationsRoos_square
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') :
    towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C) ≫
        Limits.Pi.map (fun n ↦ α.app (op n)) =
      Limits.Pi.map (fun n ↦ α.app (op n)) ≫
        towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
          (integralOperationsTowerStep C') := by
  apply Eq.symm
  apply towerTransitionEndomorphism_natural_backward
  intro n
  exact (α.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The induced map on the two shifted-cone summands is the diagonal product map.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsRoosMap
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') :
    integralOperationsRoos C ⟶ integralOperationsRoos C' :=
  (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom
      (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C))
      (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n)) (integralOperationsTowerStep C'))
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
      (Arrow.homMk (Limits.Pi.map (fun n ↦ α.app (op n)))
        (Limits.Pi.map (fun n ↦ α.app (op n))) (integralOperationsRoos_square α).symm))

/-- The diagonal product map preserves identities.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined).
Proof: the product map of identity components is identity; the mapping-cone map
and the shift preserve identity maps. -/
theorem integralOperationsRoosMap_id (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    integralOperationsRoosMap (𝟙 C) = 𝟙 (integralOperationsRoos C) := by
  have h : Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))) = 𝟙 _ := by
    apply Limits.Pi.hom_ext
    intro n
    simp
  have ha : Arrow.homMk (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
      (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
      (integralOperationsRoos_square (𝟙 C)).symm =
      𝟙 (Arrow.mk (towerTransitionEndomorphism
        (K := fun n ↦ C.obj (op n)) (integralOperationsTowerStep C))) := by
    apply Arrow.hom_ext <;> exact h
  change (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
        (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
        (Arrow.homMk (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
          (Limits.Pi.map (fun n ↦ 𝟙 (C.obj (op n))))
          (integralOperationsRoos_square (𝟙 C)).symm)) = _
  erw [ha, HomologicalComplex.homotopyCofiber.mapArrowHom_id]
  exact (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map_id _

/-- The diagonal product map preserves composition.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined).
Proof: composition of product maps is the product of componentwise composites;
the mapping-cone map and shift preserve composition. -/
theorem integralOperationsRoosMap_comp
    {C C' C'' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') (β : C' ⟶ C'') :
    integralOperationsRoosMap (α ≫ β) =
      integralOperationsRoosMap α ≫ integralOperationsRoosMap β := by
  unfold integralOperationsRoosMap
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  congr 2
  apply Arrow.hom_ext <;> apply Limits.Pi.hom_ext <;> intro n <;> simp

/-- The functorial strict-complex Roos construction; this makes no choice of cones
in a bare triangulated category.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsRoosFunctor :
    (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj := integralOperationsRoos
  map := integralOperationsRoosMap
  map_id := integralOperationsRoosMap_id
  map_comp := integralOperationsRoosMap_comp

end Roos

/-- Countable products of completed-coefficient module sheaves.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable instance integralOperationsCountableProducts (W : AlgebraicGeometry.Scheme.{t}) :
    HasCountableProducts (integralTowerModules l E W) :=
  (AlgebraicGeometry.Scheme.ProEt.countableProducts_exact.{t, u, 0} W
    (completedIntegralCommRingSheafUnrestricted l E W)).1

/-- Countable products in the derived category are represented by termwise products.
Source: Stacks Tag 07KC (blueprint: lem-pur-integral-operations-well-defined).
Proof: countable products of completed-coefficient module sheaves are exact by
lem-weil-proetale-countable-products-exact. Apply clause (2) of
lem-weil-derived-limit-existence; its product comparison identifies every termwise
product with the derived-category product, and supplies HasCountableProducts. -/
@[instance]
theorem integralOperationsDerivedCountableProducts (W : AlgebraicGeometry.Scheme.{t}) :
    HasCountableProducts (DerivedCategory (integralTowerModules l E W)) := by
  let : HasFiniteBiproducts (integralTowerModules l E W) := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ)
      (C := integralTowerModules l E W)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (AlgebraicGeometry.Scheme.ProEt.countableProducts_exact.{t, u, 0} W
          (completedIntegralCommRingSheafUnrestricted l E W)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Limits.Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi (integralTowerModules l E W) (Discrete ℕ)
  have := CountableAB4Star.of_hasExactLimitsOfShape_nat (integralTowerModules l E W)
  exact (derivedCategory_countableProducts_core.{0}
    (integralTowerModules l E W)).choose

/-- The strict pullback tower, functorial in the input complex.
Source: Stacks Tags 03D2 and 06YT
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsPullbackTowerFunctor
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :=
  (Functor.ofOpSequence (X := fun n ↦ integralOperationsPullbackLevel l E f n)
    (integralOperationsPullbackTransition l E f)).flip

/-- The strict total-tensor tower, functorial in both input complexes.
Source: Stacks Tags 012Z and 06YT
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsTensorTowerFunctor (W : AlgebraicGeometry.Scheme.{t}) :=
  (Functor.ofOpSequence (X := fun n ↦ integralOperationsTensorLevel l E W n)
    (integralOperationsTensorTransition l E W)).flip

/-- T_f(P)=Cone(1-s)[-1] on the strict tower Res_n f*(P_n).
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsPullbackComplexFunctor
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :=
  integralOperationsPullbackTowerFunctor l E f ⋙ integralOperationsRoosFunctor

/-- T(P,Q)=Cone(1-s)[-1] on the strict tower of restricted finite total tensors.
Source: Stacks Tags 012Z and 08TC
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsTensorComplexFunctor (W : AlgebraicGeometry.Scheme.{t}) :=
  integralOperationsTensorTowerFunctor l E W ⋙ integralOperationsRoosFunctor

/-- The full subcategory of K-flat complexes with flat terms, without a boundedness condition.
Source: Stacks Tags 06YN and 03ER
(blueprint: lem-pur-integral-operations-well-defined). -/
def integralOperationsGoodComplex (W : AlgebraicGeometry.Scheme.{t}) :
    ObjectProperty (CochainComplex (integralTowerModules l E W) ℤ) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (R := completedIntegralCommRingSheafUnrestricted l E W) P ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)

/-- Localization of the full subcategory of good representatives into D(W_proet,O_E).
Source: Stacks Tags 06YS and 06YT
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsGoodLocalization (W : AlgebraicGeometry.Scheme.{t}) :=
  (integralOperationsGoodComplex l E W).ι ⋙ DerivedCategory.Q

/-- The complex pullback construction on the good representative subcategory, localized.
Source: Stacks Tags 06YT and 08TC
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsPullbackOnGood
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :=
  (integralOperationsGoodComplex l E Y).ι ⋙
    integralOperationsPullbackComplexFunctor l E f ⋙ DerivedCategory.Q

/-- The total tensor construction on pairs of good representatives, localized.
Source: Stacks Tags 06YT and 08TC
(blueprint: lem-pur-integral-operations-well-defined). -/
noncomputable def integralOperationsTensorOnGood (W : AlgebraicGeometry.Scheme.{t}) :=
  ((integralOperationsGoodComplex l E W).ι.prod
    (integralOperationsGoodComplex l E W).ι) ⋙
      integralOperationsTensorComplexFunctor l E W ⋙ DerivedCategory.Q

/-- The Roos derived-limit property of the actual strict tower, using its localized
transition maps and the chosen product in the derived category.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-well-defined). -/
def integralOperationsDerivedLimitProperty (W : AlgebraicGeometry.Scheme.{t})
    (C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ)
    (K : DerivedCategory (integralTowerModules l E W)) : Prop :=
  IsDerivedLimit (K := fun n ↦ DerivedCategory.Q.obj (C.obj (op n)))
    (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n)) K

-- Prefer the exact completed-module presentation during private proof search.
attribute [local instance 3000] integralTowerHasDerivedCategory

section IntegralOperationsRoosQuasiIsoInvariantProof

attribute [local irreducible] limit



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite



private theorem cofiberMap_eq_coneMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {K L K' L' : CochainComplex A ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      CochainComplex.mappingCone.map s s' a b h := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X s (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain,
    CochainComplex.HomComplex.Cochain.comp_v, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd,
    CochainComplex.mappingCone.inr]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A levelwise quasi-isomorphism induces a quasi-isomorphism of strict Roos complexes.
Source: Stacks Project, Derived Categories, Tags 07KC, 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: exact countable products make the product of the component maps a
quasi-isomorphism. The commutative square for 1-s gives a morphism of the
mapping-cone triangles. Its first two components become isomorphisms under
localization, so the third does as well. Reflection by localization and shift
invariance give the assertion for the recorded diagonal shifted-cone map. -/
private theorem roosMap_quasiIso
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (α : C ⟶ C') (hα : ∀ n : ℕ, QuasiIso (α.app (op n))) :
    QuasiIso (integralOperationsRoosMap α) := by
  classical
  let p := Limits.Pi.map (fun n ↦ α.app (op n))
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans (F := Discrete.functor (fun n ↦ C.obj (op n)))
        (G := Discrete.functor (fun n ↦ C'.obj (op n)))
        (fun n ↦ α.app (op n.as))).app n) := hα n.as
  have hp : QuasiIso p := HomologicalComplex.quasiIso_limMap _
  let s := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
    (integralOperationsTowerStep C)
  let s' := towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
    (integralOperationsTowerStep C')
  let τ := CochainComplex.mappingCone.triangleMap s s' p p
    (integralOperationsRoos_square α)
  have hc : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.map s s' p p
      (integralOperationsRoos_square α))) :=
    Pretriangulated.isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished s)
      (DerivedCategory.mappingCone_triangle_distinguished s')
      (inferInstance : IsIso (DerivedCategory.Q.map p))
      (inferInstance : IsIso (DerivedCategory.Q.map p))
  have hcone : QuasiIso (CochainComplex.mappingCone.map s s' p p
      (integralOperationsRoos_square α)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hc
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square α)]
  infer_instance


private theorem integralOperationsRoosQuasiIsoInvariant (W : AlgebraicGeometry.Scheme.{t})
    {C C' : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ}
    (α : C ⟶ C') (hα : ∀ n : ℕ, QuasiIso (α.app (op n))) :
    QuasiIso (integralOperationsRoosMap α) := by
  classical
  let A := integralTowerModules l E W
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (AlgebraicGeometry.Scheme.ProEt.countableProducts_exact.{t, u, 0} W
          (completedIntegralCommRingSheafUnrestricted l E W)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Limits.Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  exact roosMap_quasiIso α hα


end IntegralOperationsRoosQuasiIsoInvariantProof

section IntegralOperationsPullbackQuasiIsoInvariantProof

attribute [local irreducible] limit


set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite


attribute [local irreducible] SheafOfModules.monoidalCategory
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence



set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRestriction_exact
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J RingCat.{u}} (φ : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} φ) := by
  let U := SheafOfModules.restrictScalars.{u} φ
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S))
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf R)⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteReduction_quasiIso
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    {P Q : CochainComplex (integralTowerModules l E W) ℤ} (α : P ⟶ Q)
    (hP : (integralOperationsGoodComplex l E W) P)
    (hQ : (integralOperationsGoodComplex l E W) Q) (hα : QuasiIso α) :
    QuasiIso ((unrestrictedIntegralFiniteComplex l E W n).map α) := by
  let H := unrestrictedIntegralReductionExistence l E W n
  have h := H.choose_spec.choose_spec.choose_spec.choose_spec.1 (P := P) (Q := Q) α
  dsimp only [unrestrictedIntegralFiniteComplex, unrestrictedIntegralReductionFunctor,
    integralCoefficientSheaf, integralCoefficientCommRingSheaf]
  exact h hP.1 hQ.1 hα

set_option backward.isDefEq.respectTransparency false

/-- Pullback comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: reduction modulo the coefficient powers preserves quasi-isomorphisms of
K-flat complexes. Constant-coefficient pro-etale module inverse image is exact,
as is restriction of scalars, so every map in the strict pullback tower is a
quasi-isomorphism. Exact countable products and the mapping-cone triangle give
quasi-isomorphism invariance of the associated Roos complex. -/
private theorem integralOperationsPullbackQuasiIsoInvariant
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :
    ∀ (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (α : P.obj ⟶ P'.obj), QuasiIso α →
      QuasiIso ((integralOperationsPullbackComplexFunctor l E f).map α) := by
  intro P P' α hα
  apply integralOperationsRoosQuasiIsoInvariant l E X
  intro n
  change QuasiIso ((integralOperationsPullbackLevel l E f n).map α)
  let F := integralOperationsLevelPullback l E f n
  have : F.Additive := integralOperationsLevelPullback_additive l E f n
  have he := AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback_exact.{t,u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  have : PreservesFiniteLimits F := he.1
  have : PreservesFiniteColimits F := he.2
  let φ := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)
  let U := SheafOfModules.restrictScalars.{max u (t + 1)} φ
  have hU := coefficientRestriction_exact φ
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  have hR := finiteReduction_quasiIso l E Y n α P.property P'.property hα
  have hF := HomologicalComplex.quasiIso_map_of_preservesHomology
    ((unrestrictedIntegralFiniteComplex l E Y n).map α) F (hφ := hR)
  change QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map _)
  exact HomologicalComplex.quasiIso_map_of_preservesHomology _ U (hφ := hF)


end IntegralOperationsPullbackQuasiIsoInvariantProof

section IntegralOperationsTensorQuasiIsoInvariantProof

attribute [local irreducible] limit

attribute [local irreducible] SheafOfModules.monoidalCategory


set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite


attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence



private theorem finiteReduction_kFlat
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : (integralOperationsGoodComplex l E W) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P) := by
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let φ := completedIntegralCommRingProjectionUnrestricted l E W n
  let H := unrestrictedIntegralReductionExistence l E W n
  let F := H.choose
  have : F.Additive := H.choose_spec.choose_spec.choose_spec.choose
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  have hflat (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)) (hP.2 i)
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (R := R) (S := integralCoefficientCommRingSheaf l E W n)
    φ P F H.choose_spec.choose H.choose_spec.choose_spec.choose
    hP.1 hflat
  exact h.1

namespace IntegralTensorProof

universe x y z

open SheafOfModules MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem tensorTotals
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})]
    (R : Sheaf J CommRingCat.{z}) :
    let := monoidalCategory R
    ∀ K L : CochainComplex (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)) ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor _) (.up ℤ) := by
  let := monoidalCategory R
  intro K L
  infer_instance

open MonoidalCategory in
-- Additivity is the only part of closed tensor structure needed for descent.
private theorem tensorPreadditive
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})] (R : Sheaf J CommRingCat.{z}) :
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    MonoidalPreadditive (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let A := SheafOfModules.{z}
    ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)
  have (M : A) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

-- K-flatness kills the tensor of an acyclic mapping cone.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_right_quasiIso
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})]
    {R : Sheaf J CommRingCat.{z}}
    {E E' K : CochainComplex (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)) ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    let := monoidalCategory R
    letI := tensorTotals R
    QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K)
      (MonoidalCategory.curriedTensor _) (.up ℤ)) := by
  let := monoidalCategory R
  let := tensorTotals R
  let := tensorPreadditive R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso α K (MonoidalCategory.curriedTensor _))

-- The module braiding and signed total-complex flip give the other tensor order.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_left_quasiIso
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})]
    {R : Sheaf J CommRingCat.{z}}
    {K E E' : CochainComplex (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)) ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    let := monoidalCategory R
    letI := tensorTotals R
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α
      (MonoidalCategory.curriedTensor _) (.up ℤ)) := by
  let := monoidalCategory R
  let := tensorTotals R
  let := symmetricCategory R
  let := tensorPreadditive R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := MonoidalCategory.curriedTensor (SheafOfModules.{z}
    ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)

private theorem tensor_quasiIso
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z})] {R : Sheaf J CommRingCat.{z}}
    {E E' K K' : CochainComplex (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R)) ℤ}
    (α : E ⟶ E') (β : K ⟶ K') (hα : QuasiIso α) (hβ : QuasiIso β)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K)
    (hE' : CochainComplex.IsKFlatIndependentCoefficients (R := R) E') :
    let := monoidalCategory R
    letI := tensorTotals R
    QuasiIso ((Functor.uncurry.obj ((curriedTensor (SheafOfModules.{z}
      ((sheafCompose J (forget₂ CommRingCat.{z} RingCat.{z})).obj R))).map₂CochainComplex)).map
        (X := (E, K)) (Y := (E', K')) (α, β)) := by
  let := monoidalCategory R
  let := tensorTotals R
  exact quasiIso_comp _ _
    (hφ := tensor_right_quasiIso (R := R) α hα hK)
    (hφ' := tensor_left_quasiIso (R := R) β hβ hE')

end IntegralTensorProof

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteTensor_quasiIso
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    {P P' Q Q' : CochainComplex (integralTowerModules l E W) ℤ}
    (α : P ⟶ P') (β : Q ⟶ Q')
    (hP : (integralOperationsGoodComplex l E W) P)
    (hP' : (integralOperationsGoodComplex l E W) P')
    (hQ : (integralOperationsGoodComplex l E W) Q)
    (hQ' : (integralOperationsGoodComplex l E W) Q')
    (hα : QuasiIso α) (hβ : QuasiIso β) :
    QuasiIso ((Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor
        (integralOperationsFiniteModules l E W n)).map₂CochainComplex)).map
          (X := ((unrestrictedIntegralFiniteComplex l E W n).obj P,
            (unrestrictedIntegralFiniteComplex l E W n).obj Q))
          (Y := ((unrestrictedIntegralFiniteComplex l E W n).obj P',
            (unrestrictedIntegralFiniteComplex l E W n).obj Q'))
          ((unrestrictedIntegralFiniteComplex l E W n).map α,
            (unrestrictedIntegralFiniteComplex l E W n).map β)) := by
  exact IntegralTensorProof.tensor_quasiIso
    (C := W.ProEt) (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (R := integralCoefficientCommRingSheaf l E W n)
    ((unrestrictedIntegralFiniteComplex l E W n).map α)
    ((unrestrictedIntegralFiniteComplex l E W n).map β)
    (finiteReduction_quasiIso l E W n α hP hP' hα)
    (finiteReduction_quasiIso l E W n β hQ hQ' hβ)
    (finiteReduction_kFlat l E W n Q hQ)
    (finiteReduction_kFlat l E W n P' hP')


set_option backward.isDefEq.respectTransparency false

/-- Tensor comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: finite coefficient reduction preserves quasi-isomorphisms between K-flat
complexes, and preserves K-flatness and flat terms by tensor cancellation under
change of rings. Tensoring the acyclic mapping cone with the other K-flat
factor proves invariance of the finite total tensors. Restriction of scalars is exact, so every
level of the strict tower map is a quasi-isomorphism. Exact countable products and
the mapping-cone triangle imply quasi-isomorphism invariance of its Roos complex. -/
private theorem integralOperationsTensorQuasiIsoInvariant
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∀ (P P' Q Q' : (integralOperationsGoodComplex l E W).FullSubcategory)
      (α : P.obj ⟶ P'.obj) (β : Q.obj ⟶ Q'.obj), QuasiIso α → QuasiIso β →
      QuasiIso ((integralOperationsTensorComplexFunctor l E W).map
        (X := (P.obj, Q.obj)) (Y := (P'.obj, Q'.obj)) (α, β)) := by
  intro P P' Q Q' α β hα hβ
  apply integralOperationsRoosQuasiIsoInvariant l E W
  intro n
  change QuasiIso ((integralOperationsTensorLevel l E W n).map
    (X := (P.obj, Q.obj)) (Y := (P'.obj, Q'.obj)) (α, β))
  let φ := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)
  let U := SheafOfModules.restrictScalars.{max u (t + 1)} φ
  have hex := coefficientRestriction_exact φ
  have hULim : PreservesFiniteLimits U := hex.1
  have hUColim : PreservesFiniteColimits U := hex.2
  have hTensor := finiteTensor_quasiIso l E W n α β P.property P'.property
    Q.property Q'.property hα hβ
  change QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map _)
  exact HomologicalComplex.quasiIso_map_of_preservesHomology _ U (hφ := hTensor)


end IntegralOperationsTensorQuasiIsoInvariantProof

section IntegralOperationsGoodLocalizationProof

attribute [local irreducible] limit



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject



variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true in
private theorem acyclic_of_preserves_quasiIso
    {A : Type a} [Category.{b} A] [Abelian A]
    (T : CochainComplex A ℤ ⥤ CochainComplex A ℤ) [T.PreservesZeroMorphisms]
    (hT : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L),
      QuasiIso f → QuasiIso (T.map f))
    (Z : CochainComplex A ℤ) (hZ : Z.Acyclic) : (T.obj Z).Acyclic := by
  have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hm : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hT _ hz
  have hzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (hzero i)


set_option backward.isDefEq.respectTransparency true in
private theorem coreKFlat_tensor_acyclic
    {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasColimitsOfSize.{0, 0} A]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (K : CochainComplex A ℤ)
    (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K) :
    ∀ (Z : CochainComplex A ℤ), Z.Acyclic →
      (HomologicalComplex.mapBifunctor Z K (curriedTensor A) (.up ℤ)).Acyclic := by
  exact acyclic_of_preserves_quasiIso (tensorRight K) (fun f hf ↦ hK.2 f hf)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Good completed-coefficient complexes localize to the entire derived category.
Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YT.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: the canonical functorial flat cover gives a reduced left resolution functor.
Its filtered-colimit construction has flat terms and is K-flat, and its natural
augmentation is a quasi-isomorphism. The inclusion of good complexes is fully
faithful. The augmentation and its restriction to good complexes give inverse
localized functors, so the inclusion is a localized equivalence. Composing with
the standard derived localization gives the claimed localization. -/
private theorem goodComplexes_isLocalization
    {C : Type a} [Category.{b} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (hp : ∀ K, P K ↔ CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (K.X i)) :
    (P.ι ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage P.ι) := by
  classical
  let O := (sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let A := SheafOfModules.{u} O
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have (M : A) : PreservesColimitsOfSize.{u, u}
      (tensorLeft M) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
  have (M : A) : PreservesColimitsOfSize.{u, u}
      (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimitsOfSize_shrink (tensorRight M)
  have (M : A) : (tensorLeft M).Additive :=
    SheafOfModules.tensorLeft_additive_independent R M
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  let : MonoidalPreadditive A :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  have : HasExactColimitsOfShape ℤ A := by
    have := AB5OfSize_of_univLE.{0, 0, u, u}
      AddCommGrpCat.{u}
    exact HasExactColimitsOfShape.domain_of_functor ℤ (SheafOfModules.toSheaf O)
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).obj X) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R X
    infer_instance
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have : (ObjectProperty.flat (A := A)).ContainsZero := inferInstance
  have : IsIdempotentComplete (ObjectProperty.flat (A := A)).FullSubcategory :=
    inferInstance
  let : HasFiniteCoproducts (ObjectProperty.flat (A := A)).FullSubcategory := inferInstance
  let : HasZeroObject (ObjectProperty.flat (A := A)).FullSubcategory := inferInstance
  let : MonoidalCategory (CochainComplex A ℤ) := inferInstance
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ A).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  have hgood (K : CochainComplex A ℤ) :
      P (Λ.resolutionFunctor.obj K) := by
    let P := Λ.resolutionFunctor.obj K
    have hK := Λ.kFlat_resolutionFunctor_obj hι K
    have hflat (n : ℤ) : ObjectProperty.flat (P.X n) := by
      have := CochainComplex.closedUnderColimitsOfShape_flat A ℤ
      let c := Λ.colimitOfShapeResolutionFunctorObj K
      exact ObjectProperty.prop_of_isColimit _
        (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n) c.isColimit)
        (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))
    apply (hp _).2
    constructor
    · exact coreKFlat_tensor_acyclic P hK
    · intro i
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hflat i).2
  let C := P
  let V := (HomologicalComplex.quasiIso A (.up ℤ)).inverseImage C.ι
  let Q := HomologicalComplex.quasiIso A (.up ℤ)
  let Φ : LocalizerMorphism V Q := ⟨C.ι, fun _ _ _ hf ↦ hf⟩
  let ρ : CochainComplex A ℤ ⥤ C.FullSubcategory :=
    ObjectProperty.lift C Λ.resolutionFunctor hgood
  let ε : ρ ⋙ C.ι ⟶ 𝟭 _ := Λ.resolutionNatTrans
  have hε (K : CochainComplex A ℤ) : Q (ε.app K) := by
    change QuasiIso (Λ.resolutionNatTrans.app K)
    infer_instance
  have : Φ.IsInduced := ⟨rfl⟩
  have hΦ : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions ε hε rfl
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ DerivedCategory.Q


private theorem integralOperationsGoodLocalization_isLocalization
    (W : AlgebraicGeometry.Scheme.{t}) :
    (integralOperationsGoodLocalization l E W).IsLocalization
      ((HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
        (integralOperationsGoodComplex l E W).ι) := by
  exact goodComplexes_isLocalization
    (completedIntegralCommRingSheafUnrestricted l E W) (integralOperationsGoodComplex l E W)
    (fun _ ↦ Iff.rfl)


end IntegralOperationsGoodLocalizationProof

section IntegralOperationsTensorDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsPullbackOnGood

attribute [local irreducible] limit

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict integral tensor descends to the product of the derived categories.
Source: Stacks Project, Cohomology on Sites, Tags 06YT and 0G7E.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: good completed-coefficient complexes localize to the derived category, hence
pairs of good complexes localize to its product. Tensor quasi-isomorphism invariance
shows that the strict Roos tensor followed by derived localization inverts the
product class of quasi-isomorphisms. Apply the universal property of localization;
its factorization isomorphism gives the natural representative comparison. -/
private theorem integralOperationsTensorDescent (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W),
      Nonempty (((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W) := by
  have := integralOperationsGoodLocalization_isLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let L := integralOperationsGoodLocalization l E W
  let T := integralOperationsTensorOnGood l E W
  have hT : (V.prod V).IsInvertedBy T := by
    intro P Q f hf
    have h := integralOperationsTensorQuasiIsoInvariant l E W
      P.1 Q.1 P.2 Q.2 f.1.hom f.2.hom hf.1 hf.2
    dsimp only [T]
    unfold integralOperationsTensorOnGood
    change IsIso (DerivedCategory.Q.map
      ((integralOperationsTensorComplexFunctor l E W).map
        (X := (P.1.obj, P.2.obj)) (Y := (Q.1.obj, Q.2.obj)) (f.1.hom, f.2.hom)))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  exact ⟨Localization.lift T hT (L.prod L),
    ⟨Localization.fac T hT (L.prod L)⟩⟩


end IntegralOperationsTensorDescentProof

section IntegralOperationsComparisonExistsProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsPullbackOnGood

attribute [local irreducible] limit

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Existence of the natural localization comparisons for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: good complexes localize to the derived category using functorial flat
resolutions. The strict pullback functor sends quasi-isomorphisms between good
complexes to quasi-isomorphisms by exact finite pullback, finite reduction and
Roos invariance. Its derived localization therefore inverts the defining class,
and the localization universal property gives F with its natural comparison.
The separately proved tensor descent gives G with its natural comparison. -/
private theorem integralOperationsComparisonExists
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W)),
      Nonempty (integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f) ∧
      Nonempty (((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W) := by
  have := integralOperationsGoodLocalization_isLocalization l E Y
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let L := integralOperationsGoodLocalization l E Y
  let T := integralOperationsPullbackOnGood l E f
  have hT : V.IsInvertedBy T := by
    intro P Q a ha
    have h := integralOperationsPullbackQuasiIsoInvariant l E f P Q a.hom ha
    dsimp only [T]
    unfold integralOperationsPullbackOnGood
    change IsIso (DerivedCategory.Q.map
      ((integralOperationsPullbackComplexFunctor l E f).map a.hom))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  obtain ⟨G, d⟩ := integralOperationsTensorDescent l E W
  exact ⟨Localization.lift T hT L, G, ⟨Localization.fac T hT L⟩, d⟩


end IntegralOperationsComparisonExistsProof

section IntegralOperationsNormalizedDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsPullbackOnGood

attribute [local irreducible] limit

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted



set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite




variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem good_whisker_fullyFaithful (W : AlgebraicGeometry.Scheme.{t})
    (D : Type a) [Category.{b} D] :
    Nonempty (((whiskeringLeft _ _ D).obj
      (integralOperationsGoodLocalization l E W)).FullyFaithful) := by
  have := integralOperationsGoodLocalization_isLocalization l E W
  exact ⟨Localization.fullyFaithfulWhiskeringLeft
    (integralOperationsGoodLocalization l E W)
    ((HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E W).ι) D⟩

private theorem good_prod_whisker_fullyFaithful (W : AlgebraicGeometry.Scheme.{t})
    (D : Type a) [Category.{b} D] :
    Nonempty (((whiskeringLeft _ _ D).obj
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W))).FullyFaithful) := by
  have := integralOperationsGoodLocalization_isLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  exact ⟨Localization.fullyFaithfulWhiskeringLeft
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) (V.prod V) D⟩

private theorem unique_comparison
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (L : C ⥤ D) (hL : ((whiskeringLeft _ _ H).obj L).FullyFaithful)
    {T : C ⥤ H} {F F' : D ⥤ H} (e : L ⋙ F ≅ T) (e' : L ⋙ F' ≅ T) :
    ∃! i : F ≅ F', isoWhiskerLeft L i ≪≫ e' = e := by
  let i : F ≅ F' := hL.isoEquiv.symm (e ≪≫ e'.symm)
  have hi : isoWhiskerLeft L i = e ≪≫ e'.symm := hL.isoEquiv.apply_symm_apply _
  refine ⟨i, ?_, ?_⟩
  · change isoWhiskerLeft L i ≪≫ e' = e
    rw [hi]
    simp
  · intro j hj
    apply hL.isoEquiv.injective
    change isoWhiskerLeft L j = isoWhiskerLeft L i
    rw [hi]
    have h := congrArg (fun k ↦ k ≪≫ e'.symm) hj
    simpa using h

set_option backward.isDefEq.respectTransparency true in
/-- Localization descent comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: take the two descended functors and natural comparisons from
integralOperationsComparisonExists. The functorial flat resolution proves that good
complexes localize to the derived category. Precomposition with this localization
and with its product is fully faithful by the localization universal property.
For two representative
comparisons e and e', the image of the required isomorphism must be e followed by
the inverse of e'. The fully faithful whiskering functor lifts this isomorphism;
cancellation proves the compatibility equation, and faithfulness proves uniqueness.
Apply the same argument to the tensor product localization. -/
private theorem integralOperationsNormalizedDescent
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f)
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W))
      (d : ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W),
      (∀ (F' : DerivedCategory (integralTowerModules l E Y) ⥤
          DerivedCategory (integralTowerModules l E X))
        (e' : integralOperationsGoodLocalization l E Y ⋙ F' ≅
          integralOperationsPullbackOnGood l E f),
        ∃! ι : F ≅ F',
          isoWhiskerLeft (integralOperationsGoodLocalization l E Y) ι ≪≫ e' = e) ∧
      (∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
          (DerivedCategory (integralTowerModules l E W)) ⥤
            DerivedCategory (integralTowerModules l E W))
        (d' : ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
            integralOperationsTensorOnGood l E W),
        ∃! ι : G ≅ G', isoWhiskerLeft
          ((integralOperationsGoodLocalization l E W).prod
            (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = d) := by
  obtain ⟨F, G, ⟨e⟩, ⟨d⟩⟩ := integralOperationsComparisonExists l E f W
  refine ⟨F, e, G, d, ?_, ?_⟩
  · intro F' e'
    obtain ⟨hL⟩ := good_whisker_fullyFaithful l E Y
      (DerivedCategory (integralTowerModules l E X))
    exact unique_comparison _ hL e e'
  · intro G' d'
    obtain ⟨hL⟩ := good_prod_whisker_fullyFaithful l E W
      (DerivedCategory (integralTowerModules l E W))
    exact unique_comparison _ hL d d'


end IntegralOperationsNormalizedDescentProof

section IntegralOperationsRoosDerivedLimitProof


set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false


open CategoryTheory CategoryTheory.Limits Opposite




variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The localized strict Roos complex has the derived-limit triangle.
Source: Stacks Project, Derived Categories, Tags 07KC and 08TC.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: exact countable products identify the localized product complex, with its
projections, with the product in the derived category. Checking each projection
identifies the localized endomorphism 1-s with the derived-category endomorphism.
The localized mapping-cocone triangle is distinguished. Transport its two product
vertices along this product comparison to get the required Roos triangle. -/
private theorem roos_derivedLimit
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory A] [CountableAB4Star A]
    [HasCountableProducts (DerivedCategory A)]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      (DerivedCategory.Q.obj (integralOperationsRoos C)) := by
  classical
  let K := fun n : ℕ ↦ C.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  have hQP : IsLimit (DerivedCategory.Q.mapCone P) :=
    (derivedCategory_countableProducts_core.{0} A).choose_spec.1 ℕ K |>.some
  let KD := fun n : ℕ ↦ DerivedCategory.Q.obj (K n)
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K P) hQP
  let e : DerivedCategory.Q.obj P.pt ≅ ∏ᶜ KD :=
    hQFan.conePointUniqueUpToIso (productIsProduct KD)
  have he (n : ℕ) : e.hom ≫ Pi.π KD n = DerivedCategory.Q.map (P.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct KD) ⟨n⟩
  let s := towerTransitionEndomorphism (K := K) (integralOperationsTowerStep C)
  let sd := towerTransitionEndomorphism (K := KD)
    (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
  have hsπ (n : ℕ) : s ≫ P.proj n =
      P.proj n - P.proj (n + 1) ≫ integralOperationsTowerStep C n := by
    change s ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ _
    simp [s, towerTransitionEndomorphism, towerProductShift]
  have hs : DerivedCategory.Q.map s ≫ e.hom = e.hom ≫ sd := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, ← Functor.map_comp, hsπ, Functor.map_sub]
    simp only [sd, towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_π, he]
    rw [Functor.map_comp, ← Category.assoc, he]
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle s)
  have hT : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.mappingCocone_triangle_distinguished s
  refine ⟨T.mor₁ ≫ e.hom, e.inv ≫ T.mor₃, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk T
      (Pretriangulated.Triangle.mk (T.mor₁ ≫ e.hom) sd (e.inv ≫ T.mor₃))
      (Iso.refl _) e e (by simp) hs (by simp))).mp hT


private theorem integralOperationsRoosDerivedLimit (W : AlgebraicGeometry.Scheme.{t})
    (C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) :
    integralOperationsDerivedLimitProperty l E W C
      (DerivedCategory.Q.obj (integralOperationsRoos C)) := by
  classical
  let A := integralTowerModules l E W
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (AlgebraicGeometry.Scheme.ProEt.countableProducts_exact.{t, u, 0} W
          (completedIntegralCommRingSheafUnrestricted l E W)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Limits.Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  have := CountableAB4Star.of_hasExactLimitsOfShape_nat A
  exact roos_derivedLimit C


end IntegralOperationsRoosDerivedLimitProof

section IntegralOperationsDerivedDescentProof

attribute [local irreducible] limit

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted



set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite




variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency false in
private theorem derivedLimit_of_iso
    {A : Type*} [Category* A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {K : ℕ → A} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    {L L' : A} (e : L ≅ L') (h : IsDerivedLimit f L') : IsDerivedLimit f L := by
  obtain ⟨p, δ, h⟩ := h
  refine ⟨e.hom ≫ p, δ ≫ (shiftFunctor A (1 : ℤ)).map e.inv, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (e.hom ≫ p) (towerTransitionEndomorphism f)
        (δ ≫ (shiftFunctor A (1 : ℤ)).map e.inv))
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ)
      e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))).mpr h

set_option backward.isDefEq.respectTransparency true in
/-- Localization descent comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: obtain the descended functors, natural comparisons, and both uniqueness
assertions from integralOperationsNormalizedDescent. For any chosen representative
isomorphism, apply the descended functor to its inverse and compose with the
comparison at that representative. This identifies the functor's value with the
localized strict Roos complex. The latter satisfies the derived-limit property by
integralOperationsRoosDerivedLimit. Transport its distinguished triangle along the
identification; explicitly precompose the first map by the identification and
postcompose the third map by the shifted inverse. For tensor use the product of
the two representative isomorphisms and repeat the same argument. -/
private theorem integralOperationsDerivedDescent
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f)
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W))
      (d : ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W),
      (∀ (F' : DerivedCategory (integralTowerModules l E Y) ⥤
          DerivedCategory (integralTowerModules l E X))
        (e' : integralOperationsGoodLocalization l E Y ⋙ F' ≅
          integralOperationsPullbackOnGood l E f),
        ∃! ι : F ≅ F',
          isoWhiskerLeft (integralOperationsGoodLocalization l E Y) ι ≪≫ e' = e) ∧
      (∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
          (DerivedCategory (integralTowerModules l E W)) ⥤
            DerivedCategory (integralTowerModules l E W))
        (d' : ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
            integralOperationsTensorOnGood l E W),
        ∃! ι : G ≅ G', isoWhiskerLeft
          ((integralOperationsGoodLocalization l E W).prod
            (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = d) ∧
      (∀ (K : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ K),
        integralOperationsDerivedLimitProperty l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)
          (F.obj K)) ∧
      (∀ (M N : DerivedCategory (integralTowerModules l E W))
        (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ M) (_d : DerivedCategory.Q.obj Q.obj ≅ N),
        integralOperationsDerivedLimitProperty l E W
          ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
          (G.obj (M, N))) := by
  obtain ⟨F, e, G, d, hF, hG⟩ := integralOperationsNormalizedDescent l E f W
  refine ⟨F, e, G, d, hF, hG, ?_, ?_⟩
  · intro K P i
    let C := (integralOperationsPullbackTowerFunctor l E f).obj P.obj
    have h := integralOperationsRoosDerivedLimit l E X C
    let j : F.obj (DerivedCategory.Q.obj P.obj) ≅
        DerivedCategory.Q.obj (integralOperationsRoos C) := by
      have j := e.app P
      dsimp only [integralOperationsGoodLocalization, integralOperationsPullbackOnGood,
        Functor.comp_obj] at j
      unfold integralOperationsPullbackComplexFunctor at j
      exact j
    exact derivedLimit_of_iso (A := DerivedCategory (integralTowerModules l E X))
      (K := fun n : ℕ ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      ((F.mapIso i.symm) ≪≫ j) h
  · intro M N P Q i j
    let C := (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)
    have h := integralOperationsRoosDerivedLimit l E W C
    let ij : (M, N) ≅ (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) :=
      i.symm.prod j.symm
    let k : G.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≅
        DerivedCategory.Q.obj (integralOperationsRoos C) := by
      have k := d.app (P, Q)
      dsimp only [integralOperationsGoodLocalization, integralOperationsTensorOnGood,
        Functor.comp_obj] at k
      unfold integralOperationsTensorComplexFunctor at k
      exact k
    exact derivedLimit_of_iso (A := DerivedCategory (integralTowerModules l E W))
      (K := fun n : ℕ ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      ((G.mapIso ij) ≪≫ k) h


end IntegralOperationsDerivedDescentProof


attribute [local irreducible] limit

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsDerivedLimitProperty
  integralOperationsGoodComplex integralOperationsGoodLocalization
  integralOperationsPullbackOnGood integralOperationsTensorOnGood

/-- The two integral complex constructions preserve quasi-isomorphisms on K-flat
complexes with flat terms, descend to functors with natural representative comparisons,
and are unique up to the unique isomorphism compatible with those comparisons.
Their values are derived limits of the specified finite-level towers.
Source: Stacks Tags 06YS, 06YT, 0G7E, 08TC; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9(4)
(blueprint: lem-pur-integral-operations-well-defined).

Proof:
1. Apply lem-pur-change-of-rings-kflat-quasi-iso to each completed coefficient
projection. The induced reductions of u,v are quasi-isomorphisms; by
lem-pur-kflat-change-of-rings all reduced complexes remain K-flat with flat terms.
No flatness of the coefficient projection is required.
2. prop-weil-pbc-proetale-constant-exact makes finite-level module pullback exact,
so it preserves these quasi-isomorphisms for every scheme morphism f. The site
version lem-weil-pbc-site-derived-tensor-descent identifies total tensors on K-flat
representatives with derived tensors; functoriality then proves the same assertion
for the tensor of the two reduced quasi-isomorphisms.
3. Restriction of scalars leaves the abelian sheaf and its cohomology unchanged.
The maps are strict maps of towers: on a tensor generator reducing then applying
u is the same as applying u then reducing, and similarly for v. The pullback
structure maps commute with reduction since their adjoints are the constant-section
maps. Thus the displayed pullback and tensor transition formulas commute with u,v.
4. Exact countable products on pro-etale module sheaves identify the termwise
products with derived products (lem-weil-proetale-countable-products-exact and
lem-weil-derived-limit-existence). The shifted cone triangle is the Roos triangle
of def-weil-derived-limit, so each displayed value is a derived limit. The diagonal
product map is a morphism of Roos triangles. Its two product components are
isomorphisms; lem-weil-derived-limit-levelwise-iso makes its shifted-cone component
an isomorphism. Taking cohomology proves clause (1).
5. The complex constructions preserve identities and compositions. They respect
homotopies: additive coefficient change and inverse image preserve dh+hd. The total
tensor homotopy between u⊗v and u'⊗v' is h⊗v+(-1)^p u'⊗k on first degree p;
the mixed terms cancel. These homotopies commute with reduction. For the shifted
cone differential d(b,a)=(-db-(1-s)a,da), the product homotopy h gives
H(b,a)=(-hb,ha), and dH+Hd is the diagonal product difference.
6. lem-weil-pbc-site-derived-tensor-descent identifies localization of the good
homotopy representatives with the full derived category. Descend by
lem-weil-pbc-localization-universal-property, once for pullback and separately in
each variable for tensor. It extends natural transformations uniquely, giving the
natural comparisons e,d and their stated uniqueness. Inverting quasi-isomorphisms
in each tensor variable suffices since (u,v)=(u,1) followed by (1,v).
7. For any objectwise K-flat resolutions with flat terms from lem-pc-kflat-resolution,
Q(q_K) is invertible. Its inverse under F, followed by e on P_K, identifies F(K)
with Q(T_f(P_K)); use d in both variables for tensor. Transport the action on maps
by these identifications, i_L F(a) i_K⁻¹. Thus the displayed chosen-resolution
values themselves form functors without chosen chain-map lifts. For a second choice
use i'_K i_K⁻¹. The uniqueness just proved is uniqueness compatible with e,d,
not uniqueness of arbitrary morphisms completing triangles. The derived-limit
assertions are step 4 transported through the representative comparisons. -/
theorem integralOperationsWellDefined
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    (∀ (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (α : P.obj ⟶ P'.obj), QuasiIso α →
      QuasiIso ((integralOperationsPullbackComplexFunctor l E f).map α)) ∧
    (∀ (P P' Q Q' : (integralOperationsGoodComplex l E W).FullSubcategory)
      (α : P.obj ⟶ P'.obj) (β : Q.obj ⟶ Q'.obj), QuasiIso α → QuasiIso β →
      QuasiIso ((integralOperationsTensorComplexFunctor l E W).map
        (X := (P.obj, Q.obj)) (Y := (P'.obj, Q'.obj)) (α, β))) ∧
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f)
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W))
      (d : ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W),
      (∀ (F' : DerivedCategory (integralTowerModules l E Y) ⥤
          DerivedCategory (integralTowerModules l E X))
        (e' : integralOperationsGoodLocalization l E Y ⋙ F' ≅
          integralOperationsPullbackOnGood l E f),
        ∃! ι : F ≅ F',
          isoWhiskerLeft (integralOperationsGoodLocalization l E Y) ι ≪≫ e' = e) ∧
      (∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
          (DerivedCategory (integralTowerModules l E W)) ⥤
            DerivedCategory (integralTowerModules l E W))
        (d' : ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
            integralOperationsTensorOnGood l E W),
        ∃! ι : G ≅ G', isoWhiskerLeft
          ((integralOperationsGoodLocalization l E W).prod
            (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = d) ∧
      (∀ (K : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ K),
        integralOperationsDerivedLimitProperty l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)
          (F.obj K)) ∧
      (∀ (M N : DerivedCategory (integralTowerModules l E W))
        (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ M) (_d : DerivedCategory.Q.obj Q.obj ≅ N),
        integralOperationsDerivedLimitProperty l E W
          ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
          (G.obj (M, N))) := by
  refine And.intro (integralOperationsPullbackQuasiIsoInvariant l E f) ?_
  refine And.intro (integralOperationsTensorQuasiIsoInvariant l E W) ?_
  exact integralOperationsDerivedDescent l E f W

end WeilConjectures
