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
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

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
  exact (derivedCategory_countableProducts_and_towerLimit.{0}
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
  sorry

end WeilConjectures
