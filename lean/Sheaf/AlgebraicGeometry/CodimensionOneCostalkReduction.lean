/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGeometricCostalk
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf

import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.AlgebraicGeometry.EtaleSupportedSections
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.ExcellentOfWeaklyEtale
import WeilConjectures.RingTheory.QuotientHenselianPair
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.NagataDomainN2
import WeilConjectures.RingTheory.JapaneseDomain
import Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Sheaf.RingTheory.IntegralComponentHenselianPermanence
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.FieldTheory.FieldTower
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.AlgebraicGeometry.RegularClosedSupportBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-!
# Codimension-one reduction of geometric costalks

Source: Gabber, Exposé XVII, Definition 1.1.1 and footnote, section 1.3,
and Definition 1.4.1, printed pp. 258–262
(blueprint: lem-per-codimension-one-costalk-reduction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Exact tensor on coefficient complexes. Since the coefficients form a field, this
is tensor derived from the ordinary module tensor, without a resolution choice.
Source: Gabber XVII, Definition 1.4.1, twist compatibility
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkCoefficientTensor (ℓ : ℕ) [Fact ℓ.Prime]
    (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) :=
  (MonoidalCategory.tensorRight M).mapDerivedCategoryPlus

/-- A presentation of a costalk computation by its actual operations. Its tensor passage
has a fixed source: tensor by the geometric fibre of the coefficient sheaf. The constructors
below fix the passage by monoidal inverse image, closed projection and supported adjunction;
only a basis at a supported-sections leaf remains to be supplied.
Source: Gabber XVII, Definitions 1.1.1 and 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
structure CostalkTensorPresentation (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] where
  point : Spec (.of Ω) ⟶ X
  functor : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) ⥤
    DerivedCategory.Plus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
  commShift : functor.CommShift ℤ
  Basis : Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) → Type (u + 1)
  passage : ∀ L, Basis L →
    (functor ⋙ costalkCoefficientTensor ℓ ((pointSmallEtale point).sheafFiber.obj L) ⟶
      supportTensorPlus ℓ L ⋙ functor)

/-- The shifts in a tensor presentation are the shifts of its actual composite functor.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
instance costalkPresentationCommShift (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (P : CostalkTensorPresentation ℓ X Ω) : P.functor.CommShift ℤ := P.commShift

/-- Transport the exact coefficient tensor functor along a module isomorphism.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkCoefficientTransport (ℓ : ℕ) [Fact ℓ.Prime]
    {M N : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))} (e : M ≅ N) :
    costalkCoefficientTensor ℓ M ≅ costalkCoefficientTensor ℓ N :=
  Functor.mapDerivedCategoryPlusNatIso
    ((MonoidalCategory.curriedTensor _).flip.mapIso e)

/-- The stalk presentation, with the canonical monoidal fibre comparison.
Source: Gabber XVII, Definition 1.1.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkStalkPresentation (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) : CostalkTensorPresentation ℓ X Ω :=
  letI := (pointSmallEtale s).sheafFiber_additive
    (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
  { point := s
    functor := etaleDerivedGeometricStalk (ULift.{u + 1} (ZMod ℓ)) s
    commShift := inferInstance
    Basis := fun _ ↦ PUnit
    passage := fun L _ ↦
      letI : PreservesFiniteLimits (tensorRight L) :=
        supportTensor_preservesFiniteLimits ℓ L
      ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (Functor.Monoidal.commTensorRight (pointSmallEtale s).sheafFiber L) ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _).hom }

/-- Prepend exact inverse image. The coefficient identification is the canonical
inverse-image/stalk comparison, and the tensor edge is monoidal pullback.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkPullbackPresentation (ℓ : ℕ) [Fact ℓ.Prime]
    {Y X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (f : Y ⟶ X) (P : CostalkTensorPresentation ℓ Y Ω) :
    CostalkTensorPresentation ℓ X Ω :=
  { point := P.point ≫ f
    functor := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).mapDerivedCategoryPlus ⋙
      P.functor
    commShift := inferInstance
    Basis := fun L ↦ P.Basis
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).obj L)
    passage := fun L b ↦
      let U := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).mapDerivedCategoryPlus
      let L' := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).obj L
      (Functor.associator U P.functor _).hom ≫
      Functor.whiskerLeft U (Functor.whiskerLeft P.functor
        (costalkCoefficientTransport ℓ
          ((upperStarCompSheafFiberIso
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f P.point).app L).symm).hom) ≫
      Functor.whiskerLeft U (P.passage L' b) ≫
      (Functor.associator U (supportTensorPlus ℓ L') P.functor).inv ≫
      Functor.whiskerRight (supportTensorPullbackPlus ℓ f L).inv P.functor ≫
      (Functor.associator (supportTensorPlus ℓ L) U P.functor).hom }

/-- Prepend the actual supported right adjoint. Its tensor edge is exactly the mate
of the inverse closed projection, with the supported counit normalization.
Source: Gabber XVII, Definitions 1.1.1 and 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkSupportPresentation (ℓ : ℕ) [Fact ℓ.Prime]
    {Y X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (i : Y ⟶ X) [IsClosedImmersion i] (P : CostalkTensorPresentation ℓ Y Ω) :
    CostalkTensorPresentation ℓ X Ω :=
  { point := P.point ≫ i
    functor := closedSupportPlus (ULift.{u + 1} (ZMod ℓ)) i ⋙ P.functor
    commShift := inferInstance
    Basis := fun L ↦ P.Basis
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) i).obj L)
    passage := fun L b ↦
      let U := closedSupportPlus (ULift.{u + 1} (ZMod ℓ)) i
      let L' := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) i).obj L
      (Functor.associator U P.functor _).hom ≫
      Functor.whiskerLeft U (Functor.whiskerLeft P.functor
        (costalkCoefficientTransport ℓ
          ((upperStarCompSheafFiberIso
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) i P.point).app L).symm).hom) ≫
      Functor.whiskerLeft U (P.passage L' b) ≫
      (Functor.associator U (supportTensorPlus ℓ L') P.functor).inv ≫
      Functor.whiskerRight (supportTensorMatePlus ℓ i L) P.functor ≫
      (Functor.associator (supportTensorPlus ℓ L) U P.functor).hom }

/-- Tensor by a trivialized actual sheaf, with the canonical tensor-unit identification.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkTrivializedSheafTensor (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}
    {L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))}
    (b : L ≅ 𝟙_ _) : supportTensorPlus ℓ L ≅ 𝟭 _ :=
  supportTensorTransportPlus ℓ b ≪≫
    Functor.mapDerivedCategoryPlusNatIso (MonoidalCategory.rightUnitorNatIso _) ≪≫
      Functor.mapDerivedCategoryPlusIdIso _

/-- Tensor by the geometric fibre of a trivialized sheaf; the fibre basis is the image
of the same sheaf basis, followed by the monoidal fibre unit comparison.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkTrivializedFiberTensor (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    {L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))}
    (b : L ≅ 𝟙_ _) :
    costalkCoefficientTensor ℓ ((pointSmallEtale s).sheafFiber.obj L) ≅ 𝟭 _ :=
  costalkCoefficientTransport ℓ
      ((pointSmallEtale s).sheafFiber.mapIso b ≪≫
        (Functor.Monoidal.εIso (pointSmallEtale s).sheafFiber).symm) ≪≫
    Functor.mapDerivedCategoryPlusNatIso (MonoidalCategory.rightUnitorNatIso _) ≪≫
      Functor.mapDerivedCategoryPlusIdIso _

/-- Supported sections, with the tensor passage normalized by one actual coefficient
basis and its geometric fibre. On strict local schemes Tate lines admit such bases.
The passage is required below for every basis, so none is fixed as additional data.
Source: Gabber XVII, Definition 1.1.1 footnote and Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def costalkSectionsPresentation (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (W : X.Opens) : CostalkTensorPresentation ℓ X Ω :=
  { point := s
    functor := (supportedEtaleSections (ULift.{u + 1} (ZMod ℓ)) X W).rightDerivedFunctorPlus
    commShift := inferInstance
    Basis := fun L ↦ L ≅ 𝟙_ _
    passage := fun _ b ↦
      (Functor.isoWhiskerLeft _ (costalkTrivializedFiberTensor ℓ s b) ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (costalkTrivializedSheafTensor ℓ b).symm _).hom }

/-- The ordinary-local definition of geometric costalk, with its canonical tensor route.
Source: Gabber XVII, Definition 1.1.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def geometricCostalkPresentation (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) : CostalkTensorPresentation ℓ X Ω :=
  costalkPullbackPresentation ℓ
    (X.fromSpecStalk ((Scheme.SpecToEquivOfField Ω X) s).1)
    (costalkSupportPresentation ℓ
      (localClosedPoint X ((Scheme.SpecToEquivOfField Ω X) s).1)
      (costalkStalkPresentation ℓ (Spec.map ((Scheme.SpecToEquivOfField Ω X) s).2)))

/-- The strict-local supported computation, with its actual inverse-image tensor route.
Source: Gabber XVII, Definition 1.1.1 footnote
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def strictLocalCostalkPresentation (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) : CostalkTensorPresentation ℓ X Ω :=
  letI : IsLocalRing (strictHenselization s) := isLocalRing_strictHenselization s
  costalkPullbackPresentation ℓ (strictLocalizationToBase s)
    (costalkSectionsPresentation ℓ (Spec.map (strictHenselizationEval s))
      ⟨{IsLocalRing.closedPoint (strictHenselization s)}ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩)

/-- Compatibility on the real twists `K ⊗ᴸ Λ(a)`, with all edges fixed by the displayed
presentations. Unlike a square over arbitrary endofunctors, these tensor edges come from
monoidal pullback, the inverse closed projection mate and the geometric fibre of the same
coefficient line. For each signed Tate power, section-leaf bases exist and every such basis
gives an invertible passage and the same commuting comparison square.
Source: Gabber XVII, Definitions 1.1.1 and 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def HasTwistShiftCompatibleIso (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (P Q : CostalkTensorPresentation ℓ X Ω) : Prop :=
  P.functor.Linear (ULift.{u + 1} (ZMod ℓ)) ∧
  Q.functor.Linear (ULift.{u + 1} (ZMod ℓ)) ∧
  ∃ (h : P.point = Q.point) (e : P.functor ≅ Q.functor),
    NatTrans.CommShift e.hom ℤ ∧
    ∀ (hℓ : (ℓ : ULift.{u + 1} (ZMod ℓ)) = 0) (a : ℤ),
      Nonempty (P.Basis (finiteEtaleTateSheaf _ ℓ X hℓ a)) ∧
      Nonempty (Q.Basis (finiteEtaleTateSheaf _ ℓ X hℓ a)) ∧
      ∀ (bP : P.Basis (finiteEtaleTateSheaf _ ℓ X hℓ a))
        (bQ : Q.Basis (finiteEtaleTateSheaf _ ℓ X hℓ a)),
      IsIso (P.passage _ bP) ∧ IsIso (Q.passage _ bQ) ∧
      ∀ K, (P.passage _ bP).app K ≫
          e.hom.app ((supportTensorPlus ℓ (finiteEtaleTateSheaf _ ℓ X hℓ a)).obj K) =
        (costalkCoefficientTensor ℓ
          ((pointSmallEtale P.point).sheafFiber.obj
            (finiteEtaleTateSheaf _ ℓ X hℓ a))).map (e.hom.app K) ≫
        (costalkCoefficientTransport ℓ
          (eqToIso (congrArg
            (fun z ↦ (pointSmallEtale z).sheafFiber.obj
              (finiteEtaleTateSheaf _ ℓ X hℓ a)) h))).hom.app (Q.functor.obj K) ≫
        (Q.passage _ bQ).app K

/-- The reduced closure of the image of the generizing geometric point in the strict local
scheme at the specialization. Its ideal is the actual vanishing ideal, not chosen data.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def codimensionOneClosureIdeal {X : Scheme.{u}}
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    {x : Spec (.of Ωx) ⟶ X} {y : Spec (.of Ωy) ⟶ X}
    (s : strictLocalization y ⟶ strictLocalization x) :
    (strictLocalization x).IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨closure {((Spec.map (strictHenselizationEval y)) ≫ s) default}, isClosed_closure⟩

/-- The reduced closed curve used in the immediate-specialization reduction.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
abbrev codimensionOneClosure {X : Scheme.{u}}
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    {x : Spec (.of Ωx) ⟶ X} {y : Spec (.of Ωy) ⟶ X}
    (s : strictLocalization y ⟶ strictLocalization x) : Scheme.{u} :=
  (codimensionOneClosureIdeal s).subscheme

/-- The canonical closed immersion of the reduced closure.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
abbrev codimensionOneClosureι {X : Scheme.{u}}
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    {x : Spec (.of Ωx) ⟶ X} {y : Spec (.of Ωy) ⟶ X}
    (s : strictLocalization y ⟶ strictLocalization x) :
    codimensionOneClosure s ⟶ strictLocalization x :=
  (codimensionOneClosureIdeal s).subschemeι

/-- Restriction to the strict localization followed by supported inverse image on the curve.
Source: Gabber XVII, Definition 1.4.1, the complex denoted `L`
(blueprint: lem-per-codimension-one-costalk-reduction). -/
abbrev codimensionOneComplex {X : Scheme.{u}} (R : Type (u + 1)) [CommRing R] [Finite R]
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    {x : Spec (.of Ωx) ⟶ X} {y : Spec (.of Ωy) ⟶ X}
    (s : strictLocalization y ⟶ strictLocalization x) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory.Plus
        (Sheaf (codimensionOneClosure s).smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (upperStar (ModuleCat.{u + 1} R) (strictLocalizationToBase x)).mapDerivedCategoryPlus ⋙
    closedSupportPlus R (codimensionOneClosureι s)

/-- Prepend restriction to the strict localization and supported inverse image on the
reduced closure. Its functor is exactly `codimensionOneComplex` followed by the supplied
computation on the curve; tensor passages are composed from those actual operations.
Source: Gabber XVII, Definition 1.4.1
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def codimensionOnePresentation {X : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]
    {Ωx Ωy Ω : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    [Field Ω] [IsAlgClosed Ω]
    {x : Spec (.of Ωx) ⟶ X} {y : Spec (.of Ωy) ⟶ X}
    (s : strictLocalization y ⟶ strictLocalization x)
    (P : CostalkTensorPresentation ℓ (codimensionOneClosure s) Ω) :
    CostalkTensorPresentation ℓ X Ω :=
  costalkPullbackPresentation ℓ (strictLocalizationToBase x)
    (costalkSupportPresentation ℓ (codimensionOneClosureι s) P)

/-- The residue extension properties, using exactly the algebra structure induced by
`f.residueFieldMap`. The degree includes the characteristic-zero convention.
Source: Gabber XVII, section 1.3
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def HasPrimeToResidueDegree {Y Z : Scheme.{u}} (f : Y ⟶ Z) (t : Y) (ℓ : ℕ) : Prop :=
  letI := (f.residueFieldMap t).hom.toAlgebra
  Module.Finite (Z.residueField (f t)) (Y.residueField t) ∧
    IsPurelyInseparable (Z.residueField (f t)) (Y.residueField t) ∧
    (if ringChar (Z.residueField (f t)) = 0 then
      Module.finrank (Z.residueField (f t)) (Y.residueField t) = 1
    else ∃ r : ℕ, Module.finrank (Z.residueField (f t)) (Y.residueField t) =
      ringChar (Z.residueField (f t)) ^ r) ∧
    IsUnit (Module.finrank (Z.residueField (f t)) (Y.residueField t) : ZMod ℓ)

/-- The geometric and categorical conclusions after the reduced closure is known integral.
The geometric lifts are constrained by the original specialization, and unique on the
normalization. Every comparison is natural in the entire bounded below complex.
Source: Gabber XVII, sections 1.3–1.4
(blueprint: lem-per-codimension-one-costalk-reduction). -/
def CodimensionOneCostalkReduction {X : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    {x : Spec (.of Ωx) ⟶ X} {y : Spec (.of Ωy) ⟶ X}
    (s : strictLocalization y ⟶ strictLocalization x)
    [IsIntegral (codimensionOneClosure s)] : Prop :=
  IsNoetherian (codimensionOneClosure s) ∧
  (∃ (B : CommRingCat.{u}) (_ : IsStrictlyHenselianLocalRing B),
    IsExcellent B ∧ Nonempty (codimensionOneClosure s ≅ Spec B)) ∧
  IsFinite (codimensionOneClosure s).fromNormalization ∧
  (topologically IsHomeomorph).universally (codimensionOneClosure s).fromNormalization ∧
  (∃ (D : CommRingCat.{u}) (_ : IsDomain D) (_ : IsDiscreteValuationRing D)
      (_ : IsStrictlyHenselianLocalRing D),
    Nonempty ((codimensionOneClosure s).normalization ≅ Spec D)) ∧
  (codimensionOneClosure s).fromNormalization
      (genericPoint (codimensionOneClosure s).normalization) =
    genericPoint (codimensionOneClosure s) ∧
  IsIso ((codimensionOneClosure s).fromNormalization.residueFieldMap
    (genericPoint (codimensionOneClosure s).normalization)) ∧
  (lowerStar (Type (u + 1))
    (codimensionOneClosure s).fromNormalization).IsEquivalence ∧
  (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (codimensionOneClosure s).fromNormalization).IsEquivalence ∧
  ∃ (z₀ : codimensionOneClosure s) (t₀ : (codimensionOneClosure s).normalization),
    IsClosed ({z₀} : Set (codimensionOneClosure s)) ∧
    (∀ z : codimensionOneClosure s, z ⤳ z₀) ∧
    ∃ ht₀ : IsClosed ({t₀} : Set (codimensionOneClosure s).normalization),
    (∀ t : (codimensionOneClosure s).normalization, t ⤳ t₀) ∧
    (codimensionOneClosure s).fromNormalization t₀ = z₀ ∧
    HasPrimeToResidueDegree (codimensionOneClosure s).fromNormalization t₀ ℓ ∧
    ∃ (yZ : Spec (.of Ωy) ⟶ codimensionOneClosure s)
      (xZ : Spec (.of Ωx) ⟶ codimensionOneClosure s)
      (yN : Spec (.of Ωy) ⟶ (codimensionOneClosure s).normalization)
      (xN : Spec (.of Ωx) ⟶ (codimensionOneClosure s).normalization),
      yZ ≫ codimensionOneClosureι s = Spec.map (strictHenselizationEval y) ≫ s ∧
      xZ ≫ codimensionOneClosureι s = Spec.map (strictHenselizationEval x) ∧
      yZ default = genericPoint (codimensionOneClosure s) ∧
      xZ default = z₀ ∧
      yN default = genericPoint (codimensionOneClosure s).normalization ∧
      xN default = t₀ ∧
      yN ≫ (codimensionOneClosure s).fromNormalization = yZ ∧
      xN ≫ (codimensionOneClosure s).fromNormalization = xZ ∧
      (∀ yN' : Spec (.of Ωy) ⟶ (codimensionOneClosure s).normalization,
        yN' ≫ (codimensionOneClosure s).fromNormalization = yZ → yN' = yN) ∧
      (∀ xN' : Spec (.of Ωx) ⟶ (codimensionOneClosure s).normalization,
        xN' ≫ (codimensionOneClosure s).fromNormalization = xZ → xN' = xN) ∧
      HasTwistShiftCompatibleIso ℓ
        (geometricCostalkPresentation ℓ y)
        (codimensionOnePresentation ℓ s (geometricCostalkPresentation ℓ yZ)) ∧
      HasTwistShiftCompatibleIso ℓ
        (codimensionOnePresentation ℓ s (geometricCostalkPresentation ℓ yZ))
        (codimensionOnePresentation ℓ s
          (costalkPullbackPresentation ℓ (codimensionOneClosure s).fromNormalization
            (costalkStalkPresentation ℓ yN))) ∧
      HasTwistShiftCompatibleIso ℓ
        (geometricCostalkPresentation ℓ x)
        (codimensionOnePresentation ℓ s (geometricCostalkPresentation ℓ xZ)) ∧
      HasTwistShiftCompatibleIso ℓ
        (codimensionOnePresentation ℓ s (geometricCostalkPresentation ℓ xZ))
        (codimensionOnePresentation ℓ s
          (costalkPullbackPresentation ℓ (codimensionOneClosure s).fromNormalization
            (costalkSectionsPresentation ℓ xN ⟨{t₀}ᶜ, ht₀.isOpen_compl⟩)))

/-- Strict-local comparison and immediate-specialization reduction, naturally in every
bounded below complex. Source: Gabber XVII, Definitions 1.1.1 and 1.4.1 and section 1.3
(blueprint: lem-per-codimension-one-costalk-reduction).

Proof:
1. The module enhancement of the support adjunction is coefficient-linear. Closed
   pushforward is exact, hence its support right adjoint preserves injectives. The
   support functor on injectives computes supported sections, and composable closed
   right adjoints compose with their counits.
2. Compare the ordinary local ring and strict henselization using the ind-etale
   closed-support base-change lemma. Its closed fibre is the separable residue closure.
   Sections there are the geometric stalk, giving the first natural comparison.
3. The excellent affine chart has excellent Noetherian strict henselization. The
   reduced closure is Spec(H/p); it is integral, excellent, local and strictly henselian,
   and its dimension is one by hypothesis.
4. Excellence gives the Nagata finiteness of normalization. The integral closure
   in the function field is a normal one-dimensional Noetherian domain; henselian
   permanence makes it local strictly henselian, hence a discrete valuation ring.
5. Both local spectra have only their generic and closed points. The generic residue
   field is unchanged; the finite closed residue extension is purely inseparable.
   Thus normalization is integral, radicial, surjective and a universal homeomorphism.
6. The closed residue degree is one in characteristic zero and a p-power otherwise.
   Since ell is invertible, that degree is a unit in the coefficient field.
7. Ind-etale invariance of strict localizations and composition of closed support
   functors identify both original costalks with those on the reduced closure.
8. Topological invariance transports module sheaves and supported sections to the
   normalization. At the generic point costalk is stalk, giving both displayed chains.
9. All these maps are coefficient-linear maps of complexes, and commute with shifts.
   For twists choose a basis of the actual roots-of-unity Tate line on the strict
   localization (an etale trivializing neighborhood has a section), and pull it to
   the closure and normalization. Positive tensor powers and dual negative powers
   identify twist compatibility with coefficient linearity. Changing the basis
   multiplies by a scalar unit, so the resulting comparisons are independent of it.
   This is the twist/shift compatibility in Definition 1.4.1's square.

The nine steps use, respectively:
1. `lem-pur-etale-supported-kernel-adjunction`, `lem-sp-right-adjoint-preserves-injectives`,
   `lem-cat-right-adjoint-composition`, `def-pur-etale-derived-supported-sections`.
2. `lem-exc-affine-strict-local-ring-comparison`, `lem-weil-pbc-strict-henselization-triples`,
   `lem-weil-pbc-localization-noetherian`, `lem-sc-strict-henselization-noetherian`,
   `lem-per-ind-etale-closed-support-base-change`,
   `lem-weil-pbc-strictly-henselian-sections-stalk`.
3. `lem-exc-finite-type-localization-excellent`, `lem-exc-weakly-etale-excellent`,
   `lem-weil-pbc-strict-henselization-affine-chart-ind-etale`,
   `lem-weil-pbc-ind-etale-stability`, `lem-weil-pbc-spec-irreducible-closed-subsets-primes`,
   `lem-weil-pbc-quotient-henselian-pair`.
4. `lem-exc-quasi-excellent-nagata`, `lem-weil-pbc-nagata-domain-n2`,
   `def-weil-pbc-japanese-domain`, `lem-sc-integral-closure-dedekind-surjective-fibres`,
   `lem-trf-integral-component-henselian-permanence`, `lem-sc-normal-dim1-dvr`.
5. `lem-kun-sep-closed-finite-extension-purely-inseparable`, `def-weil-radicial-morphism`,
   `lem-pc-integral-radicial-surjective-universal-homeomorphism`,
   `lem-weil-pbc-sepclosed-finite-extension-unique-embedding`.
6. `def-pc-field-tower`, `lem-weil-pbc-purely-inseparable-pth-root-tower`,
   `lem-weil-pbc-field-degree-multiplicativity`.
7. `lem-trf-ind-etale-strict-local-invariance`,
   `lem-per-ind-etale-closed-support-base-change`.
8. `prop-weil-pbc-universal-homeomorphism-topos`,
   `def-pur-etale-derived-supported-sections`.
9. `def-asd-finite-etale-tate-twist`, `lem-asd-finite-etale-twist-line`,
   `lem-sbc-strict-henselian-etale-neighbourhood-section`. -/
theorem codimensionOneCostalkReduction (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X]
    (hExcellent : ∀ z : X, ∃ U : X.affineOpens, z ∈ U.1 ∧ IsExcellent Γ(X, U.1))
    (hInvertible : ∀ z : X, IsUnit (ℓ : X.residueField z)) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ X),
      HasTwistShiftCompatibleIso ℓ
        (geometricCostalkPresentation ℓ z) (strictLocalCostalkPresentation ℓ z)) ∧
    ∀ (Ωx Ωy : Type u) [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
      (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ X)
      (s : strictLocalization y ⟶ strictLocalization x),
      s ≫ strictLocalizationToBase x = strictLocalizationToBase y →
      topologicalKrullDim (codimensionOneClosure s) = 1 →
      ∃ hIntegral : IsIntegral (codimensionOneClosure s),
        @CodimensionOneCostalkReduction X ℓ _ Ωx Ωy _ _ _ _ x y s hIntegral := by
  sorry

end AlgebraicGeometry.Etale
