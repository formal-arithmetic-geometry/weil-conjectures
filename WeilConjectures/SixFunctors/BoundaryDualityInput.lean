/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.DualityPairing
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ClosedCostalkDuality
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Finite-stage boundary duality input

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-biduality-general/def-weil-boundary-duality-input.md`
(blueprint: def-weil-boundary-duality-input).

The coefficient presentation is the recorded fixed-scalar presentation, related to the
intrinsic constant-ring presentation by `sfIntrinsicDerivedEquivalence`. Finite Tor
constructibility is tested after that specified equivalence. All functors below are the
recorded functors. The auxiliary comparison maps are fixed by equations with the comparison
adjunction, the etale tensor-exceptional mate, and compact-support composition. Thus neither
boundary exchange nor its normalization is an independently chosen map.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u a

open TopologicalSpace CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.BoundaryDualityInput

section AbstractSystem

universe i b c e v w

variable {I : Type i} (B : I → I → Type b)
  (P : I → Type c) [∀ T, Category.{v} (P T)] [∀ T, MonoidalCategory (P T)]
  [∀ T, MonoidalClosed (P T)]
  (E : I → Type e) [∀ T, Category.{w} (E T)] [∀ T, MonoidalCategory (E T)]

/-- Canonical operations used to write boundary pairings, before choosing site coordinates.
Every field is tied to the recorded operation by CanonicalOperations below.
Source: both clauses (blueprint: def-weil-boundary-duality-input). -/
structure Operations where
  nu : ∀ T, E T ⥤ P T
  nuR : ∀ T, P T ⥤ E T
  adj : ∀ T, nu T ⊣ nuR T
  star : ∀ {Z T}, B Z T → P T ⥤ P Z
  estar : ∀ {Z T}, B Z T → E T ⥤ E Z
  estarLeft : ∀ {Z T}, B Z T → E T ⥤ E Z
  estarIso : ∀ {Z T} (f : B Z T), estarLeft f ≅ estar f
  eexc : ∀ {Z T}, B Z T → E T ⥤ E Z
  eOmega : ∀ T, E T
  symmetry : ∀ T (K L : P T), K ⊗ L ≅ L ⊗ K
  etaleSymmetry : ∀ T (K L : E T), K ⊗ L ≅ L ⊗ K
  evaluation : ∀ T (K : P T),
    (MonoidalClosed.internalHom.flip.obj ((nu T).obj (eOmega T))).obj (op K) ⊗ K ⟶
      (nu T).obj (eOmega T)
  nuTensor : ∀ T (K L : E T),
    (nu T).obj (K ⊗ L) ≅ (nu T).obj K ⊗ (nu T).obj L
  square : ∀ {Z T} (f : B Z T), nu T ⋙ star f ≅ estar f ⋙ nu Z
  etau : ∀ {Z T} (f : B Z T) (M N : E T),
    (eexc f).obj M ⊗ (estarLeft f).obj N ⟶ (eexc f).obj (M ⊗ N)
  ecomp : ∀ {Z T} (f : B Z T), (eexc f).obj (eOmega T) ≅ eOmega Z

namespace Operations

variable {B P E}

/-- The specified comparison presentation of the dualizing object.
Source: clause 1 (blueprint: def-weil-boundary-duality-input). -/
def omega (o : Operations B P E) (T : I) := (o.nu T).obj (o.eOmega T)

/-- Internal Hom into the specified dualizing object.
Source: clause 1 (blueprint: def-weil-boundary-duality-input). -/
def dual (o : Operations B P E) (T : I) : (P T)ᵒᵖ ⥤ P T :=
  MonoidalClosed.internalHom.flip.obj (o.omega T)

/-- Exceptional inverse image is the comparison transport of the etale adjoint.
Source: exceptional-inverse-image convention (blueprint: def-weil-boundary-duality-input). -/
def exceptional (o : Operations B P E) {Z T : I} (f : B Z T) : P T ⥤ P Z :=
  o.nuR T ⋙ o.eexc f ⋙ o.nu Z

/-- Double duality is the tensor-Hom transpose of the specified evaluation.
Source: evaluation convention (blueprint: def-weil-boundary-duality-input). -/
def delta (o : Operations B P E) (T : I) (K : P T) :
    K ⟶ (o.dual T).obj (op ((o.dual T).obj (op K))) :=
  (MonoidalClosed.internalHomAdjunction₂.adj ((o.dual T).obj (op K))).homEquiv K _
    (o.evaluation T K)

/-- Tensor-Hom transposition with the internal-Hom argument on the right.
Source: clause 2 (blueprint: def-weil-boundary-duality-input). -/
def transpose (o : Operations B P E) (T : I) (K L : P T)
    (f : K ⊗ L ⟶ o.omega T) : K ⟶ (o.dual T).obj (op L) :=
  (MonoidalClosed.internalHomAdjunction₂.adj L).homEquiv K _
    ((o.symmetry T L K).hom ≫ f)

/-- Lax tensor map of the comparison right adjoint, the mate of the two counits.
Source: canonical tensor comparison (blueprint: def-weil-boundary-duality-input). -/
def rightTensor (o : Operations B P E) (T : I) (M N : P T) :
    (o.nuR T).obj M ⊗ (o.nuR T).obj N ⟶ (o.nuR T).obj (M ⊗ N) :=
  (o.adj T).homEquiv _ _ ((o.nuTensor T _ _).hom ≫
    ((o.adj T).counit.app M ⊗ₘ (o.adj T).counit.app N))

/-- The canonical tensor-exceptional paste before cancelling the comparison counit.
Source: the boundary pairing (blueprint: def-weil-boundary-duality-input). -/
def tensorModel (o : Operations B P E) {Z T : I} (f : B Z T) (M N : P T) :
    (o.star f).obj ((o.nu T).obj ((o.nuR T).obj M)) ⊗ (o.exceptional f).obj N ⟶
      (o.exceptional f).obj (M ⊗ N) :=
  ((o.square f).hom.app ((o.nuR T).obj M) ⊗ₘ 𝟙 ((o.exceptional f).obj N)) ≫
    (o.nuTensor Z _ _).inv ≫
    (o.nu Z).map ((o.etaleSymmetry Z _ _).hom ≫
      (𝟙 _ ⊗ₘ (o.estarIso f).inv.app ((o.nuR T).obj M)) ≫
      o.etau f ((o.nuR T).obj N) ((o.nuR T).obj M) ≫
      (o.eexc f).map ((o.etaleSymmetry T _ _).hom ≫ o.rightTensor T M N))

/-- Boundary exchange is exactly the transpose of tau followed by evaluation and theta.
Source: clause 2 (blueprint: def-weil-boundary-duality-input). -/
def exchange (o : Operations B P E) {Z T : I} (f : B Z T)
    (theta : (o.exceptional f).obj (o.omega T) ≅ o.omega Z) (L : P T)
    (tau : (o.star f).obj ((o.dual T).obj (op L)) ⊗ (o.exceptional f).obj L ⟶
      (o.exceptional f).obj ((o.dual T).obj (op L) ⊗ L)) :
    (o.star f).obj ((o.dual T).obj (op L)) ⟶
      (o.dual Z).obj (op ((o.exceptional f).obj L)) :=
  o.transpose Z _ _ (tau ≫ (o.exceptional f).map (o.evaluation T L) ≫ theta.hom)

end Operations

/-- The two boundary-duality assertions, expressed in the specified operations.
Source: clauses 1 and 2 and the expanded alpha normalization
(blueprint: def-weil-boundary-duality-input). -/
structure Assertions (o : Operations B P E) (ctf : ∀ T, P T → Prop) where
  preserves : ∀ T (K : P T), ctf T K → ctf T ((o.dual T).obj (op K))
  theta : ∀ {Z T} (f : B Z T), (o.exceptional f).obj (o.omega T) ≅ o.omega Z
  theta_normalization : ∀ {Z T} (f : B Z T),
    (o.nu Z).map ((o.eexc f).map ((o.adj T).unit.app (o.eOmega T))) ≫
      (theta f).hom = (o.nu Z).map (o.ecomp f).hom
  tau : ∀ {Z T} (f : B Z T) (M N : P T) (_hM : ctf T M),
    (o.star f).obj M ⊗ (o.exceptional f).obj N ⟶ (o.exceptional f).obj (M ⊗ N)
  tau_normalization : ∀ {Z T} (f : B Z T) (M N : P T) (hM : ctf T M),
    ((o.star f).map ((o.adj T).counit.app M) ⊗ₘ 𝟙 ((o.exceptional f).obj N)) ≫
      tau f M N hM = o.tensorModel f M N
  exchange_isIso : ∀ {Z T} (f : B Z T) (L : P T) (hL : ctf T L),
    IsIso (o.exchange f (theta f) L (tau f ((o.dual T).obj (op L)) L (preserves T L hL)))
  alpha : ∀ {Z T} (f : B Z T) (K : P T) (_hK : ctf T K),
    (o.exceptional f).obj ((o.dual T).obj (op K)) ≅
      (o.dual Z).obj (op ((o.star f).obj K))
  alpha_normalization : ∀ {Z T} (f : B Z T) (K : P T) (hK : ctf T K),
    (alpha f K hK).hom = o.transpose Z _ _
      ((o.symmetry Z _ _).hom ≫ tau f K ((o.dual T).obj (op K)) hK ≫
        (o.exceptional f).map ((o.symmetry T _ _).hom ≫ o.evaluation T K) ≫
        (theta f).hom)
  compatibility : ∀ {Z T} (f : B Z T) (K : P T) (hK : ctf T K),
    (o.star f).map (o.delta T K) ≫
      o.exchange f (theta f) ((o.dual T).obj (op K))
        (tau f _ _ (preserves T _ (preserves T K hK))) =
      o.delta Z ((o.star f).obj K) ≫ (o.dual Z).map (alpha f K hK).hom.op

end AbstractSystem

/-- Fixed-scalar coordinates for the recorded small pro-etale coefficient category.
Source: finite-stage coefficient convention (blueprint: def-weil-boundary-duality-input). -/
abbrev FixedCategory (C : Type a) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (ProEt.topology T) C)


/-- The ordinary etale category used to define the exceptional adjoint.
Source: exceptional inverse image (blueprint: def-weil-boundary-duality-input). -/
abbrev FixedEtaleCategory (C : Type a) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf T.smallEtaleTopology C)

variable (C : Type a) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Etale.UpperStarPreservesFlat C]
  [∀ T : Scheme.{u}, (comparisonUpperStar C T).PreservesFlat]
  {FC : C → C → Type*} {CC : C → Type (u + 1)}
  [∀ (P Q : C), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} C FC]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget C)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget C)]
  [∀ {Z T : Scheme.{u}} (i : Z ⟶ T) [HasCompactification i], IsIso (Etale.projectionMap C i)]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]


/-- The canonical derived comparison inverse image.
Source: comparison convention (blueprint: def-weil-boundary-duality-input). -/
abbrev comparison (T : Scheme.{u}) : FixedEtaleCategory C T ⥤ FixedCategory C T :=
  (comparisonUpperStar C T).mapDerivedCategory


/-- The canonical derived comparison direct image.
Source: comparison convention (blueprint: def-weil-boundary-duality-input). -/
abbrev comparisonRight (T : Scheme.{u}) : FixedCategory C T ⥤ FixedEtaleCategory C T :=
  (comparisonLowerStar
    C T).rightDerivedFunctor


section GenericMonoidal
universe b c
variable {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [BraidedCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {D : Type c} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [BraidedCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

/-- Derived monoidal comparison transported through LF = D(F).
Source: site comparison (blueprint: def-weil-boundary-duality-input). -/
def genericComparisonTensor (K : DerivedCategory B) :
    (curriedTensor (DerivedCategory B)).obj K ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙
        (curriedTensor (DerivedCategory D)).obj (F.mapDerivedCategory.obj K) :=
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  let t := asIso F.leftDerivedTensorComparison
  Functor.isoWhiskerLeft ((curriedTensor (DerivedCategory B)).obj K) e.symm ≪≫
    t.app K ≪≫
    Functor.isoWhiskerRight e
      ((curriedTensor (DerivedCategory D)).obj (F.leftDerivedFunctor.obj K)) ≪≫
    Functor.isoWhiskerLeft F.mapDerivedCategory
      ((curriedTensor (DerivedCategory D)).mapIso (e.app K))
end GenericMonoidal

/-- The etale dualizing object Ra! Λ.
Source: clause 1 (blueprint: def-weil-boundary-duality-input). -/
def etaleOmega {S T : Scheme.{u}} (a : T ⟶ S) [HasCompactification a] :
    FixedEtaleCategory (ModuleCat.{u + 1} Λ) T :=
  Etale.dualizingComplex Λ a


/-- The pro-etale dualizing object: the comparison pullback of the etale adjoint's value.
The comparison unit at the coefficient object identifies this with the recorded Ra! Λ.
Source: clause 1 (blueprint: def-weil-boundary-duality-input). -/
def omega {S T : Scheme.{u}} (a : T ⟶ S) [HasCompactification a] :
    FixedCategory (ModuleCat.{u + 1} Λ) T :=
  (comparison (ModuleCat.{u + 1} Λ) T).obj (etaleOmega Λ a)


/-- The right-adjoint mate of the specified compact-support composition.
Source: composition convention (blueprint: def-weil-boundary-duality-input). -/
def etaleOmegaComposition {Z T S : Scheme.{u}} (i : Z ⟶ T) (a : T ⟶ S) (b : Z ⟶ S)
    [HasCompactification i] [HasCompactification a] [HasCompactification b]
    (e : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) a ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) b) :=
  ((Etale.rightDerivedUpperShriekAdjunction Λ i).comp
    (Etale.rightDerivedUpperShriekAdjunction Λ a)).rightAdjointUniq
      ((Etale.rightDerivedUpperShriekAdjunction Λ b).ofNatIsoLeft e.symm) |>.app (𝟙_ _)

/-- Canonical comparison pullback square on the derived categories.
Source: site comparison (blueprint: def-weil-boundary-duality-input). -/
def derivedComparisonPullback {Z T : Scheme.{u}} (i : Z ⟶ T) :=
  (Functor.mapDerivedCategoryCompIso (comparisonUpperStar C T) (upperStar C i)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso C i) ≪≫
    Functor.mapDerivedCategoryCompIso (Etale.upperStar C i) (comparisonUpperStar C Z)


/-- A locally closed piece is precisely a scheme equipped with an immersion into Y.
Source: the piece convention (blueprint: def-weil-boundary-duality-input). -/
structure Piece (Y : Scheme.{u}) where
  scheme : Scheme.{u}
  inclusion : scheme ⟶ Y
  immersion : IsImmersion inclusion

attribute [instance] Piece.immersion

/-- Immersions have inducing underlying maps, so pieces of a Noetherian space are Noetherian.
Source: the finite-type setting (blueprint: def-weil-boundary-duality-input). -/
instance Piece.noetherianSpace {Y : Scheme.{u}} [NoetherianSpace Y] (P : Piece Y) :
    NoetherianSpace P.scheme :=
  P.inclusion.isEmbedding.isInducing.noetherianSpace

/-- The structure map of the piece, with its inherited separated finite-type structure.
Source: clause 1 (blueprint: def-weil-boundary-duality-input). -/
abbrev Piece.structureMap {Y S : Scheme.{u}} (P : Piece Y) (aY : Y ⟶ S) :=
  P.inclusion ≫ aY

/-- Compactifiability inherited by a piece from the finite-type setting.
Source: clause 1 (blueprint: def-weil-boundary-duality-input). -/
instance Piece.structureMap_hasCompactification {S Y : Scheme.{u}} (aY : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [NoetherianSpace Y]
    [IsSeparated aY] [LocallyOfFiniteType aY] (P : Piece Y) :
    HasCompactification (P.structureMap aY) :=
  letI : IsSeparated P.inclusion := IsSeparated.isSeparated_of_mono P.inclusion
  letI : LocallyOfFiniteType (P.structureMap aY) :=
    locallyOfFiniteType_comp P.inclusion aY
  letI : QuasiCompact (P.structureMap aY) :=
    quasiCompact_of_noetherianSpace_source (P.structureMap aY)
  (NagataCompactification (P.structureMap aY)).hasCompactification

/-- A closed immersion between the specified pieces, with its equality over Y.
Source: clause 2 (blueprint: def-weil-boundary-duality-input). -/
structure Boundary {Y : Scheme.{u}} (Z T : Piece Y) where
  map : Z.scheme ⟶ T.scheme
  closed : IsClosedImmersion map
  over_eq : map ≫ T.inclusion = Z.inclusion

attribute [instance] Boundary.closed

section PairingComponents

variable {A : Type a} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The descended Koszul symmetry recorded by a pro-etale duality pairing.
Stated for abstract coefficients so that the kernel unfolds the pairing only once.
Source: both clauses (blueprint: def-weil-boundary-duality-input). -/
def proPairingSymmetry {W : FixedCategory A X} (h : ProEtale.AmbientDualityPairing A X W)
    (K L : FixedCategory A X) :=
  (h.choose.app K).app L

/-- The descended Koszul symmetry recorded by an etale duality pairing.
Source: both clauses (blueprint: def-weil-boundary-duality-input). -/
def etalePairingSymmetry {W : FixedEtaleCategory A X} (h : Etale.AmbientDualityPairing A X W)
    (K L : FixedEtaleCategory A X) :=
  (h.choose.app K).app L

/-- The evaluation recorded by a pro-etale duality pairing.
Source: both clauses (blueprint: def-weil-boundary-duality-input). -/
def proPairingEvaluation {W : FixedCategory A X} (h : ProEtale.AmbientDualityPairing A X W)
    (K : FixedCategory A X) :=
  h.choose_spec.2.choose K

end PairingComponents

/-- The normalized site-coordinate realization of all operations in the abstract formulas.
HEq includes endpoints and thus fixes each field to the existing canonical construction.
Source: both clauses (blueprint: def-weil-boundary-duality-input). -/
structure CanonicalOperations {S : Scheme.{u}} (Y : Scheme.{u}) (aY : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [NoetherianSpace Y]
    [IsSeparated aY] [LocallyOfFiniteType aY]
    (composition : ∀ {Z T : Piece Y} (f : Boundary Z T),
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f.map ⋙
          Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (T.structureMap aY) ≅
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (Z.structureMap aY))
    (o : Operations Boundary (fun T : Piece Y ↦ FixedCategory (ModuleCat.{u + 1} Λ) T.scheme)
      (fun T : Piece Y ↦ FixedEtaleCategory (ModuleCat.{u + 1} Λ) T.scheme)) : Prop where
  /-- Recorded pro-etale evaluation with descended Koszul symmetry. -/
  pairing : ∀ T : Piece Y, ProEtale.AmbientDualityPairing
    (ModuleCat.{u + 1} Λ) T.scheme (omega Λ (T.structureMap aY))
  /-- Recorded etale evaluation with descended Koszul symmetry. -/
  etalePairing : ∀ T : Piece Y, Etale.AmbientDualityPairing
    (ModuleCat.{u + 1} Λ) T.scheme (etaleOmega Λ (T.structureMap aY))
  nu : ∀ T, HEq (o.nu T) (comparison (ModuleCat.{u + 1} Λ) T.scheme)
  nuR : ∀ T, HEq (o.nuR T) (comparisonRight (ModuleCat.{u + 1} Λ) T.scheme)
  adj : ∀ T, HEq (o.adj T) (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) T.scheme)
  star : ∀ {Z T} (f : Boundary Z T),
    HEq (o.star f) (upperStar (ModuleCat.{u + 1} Λ) f.map).mapDerivedCategory
  estar : ∀ {Z T} (f : Boundary Z T),
    HEq (o.estar f) (Etale.upperStar (ModuleCat.{u + 1} Λ) f.map).mapDerivedCategory
  estarLeft : ∀ {Z T} (f : Boundary Z T),
    HEq (o.estarLeft f) (Etale.upperStar (ModuleCat.{u + 1} Λ) f.map).leftDerivedFunctor
  estarIso : ∀ {Z T} (f : Boundary Z T),
    HEq (o.estarIso f)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f.map)
  eexc : ∀ {Z T} (f : Boundary Z T),
    HEq (o.eexc f) (Etale.rightDerivedUpperShriek Λ f.map)
  eOmega : ∀ T, HEq (o.eOmega T) (etaleOmega Λ (T.structureMap aY))
  symmetry : ∀ T K L, HEq (o.symmetry T K L) (proPairingSymmetry (pairing T) K L)
  etaleSymmetry : ∀ T K L,
    HEq (o.etaleSymmetry T K L) (etalePairingSymmetry (etalePairing T) K L)
  evaluation : ∀ T K, HEq (o.evaluation T K) (proPairingEvaluation (pairing T) K)
  nuTensor : ∀ T K L, HEq (o.nuTensor T K L)
    ((genericComparisonTensor (comparisonUpperStar (ModuleCat.{u + 1} Λ) T.scheme) K).app L)
  square : ∀ {Z T} (f : Boundary Z T),
    HEq (o.square f) (derivedComparisonPullback (ModuleCat.{u + 1} Λ) f.map)
  etau : ∀ {Z T} (f : Boundary Z T) M N,
    HEq (o.etau f M N) (Etale.rightDerivedUpperShriekTensorMap f.map M N)
  ecomp : ∀ {Z T} (f : Boundary Z T), HEq (o.ecomp f)
    (etaleOmegaComposition Λ f.map (T.structureMap aY) (Z.structureMap aY) (composition f))

/-- Boundary input in site coordinates with every operation fixed by its canonical formula.
Source: both clauses (blueprint: def-weil-boundary-duality-input). -/
def Data {S : Scheme.{u}} (Y : Scheme.{u}) (aY : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [NoetherianSpace Y]
    [IsSeparated aY] [LocallyOfFiniteType aY]
    (ctf : ∀ T : Piece Y, FixedCategory (ModuleCat.{u + 1} Λ) T.scheme → Prop)
    (composition : ∀ {Z T : Piece Y} (f : Boundary Z T),
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f.map ⋙
          Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (T.structureMap aY) ≅
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (Z.structureMap aY)) : Prop :=
  ∃ o : Operations Boundary (fun T : Piece Y ↦ FixedCategory (ModuleCat.{u + 1} Λ) T.scheme)
      (fun T : Piece Y ↦ FixedEtaleCategory (ModuleCat.{u + 1} Λ) T.scheme),
    CanonicalOperations Λ Y aY composition o ∧ Nonempty (Assertions Boundary _ _ o ctf)

/-- The recorded finite-Tor predicate in the canonical fixed-scalar coordinates.
Positive levels are indexed by n+1, covering every integer level at least one.
Source: finite-Tor convention (blueprint: def-weil-boundary-duality-input). -/
def ctf (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (K : FixedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) T) : Prop :=
  WeilConjectures.finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) T
    ((sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K)


/-- The actual compact-support composition along a boundary and its structure morphism.
Source: composition convention (blueprint: def-weil-boundary-duality-input). -/
def finiteComposition (A : Type u) [CommRing A] [Finite A]
    {S : Scheme.{u}} (Y : Scheme.{u}) (aY : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [NoetherianSpace Y]
    [IsSeparated aY] [LocallyOfFiniteType aY]
    {Z T : Piece Y} (f : Boundary Z T) :=
  letI : HasCompactification (f.map ≫ T.structureMap aY) :=
    HasCompactification.of_eq
      ((Category.assoc f.map T.inclusion aY).symm.trans
        (congrArg (fun g : Z.scheme ⟶ Y ↦ g ≫ aY) f.over_eq)).symm
  Etale.unboundedEtaleLowerShriekCompIso (ULift.{u + 1, u} A) f.map (T.structureMap aY) ≪≫
    Etale.unboundedEtaleLowerShriekCongr (ULift.{u + 1, u} A)
      ((Category.assoc f.map T.inclusion aY).symm.trans
        (congrArg (fun g : Z.scheme ⟶ Y ↦ g ≫ aY) f.over_eq))

end AlgebraicGeometry.ProEtale.BoundaryDualityInput

namespace AlgebraicGeometry.ProEtale

/-- The finite-stage boundary duality input on every locally closed piece.
Positive coefficient levels are indexed by n+1. Canonical coordinate normalizations
only transport the existing maps between definitionally equal instance presentations.
Source: blueprint main-20261015, both clauses (blueprint: def-weil-boundary-duality-input). -/
def BoundaryDualityInput
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  letI : IsNoetherian Y := ⟨⟩
  _root_.AlgebraicGeometry.ProEtale.BoundaryDualityInput.Data
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) Y aY
    (fun T ↦ _root_.AlgebraicGeometry.ProEtale.BoundaryDualityInput.ctf l E n T.scheme)
    (_root_.AlgebraicGeometry.ProEtale.BoundaryDualityInput.finiteComposition
      (Padic.coefficientExtensionRing l E (n + 1)) Y aY)

end AlgebraicGeometry.ProEtale
