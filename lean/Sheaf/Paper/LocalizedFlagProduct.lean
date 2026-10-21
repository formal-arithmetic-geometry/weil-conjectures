/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.CompleteFlagBundle
public import Sheaf.Paper.PurityVectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.Paper.SupportedCupFunctoriality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.Paper.ChernFlagFormula
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace

import Sheaf.Paper.SupportedCup
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.KummerAdditivity
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-! # Nested supported Cartier classes of vector subbundles

Source: blueprint main-20261015, localized-top-Chern proof, Steps 2 and 4;
Stacks Tags 01M2, 01X0, 03PL and 0B56 (blueprint: lem-pur-flag-localized-product).

The total space uses the dual module. Ordinary etale representatives are composed
using exact closed direct images and the normalized projection map. The canonical
site comparison then gives the specified pro-etale supported morphisms.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u c v w h h₁ h₂ h₃ h₄ h₅ h₆ c₁ c₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting


/-- The canonical single embedding, elaborated before specializing the coefficient ring.
Source: purity conventions (blueprint: lem-pur-flag-localized-product). -/
abbrev localizedFlagSingleRaw (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0

/-- Reference to the existing degree-zero embedding, with its canonical instances.
Source: purity conventions (blueprint: lem-pur-flag-localized-product). -/
abbrev localizedFlagSingle (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  localizedFlagSingleRaw P.Coefficient X

/-- The existing finite root-power Tate sheaf, in ordinary etale coordinates.
Source: def-coefficient-twists-detailed (blueprint: lem-pur-flag-localized-product). -/
abbrev localizedFlagTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (j : ℤ) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
    P.diagonalExponent_annihilates j

/-- Reference to the actual closed direct image of the coefficient sheaf.
Source: lem-amb-closed-support-hom (blueprint: lem-pur-flag-localized-product). -/
abbrev localizedFlagSource (P : PurityFiniteSetting.{u}) {Y X : Scheme.{u}} (a : Y ⟶ X) :=
  Etale.closedConstantModule P.Coefficient a

/-- The supported-Hom coordinates with the canonical ordinary-etale instances.
Source: lem-amb-closed-support-hom (blueprint: lem-pur-flag-localized-product). -/
abbrev LocalizedFlagH (P : PurityFiniteSetting.{u}) {Y X : Scheme.{u}}
    (a : Y ⟶ X) (n j : ℤ) :=
  (P.localizedFlagSingle X).obj (P.localizedFlagSource a) ⟶
    ((P.localizedFlagSingle X).obj (P.localizedFlagTwist X j))⟦n⟧

/-- Reference to restriction of constants onto a closed support.
Source: def-pur-supported-cup (blueprint: lem-pur-flag-localized-product). -/
abbrev localizedFlagRestriction (P : PurityFiniteSetting.{u}) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] := Etale.closedConstantSectionMap P.Coefficient a


/-- The symmetric-algebra map on the transpose of a bundle inclusion.
Source: Stacks 01M2, degree-one universal property
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagAlgebraMap {S : Scheme.{u}} {M N : S.Modules} (d : M ⟶ N) :
    SymmetricAlgebraSheaf.algebra (Scheme.Modules.dual N) ⟶
      SymmetricAlgebraSheaf.algebra (Scheme.Modules.dual M) :=
  (exists_quasiCoherentSymmetricAlgebra_core S (Scheme.Modules.dual N)
    (SymmetricAlgebraSheaf.algebra (Scheme.Modules.dual M))
    (Scheme.Modules.dualMap d ≫
      SymmetricAlgebraSheaf.inclusion (Scheme.Modules.dual M))).choose

/-- Relative Spec sends the transpose algebra map to the actual inclusion of total spaces.
Source: Stacks 01M2 and 01LX (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagTotalMap {S : Scheme.{u}} [IsNoetherian S]
    {m n : ℕ} {M N : S.Modules}
    [hm : (Scheme.Modules.dual M).IsFiniteLocallyFreeOfRank m]
    [hn : (Scheme.Modules.dual N).IsFiniteLocallyFreeOfRank n] (d : M ⟶ N) :
    VectorBundleZeroSection.scheme S m (Scheme.Modules.dual M) ⟶
      VectorBundleZeroSection.scheme S n (Scheme.Modules.dual N) :=
  ((VectorBundleZeroSection.antiEquivalence S).inverse.map
    (ObjectProperty.homMk (localizedFlagAlgebraMap d))).unop.hom.left

/-- The counit-normalized projection with a specified coefficient pullback comparison.
The coefficient category is kept abstract while forming this canonical mate.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagProjectionRaw (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (a : Y ⟶ X)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (e : (Etale.upperStar (ModuleCat.{u + 1} A) a).obj L ≅ M) :
    Etale.closedConstantModule A a ⊗ L ⟶
      (Etale.lowerStar (ModuleCat.{u + 1} A) a).obj M :=
  (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).homEquiv _ _
    (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) a) _ _ ≫
      tensorHom ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) a).counit.app (Etale.ordinaryFiniteConstant A Y)) e.hom ≫
      (λ_ _).hom)

/-- Canonical flat-tensor projection, with the coefficient category abstract.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagDerivedProjectionModel
    {B : Type c} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology B ⥤ Sheaf X.smallEtaleTopology B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : Sheaf Y.smallEtaleTopology B) (T : Sheaf X.smallEtaleTopology B)
    (M : Sheaf Y.smallEtaleTopology B) (h : ObjectProperty.flat (F.obj L))
    (f : F.obj L ⊗ T ⟶ F.obj M) :=
  Etale.closedConstantFlatModelMap (B := B) (X := X) (F.obj L) T (F.obj M) h f ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app M


/-- Specialization to the counit mate.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagDerivedProjectionRaw (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (a : Y ⟶ X) [IsClosedImmersion a]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (e : (Etale.upperStar (ModuleCat.{u + 1} A) a).obj L ≅ M) :=
  localizedFlagDerivedProjectionModel (B := ModuleCat.{u + 1} A)
    (Etale.lowerStar (ModuleCat.{u + 1} A) a) (Etale.ordinaryFiniteConstant A Y) L M
    (Etale.closedConstantModule_flat A a) (localizedFlagProjectionRaw A a L M e)


/-- The finite-root projection before specializing the purity coefficient ring.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagFiniteProjection (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] (hX : IsUnit (N : Γ(X, ⊤))) (j : ℤ) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((DerivedCategory.singleFunctor _ 0).obj (Etale.closedConstantModule A a))).obj
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N X hA j)) ⟶
    (Etale.lowerStar (ModuleCat.{u + 1} A) a).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N Y hA j)) :=
  localizedFlagDerivedProjectionRaw A a
    (Scheme.finiteEtaleTateSheaf A N X hA j) (Scheme.finiteEtaleTateSheaf A N Y hA j)
    (Etale.p1DecompositionSheafPullback A N hN hA a hX j)

/-- The finite-root counit projection is invertible.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product).
Proof: trivialize the root line etale locally. Every signed power is then the free
rank-one coefficient module. The counit mate becomes the identity on the closed
constant module. Its inverse glues because the mate is canonical. Flat degree-zero
tensor comparison and exactness of closed direct image preserve this inverse. -/
theorem localizedFlagFiniteProjection_isIso (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] (hX : IsUnit (N : Γ(X, ⊤))) (j : ℤ) :
    IsIso (localizedFlagFiniteProjection A N hN hA a hX j) := by
  sorry


/-- Select an object determined uniquely by its normalization.
Source: Stacks 0A45 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagUniqueWitness {α : Sort w} {p : α → Prop} (h : ∃! x, p x) : α :=
  h.exists.choose


/-- Realize a degree-two Ext class without specializing its ambient category.
Source: Stacks 0A45 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagExtHom {B : Type c} [Category.{v} B] [Abelian B]
    [CategoryTheory.HasExt.{w} B] [HasDerivedCategory.{w} B]
    {F G : B} (x : CategoryTheory.Abelian.Ext F G 2) := x.hom

/-- Select precisely the supported Ext class fixed by its relative Kummer boundary.
Source: Stacks 03PL and 0A45 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagCartierClass (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤))) :
    CategoryTheory.Abelian.Ext (Etale.closedConstantModule A a)
      (Scheme.finiteEtaleTateLine X N A hA) 2 :=
  localizedFlagUniqueWitness
    (Etale.ordinary_supported_kummer_uniqueBoundary X N hN A hA hX a hI)

/-- The uniquely boundary-normalized ordinary Cartier class in derived coordinates.
Source: Stacks 03PL and 0A45 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagCartierRaw (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤))) :=
  localizedFlagExtHom (localizedFlagCartierClass A N hN hA a hI hX)

/-- The root line and every signed power are flat.
Source: lem-pur-twist-sheaf-locally-free and the signed Tate comparisons
(blueprint: lem-pur-flag-localized-product).
Proof: the root-line construction is etale locally a free rank-one coefficient
module. Tensor powers and duals preserve that description. Tensor with a free
rank-one module is exact, and flatness is local, giving the assertion. -/
theorem localizedFlagTwist_flat (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (j : ℤ) :
    ObjectProperty.flat (P.localizedFlagTwist X j) := by
  sorry

/-- Tensor a degree-two class with a flat line, using the canonical shifted tensor
comparison and the specified ordinary line multiplication.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagTensorCartierModel
    {B : Type c} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} (U V L W : Sheaf X.smallEtaleTopology B)
    (d : (DerivedCategory.singleFunctor _ 0).obj U ⟶
      ((DerivedCategory.singleFunctor _ 0).obj V)⟦(2 : ℤ)⟧)
    (hV : ObjectProperty.flat V) (m : V ⊗ L ⟶ W) :
    ((Etale.derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj U)).obj
        ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj W)⟦(2 : ℤ)⟧ :=
  Etale.derivedTensorHom B d ((shiftFunctorZero _ ℤ).inv.app
    ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
    (Etale.derivedTensorShiftIso B
      ((DerivedCategory.singleFunctor _ 0).obj V)
      ((DerivedCategory.singleFunctor _ 0).obj L) 2 0).hom ≫
    (Etale.closedConstantFlatModelMap V L W hV m)⟦(2 : ℤ)⟧'


/-- Multiply the twists and reindex the result before specializing the sheaf category.
Source: blueprint Step 4, constant-coefficient twist identifications
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagTwistMultiply {C : Type c} [Category.{v} C] [MonoidalCategory C]
    (L : ℤ → C) (p : ∀ a b : ℤ, L a ⊗ L b ≅ L (a + b)) (j : ℕ) :
    L 1 ⊗ L (j : ℤ) ⟶ L ((j + 1 : ℕ) : ℤ) :=
  (p 1 (j : ℤ)).hom ≫ eqToHom (congrArg L
    (by omega : 1 + (j : ℤ) = ((j + 1 : ℕ) : ℤ)))

/-- The explicit tensor composite, with endpoint presentations transported by HEq.
All inputs to the model, including the divisor arrow and twist multiplication, are fixed.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagTensorCharacterization
    {B : Type c} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} (U₀ V₀ L₀ W₀ : Sheaf X.smallEtaleTopology B)
    {D₀ : Type (u + 1)} (d₀ : D₀) {M₀ : Type (u + 1)} (m₀ : M₀)
    {H₀ : Type (u + 1)} (γ : H₀) : Prop :=
  ∃ (U V L W : Sheaf X.smallEtaleTopology B)
    (d : (DerivedCategory.singleFunctor _ 0).obj U ⟶
      ((DerivedCategory.singleFunctor _ 0).obj V)⟦(2 : ℤ)⟧)
    (hV : ObjectProperty.flat V) (m : V ⊗ L ⟶ W),
    U = U₀ ∧ V = V₀ ∧ L = L₀ ∧ W = W₀ ∧ HEq d d₀ ∧ HEq m m₀ ∧
      HEq γ (localizedFlagTensorCartierModel U V L W d hV m)

/-- Normalization by the actual Cartier arrow and the normalized root multiplication.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagTensorRawCharacterization (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤))) (j : ℕ) {H₀ : Type (u + 1)} (γ : H₀) : Prop :=
  LocalizedFlagTensorCharacterization (B := ModuleCat.{u + 1} A)
    (Etale.closedConstantModule A a) (Scheme.finiteEtaleTateSheaf A N X hA 1)
    (Scheme.finiteEtaleTateSheaf A N X hA (j : ℤ))
    (Scheme.finiteEtaleTateSheaf A N X hA ((j + 1 : ℕ) : ℤ))
    (localizedFlagCartierRaw A N hN hA a hI hX)
    (localizedFlagTwistMultiply (Scheme.finiteEtaleTateSheaf A N X hA)
      (functorialCupTwistProductGeneral A N hN hA X hX) j) γ

/-- The explicit tensor composite has a unique realization in the concrete Hom type.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product).
Proof: take the four displayed sheaves. The degree-one root line is flat by its
normalized root/dual pairing. Transport the given Cartier arrow and multiplication
through their identical endpoint presentations and apply localizedFlagTensorCartierModel.
Unfolding singleFunctor and the finite twist identifies its endpoints with the displayed
Hom type. HEq fixes every input and the output; eliminating these equalities proves
uniqueness. Flatness proofs agree by proof irrelevance. No morphism data are forgotten. -/
theorem localizedFlagTensorRaw_realization (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤))) (j : ℕ) :
    ∃! γ : ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((localizedFlagSingleRaw A X).obj (Etale.closedConstantModule A a))).obj
        ((localizedFlagSingleRaw A X).obj
          (Scheme.finiteEtaleTateSheaf A N X hA (j : ℤ))) ⟶
      ((localizedFlagSingleRaw A X).obj
        (Scheme.finiteEtaleTateSheaf A N X hA ((j + 1 : ℕ) : ℤ)))⟦(2 : ℤ)⟧,
      LocalizedFlagTensorRawCharacterization A N hN hA a hI hX j γ := by
  sorry

/-- The same explicit tensor composite, transported to its concrete endpoints.
Its uniqueness predicate retains every factor of localizedFlagTensorCartierModel.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagTensorCartierRaw (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {Y X : Scheme.{u}}
    (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤))) (j : ℕ) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((localizedFlagSingleRaw A X).obj (Etale.closedConstantModule A a))).obj
        ((localizedFlagSingleRaw A X).obj
          (Scheme.finiteEtaleTateSheaf A N X hA (j : ℤ))) ⟶
      ((localizedFlagSingleRaw A X).obj
        (Scheme.finiteEtaleTateSheaf A N X hA ((j + 1 : ℕ) : ℤ)))⟦(2 : ℤ)⟧ :=
  localizedFlagUniqueWitness (localizedFlagTensorRaw_realization A N hN hA a hI hX j)


/-- Push a shifted single-object class through an exact functor and compose it
with the next shifted arrow, using the canonical single and shift comparisons.
Source: blueprint Step 4; Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagComposeModel {C : Type c₁} {D : Type c₂}
    [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M N : C) (U V : D) (n m : ℤ) (b : U ≅ F.obj M)
    (θ : (DerivedCategory.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.singleFunctor C 0).obj N)⟦n⟧)
    (d : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj N) ⟶
      ((DerivedCategory.singleFunctor D 0).obj V)⟦m⟧) :
    (DerivedCategory.singleFunctor D 0).obj U ⟶
      ((DerivedCategory.singleFunctor D 0).obj V)⟦m + n⟧ :=
  (DerivedCategory.singleFunctor D 0).map b.hom ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫
    F.mapDerivedCategory.map θ ≫
    (F.mapDerivedCategory.commShiftIso n).hom.app _ ≫ d⟦n⟧' ≫
    (shiftFunctorAdd _ m n).inv.app _

/-- The actual exact-image composite, with all endpoint and arrow data fixed by HEq.
The shift label may have an equal presentation in the concrete Hom group.
Source: blueprint Step 4; Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagComposeCharacterization {C : Type c₁} {D : Type c₂}
    [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F₀ : Type (max c₁ c₂ v₁ v₂)} (functor₀ : F₀)
    {M₀ N₀ : Type c₁} (source₀ : M₀) (target₀ : N₀)
    {U₀ V₀ : Type c₂} (source₁ : U₀) (target₁ : V₀) (n m : ℤ)
    {B₀ : Type v₂} (b₀ : B₀) {T₀ : Type w₁} (θ₀ : T₀)
    {P₀ T₁ : Type w₂} (p₀ : P₀) (t₀ : T₁) {H₀ : Type w₂} (γ : H₀) : Prop :=
  ∃ (F : C ⥤ D) (_ : F.Additive) (_ : PreservesFiniteLimits F)
    (_ : PreservesFiniteColimits F) (M N : C) (U V : D) (b : U ≅ F.obj M)
    (θ : (DerivedCategory.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.singleFunctor C 0).obj N)⟦n⟧)
    (W : DerivedCategory D)
    (p : W ⟶ F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj N))
    (_ : IsIso p) (t : W ⟶ ((DerivedCategory.singleFunctor D 0).obj V)⟦m⟧),
    HEq F functor₀ ∧ HEq M source₀ ∧ HEq N target₀ ∧ HEq U source₁ ∧ HEq V target₁ ∧
      HEq b b₀ ∧ HEq θ θ₀ ∧ HEq p p₀ ∧ HEq t t₀ ∧
      HEq γ (localizedFlagComposeModel F M N U V n m b θ (inv p ≫ t))

/-- The inverse of a specified invertible arrow, formed in its ambient category.
Source: Stacks 0B56 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagInverse {C : Type c} [Category.{v} C] {U V : C}
    (f : U ⟶ V) (h : IsIso f) : V ⟶ U := @inv C _ U V f h

/-- The specified direct-image, inverse-projection and Cartier factors over a finite ring.
Source: blueprint Steps 2 and 4; Stacks 0B56
(blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagComposeRawNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) {S Y X : Scheme.{u}}
    (z : S ⟶ Y) (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤))) (j : ℕ)
    {T₀ : Type (u + 1)} (θ : T₀)
    {H₀ : Type (u + 1)} (γ : H₀) : Prop :=
  LocalizedFlagComposeCharacterization
    (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Etale.lowerStar (ModuleCat.{u + 1} A) a)
    (Etale.closedConstantModule A z) (Scheme.finiteEtaleTateSheaf A N Y hA (j : ℤ))
    (Etale.closedConstantModule A (z ≫ a))
    (Scheme.finiteEtaleTateSheaf A N X hA ((j + 1 : ℕ) : ℤ)) (2 * (j : ℤ)) 2
    ((Etale.lowerStarComp (ModuleCat.{u + 1} A) z a (z ≫ a) rfl).symm.app
      (Etale.constantModuleSheaf A S)) θ
    (localizedFlagFiniteProjection A N hN hA a hX (j : ℤ))
    (localizedFlagTensorCartierRaw A N hN hA a hI hX j) γ

/-- Specialize the exact same composition normalization to the finite purity datum.
Source: blueprint Steps 2 and 4 (blueprint: lem-pur-flag-localized-product). -/
abbrev LocalizedFlagComposeNormalization (P : PurityFiniteSetting.{u}) {S Y X : Scheme.{u}}
    (z : S ⟶ Y) (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (aX : X ⟶ Spec (.of P.field.k)) (j : ℕ)
    {T₀ : Type (u + 1)} (θ : T₀) {H₀ : Type (u + 1)} (γ : H₀) : Prop :=
  LocalizedFlagComposeRawNormalization P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates z a hI (P.diagonalExponent_isUnit aX) j θ γ

/-- The explicit exact-image composite has a unique realization at the given endpoints.
Source: blueprint Steps 2 and 4; Stacks 0B56
(blueprint: lem-pur-flag-localized-product).
Proof: use the direct-image composition comparison, the given preceding class,
and inverse projection followed by the tensored Cartier class as the three model inputs.
Unfold the endpoint abbreviations; 2+2j=2(j+1) identifies the shift labels. Transport
localizedFlagComposeModel through these equalities. HEq fixes the direct-image comparison,
preceding class, projection and Cartier factors, and therefore the output. Eliminating the
endpoint equalities gives uniqueness. -/
theorem localizedFlagCompose_realization (P : PurityFiniteSetting.{u})
    {S Y X : Scheme.{u}} (z : S ⟶ Y) (a : Y ⟶ X) [IsClosedImmersion a]
    (hI : a.ker.IsInvertible) (aX : X ⟶ Spec (.of P.field.k)) (j : ℕ)
    (θ : P.LocalizedFlagH z (2 * (j : ℤ)) (j : ℤ)) :
    ∃! γ : P.LocalizedFlagH (z ≫ a)
      (2 * ((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ),
      P.LocalizedFlagComposeNormalization z a hI aX j θ γ := by
  sorry

/-- Push the preceding supported class forward, then apply inverse projection and
its tensored Cartier map. The uniqueness predicate retains the explicit model factors.
Source: blueprint Steps 2 and 4; Stacks 0B56
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagCompose (P : PurityFiniteSetting.{u}) {S Y X : Scheme.{u}}
    (z : S ⟶ Y) (a : Y ⟶ X) [IsClosedImmersion a] (hI : a.ker.IsInvertible)
    (aX : X ⟶ Spec (.of P.field.k)) (j : ℕ)
    (θ : P.LocalizedFlagH z (2 * (j : ℤ)) (j : ℤ)) :
    P.LocalizedFlagH (z ≫ a) (2 * ((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ) :=
  localizedFlagUniqueWitness (P.localizedFlagCompose_realization z a hI aX j θ)


/-- A filtration with ambient quotient and line quotient properties.
Source: def-pur-complete-flag-bundle (blueprint: lem-pur-flag-localized-product). -/
structure LocalizedFlagFiltrationModel (C : Type c) [Category.{v} C]
    (quotient : ∀ {M N : C}, (M ⟶ N) → C)
    (r : ℕ) (invertible : C → Prop) where
  H : Fin (r + 1) → C
  step : ∀ j : Fin r, H j.castSucc ⟶ H j.succ
  mono : ∀ j : Fin r, Mono (step j)
  zero : IsZero (H 0)
  line : ∀ j : Fin r, invertible (quotient (step j))

/-- A filtration by vector subbundles with line quotients, using the recorded predicates.
Source: def-pur-complete-flag-bundle (blueprint: lem-pur-flag-localized-product). -/
abbrev LocalizedFlagFiltration (S : Scheme.{u}) (r : ℕ) :=
  LocalizedFlagFiltrationModel S.Modules (fun {_ _} f ↦ cokernel f) r
    (fun M : S.Modules ↦ M.IsInvertible)

/-- The i-th subbundle and its dual have rank i.
Source: blueprint localized-top-Chern proof Step 2; Stacks 02UL
(blueprint: lem-pur-flag-localized-product).
Proof: locally trivialize each line quotient and lift its generator through the
quotient epimorphism. On a smaller affine open those lifts split the surjections.
Induction appends the lifted vector to the preceding frame, producing an adapted
frame of H_i of length i; its dual frame proves the stated dual rank. The finite
intersection of these opens works for every level. This includes i=0 and the empty base. -/
theorem localizedFlagDualRank {S : Scheme.{u}} {r : ℕ}
    (D : LocalizedFlagFiltration S r) (i : Fin (r + 1)) :
    (Scheme.Modules.dual (D.H i)).IsFiniteLocallyFreeOfRank i.val := by
  sorry

/-- The chosen total space is exactly Spec Sym(H_i dual), with its augmentation zero.
Source: Stacks 01M2; def-pur-vector-bundle-zero-section
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagBundle (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) (i : Fin (r + 1)) :
    PurityVectorBundle P S aS i.val :=
  letI := isNoetherian_of_locallyOfFiniteType aS
  letI := localizedFlagDualRank D i
  { E := VectorBundleZeroSection.scheme S i.val (Scheme.Modules.dual (D.H i))
    p := VectorBundleZeroSection.π S i.val (Scheme.Modules.dual (D.H i))
    𝓔 := Scheme.Modules.dual (D.H i)
    phi := Iso.refl _
    over_commutes := Category.id_comp _ }

/-- The successive total-space inclusion is Spec of Sym of the transpose inclusion.
Source: Stacks 01M2 and 01X0 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagInclusion (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) (j : Fin r) :
    (P.localizedFlagBundle aS D j.castSucc).E ⟶ (P.localizedFlagBundle aS D j.succ).E :=
  letI := isNoetherian_of_locallyOfFiniteType aS
  letI := localizedFlagDualRank D j.castSucc
  letI := localizedFlagDualRank D j.succ
  localizedFlagTotalMap (D.step j)

/-- Geometry of the nested total spaces, including the divisor line and compatibility
with the projection and augmentation zero sections.
Source: Stacks 01X0; blueprint localized-top-Chern proof Steps 2 and 4
(blueprint: lem-pur-flag-localized-product).
Proof: in the adapted frame of localizedFlagDualRank, the dual symmetric algebra
is R[t_1,...,t_i]. The transpose map sends the last coordinate to zero and fixes
all previous coordinates. Thus its spectrum is the closed immersion t_i=0, with
invertible ideal (t_i), and augmentation sections and projections commute.
Multiplication by t_i is injective over every ring. The image of the tautological
vector in the quotient line is t_i times its frame, so this divisor has associated
line pi_i*Q_i by Stacks 01X0. Polynomial charts are smooth over the base, hence all
projections are smooth. At rank zero the augmentation is the identity on R, so
its zero section is an isomorphism. Each zero section is closed by its surjective
augmentation, as in def-pur-vector-bundle-zero-section. -/
def LocalizedFlagGeometry (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) : Prop :=
    (∀ i : Fin (r + 1), Smooth (P.localizedFlagBundle aS D i).p ∧
      IsClosedImmersion (P.localizedFlagBundle aS D i).zeroSection) ∧
    IsIso (P.localizedFlagBundle aS D 0).zeroSection ∧
    ∀ j : Fin r, IsClosedImmersion (P.localizedFlagInclusion aS D j) ∧
      (P.localizedFlagInclusion aS D j).ker.IsInvertible ∧
      P.localizedFlagInclusion aS D j ≫ (P.localizedFlagBundle aS D j.succ).p =
        (P.localizedFlagBundle aS D j.castSucc).p ∧
      (P.localizedFlagBundle aS D j.castSucc).zeroSection ≫
        P.localizedFlagInclusion aS D j = (P.localizedFlagBundle aS D j.succ).zeroSection ∧
      Nonempty ((P.localizedFlagInclusion aS D j).ker.toModules ≅
        Scheme.Modules.dual ((Scheme.Modules.tensorPullback
          (P.localizedFlagBundle aS D j.succ).p).obj (cokernel (D.step j))))


/-- The polynomial-chart geometry collected in LocalizedFlagGeometry.
Source: Stacks 01X0; blueprint localized-top-Chern proof Steps 2 and 4
(blueprint: lem-pur-flag-localized-product).
Proof: choose adapted frames by lifting the generators of the successive line
quotients. The total spaces become affine polynomial spaces and the inclusions
set the last coordinate to zero. Polynomial coordinates are nonzerodivisors over
any base ring, and the ideal transforms as the dual of the pulled-back quotient
line. Augmentations commute with setting a coordinate to zero. These charts also
prove smoothness, closedness of every augmentation zero, and the rank-zero isomorphism. -/
theorem localizedFlagGeometry (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) : P.LocalizedFlagGeometry aS D := by
  sorry

/-- Closedness of the actual nested divisor, supplied by the polynomial-chart theorem.
Source: Stacks 01X0 (blueprint: lem-pur-flag-localized-product). -/
instance localizedFlagInclusion_closed (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) (j : Fin r) :
    IsClosedImmersion (P.localizedFlagInclusion aS D j) :=
  ((P.localizedFlagGeometry aS D).2.2 j).1

/-- Closedness of the augmentation section of each actual total space.
Source: Stacks 01M2 (blueprint: lem-pur-flag-localized-product). -/
instance localizedFlagZero_closed (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) (i : Fin (r + 1)) :
    IsClosedImmersion (P.localizedFlagBundle aS D i).zeroSection :=
  ((P.localizedFlagGeometry aS D).1 i).2

/-- At rank zero restriction of constants to the zero section is invertible.
Source: blueprint localized-top-Chern proof, rank-zero normalization
(blueprint: lem-pur-flag-localized-product).
Proof: the rank-zero augmentation is an isomorphism by localizedFlagGeometry;
the constant-unit comparison along an isomorphism is invertible. Restriction is
that comparison followed by the adjunction unit, hence is invertible as well. -/
theorem localizedFlagZeroRestriction_isIso (P : PurityFiniteSetting.{u})
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) :
    IsIso (P.localizedFlagRestriction (P.localizedFlagBundle aS D 0).zeroSection) := by
  sorry

/-- The initial supported class is inverse restriction, with the zero shift.
Source: blueprint Steps 2 and 4 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagInitialModel {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {U V : C} (ρ : U ⟶ V) (h : IsIso ρ) :=
  (DerivedCategory.singleFunctor C 0).map (localizedFlagInverse ρ h) ≫
    (shiftFunctorZero _ ℤ).inv.app ((DerivedCategory.singleFunctor C 0).obj U)

/-- The zero class and every successor are fixed by the actual nested composition.
HEq transports only endpoint presentations, including the zero-section composition law.
Source: blueprint Steps 2 and 4 (blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagThetaNormalization (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r)
    (θ : ∀ i : Fin (r + 1), P.LocalizedFlagH
      (P.localizedFlagBundle aS D i).zeroSection (2 * (i.val : ℤ)) (i.val : ℤ)) : Prop :=
  HEq (θ 0)
    (localizedFlagInitialModel
      (P.localizedFlagRestriction (P.localizedFlagBundle aS D 0).zeroSection)
      (P.localizedFlagZeroRestriction_isIso aS D)) ∧
    ∀ j : Fin r, HEq (θ j.succ)
      (P.localizedFlagCompose (P.localizedFlagBundle aS D j.castSucc).zeroSection
        (P.localizedFlagInclusion aS D j) ((P.localizedFlagGeometry aS D).2.2 j).2.1
        ((P.localizedFlagBundle aS D j.succ).p ≫ aS) j.val (θ j.castSucc))

/-- The nested recursion determines one and only one family of supported morphisms.
Source: blueprint Steps 2 and 4 (blueprint: lem-pur-flag-localized-product).
Proof: construct the family by Fin.induction. At zero take inverse restriction of
constants, followed by the zero-shift comparison. At the successor apply the specified
localizedFlagCompose and transport its source along z_(j+1)=z_j followed by a_(j+1),
which is localizedFlagGeometry's zero-section equation. The degree and twist labels
agree by successor arithmetic. Equality elimination proves the two HEq normalizations.
Fin.induction and the same equations prove equality of any two such families. -/
theorem localizedFlagTheta_existsUnique (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) :
    ∃! θ : ∀ i : Fin (r + 1), P.LocalizedFlagH
      (P.localizedFlagBundle aS D i).zeroSection (2 * (i.val : ℤ)) (i.val : ℤ),
      P.LocalizedFlagThetaNormalization aS D θ := by
  sorry

/-- The canonically normalized nested supported class, including its rank-zero identity.
Its uniquely determining recursion uses the actual closed direct images and Cartier maps.
Source: blueprint Steps 2 and 4 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagTheta (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) :
    ∀ i : Fin (r + 1), P.LocalizedFlagH
      (P.localizedFlagBundle aS D i).zeroSection (2 * (i.val : ℤ)) (i.val : ℤ) :=
  localizedFlagUniqueWitness (P.localizedFlagTheta_existsUnique aS D)


/-- The normalized product with the successor twist label, in an abstract category.
Source: blueprint Step 4, Tate identifications
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagTwistProductNext {C : Type c} [Category.{v} C] [MonoidalCategory C]
    (L : ℤ → C) (p : ∀ a b : ℤ, L a ⊗ L b ≅ L (a + b)) (j : ℕ) :
    L (j : ℤ) ⊗ L 1 ≅ L ((j + 1 : ℕ) : ℤ) :=
  p (j : ℤ) 1 ≪≫ eqToIso (congrArg L
    (by omega : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ)))

/-- Assemble the actual flat-single, shifted-tensor and twist-product isomorphisms.
The coefficient category and endpoint families are abstract while composing them.
Source: blueprint Step 4, Tate identifications; Stacks 0B56
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagPowerModel
    {B : Type c} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} (L : ℤ → Sheaf X.smallEtaleTopology B)
    (K : ℕ → DerivedCategory (Sheaf X.smallEtaleTopology B))
    (base : K 0 ≅ (DerivedCategory.singleFunctor _ 0).obj (L 0))
    (step : ∀ j : ℕ, K (j + 1) ≅
      ((Etale.derivedTensor B X).obj (K j)).obj
        (((DerivedCategory.singleFunctor _ 0).obj (L 1))⟦(2 : ℤ)⟧))
    (flat : ∀ j : ℕ, ObjectProperty.flat (L (j : ℤ)))
    (mul : ∀ j : ℕ, L (j : ℤ) ⊗ L 1 ≅ L ((j + 1 : ℕ) : ℤ)) :
    (j : ℕ) → K j ≅
      ((DerivedCategory.singleFunctor _ 0).obj (L (j : ℤ)))⟦2 * (j : ℤ)⟧ :=
  Nat.rec (base ≪≫ (shiftFunctorZero _ ℤ).symm.app _)
    (fun j previous ↦ step j ≪≫
      ((Etale.derivedTensor B X).flip.obj
        (((DerivedCategory.singleFunctor _ 0).obj (L 1))⟦(2 : ℤ)⟧)).mapIso previous ≪≫
      Etale.derivedTensorShiftIso B
        ((DerivedCategory.singleFunctor _ 0).obj (L (j : ℤ)))
        ((DerivedCategory.singleFunctor _ 0).obj (L 1)) (2 * (j : ℤ)) 2 ≪≫
      (shiftFunctor _ (2 * (j : ℤ) + 2)).mapIso
        (Etale.singleFunctorObjTensorIso (L (j : ℤ)) (L 1) (flat j) ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso (mul j)) ≪≫
      eqToIso (congrArg
        (fun t : ℤ ↦ ((DerivedCategory.singleFunctor _ 0).obj
          (L ((j + 1 : ℕ) : ℤ)))⟦t⟧)
        (by omega : 2 * (j : ℤ) + 2 = 2 * ((j + 1 : ℕ) : ℤ))))

/-- Every datum of the explicit positive-power model is fixed; HEq changes only its
endpoint presentation. In particular the model's recursion is not an arbitrary isomorphism.
Source: blueprint Step 4 (blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagPowerCharacterization
    {B : Type c} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} {L₀ : Type (max (u + 1) c)} (line : L₀)
    {K₀ : Type (max (u + 1) c)} (powers : K₀)
    {Z₀ : Type (u + 1)} (zero : Z₀) {S₀ : Type (u + 1)} (successor : S₀)
    {F₀ : Prop} (flat₀ : F₀) {M₀ : Type (u + 1)} (product : M₀)
    {H₀ : Type (u + 1)} (γ : H₀) (j : ℕ) : Prop :=
  ∃ (L : ℤ → Sheaf X.smallEtaleTopology B)
    (K : ℕ → DerivedCategory (Sheaf X.smallEtaleTopology B))
    (base : K 0 ≅ (DerivedCategory.singleFunctor _ 0).obj (L 0))
    (step : ∀ n : ℕ, K (n + 1) ≅
      ((Etale.derivedTensor B X).obj (K n)).obj
        (((DerivedCategory.singleFunctor _ 0).obj (L 1))⟦(2 : ℤ)⟧))
    (flat : ∀ n : ℕ, ObjectProperty.flat (L (n : ℤ)))
    (mul : ∀ n : ℕ, L (n : ℤ) ⊗ L 1 ≅ L ((n + 1 : ℕ) : ℤ)),
    HEq L line ∧ HEq K powers ∧ HEq base zero ∧ HEq step successor ∧
      HEq flat flat₀ ∧ HEq mul product ∧ HEq γ (localizedFlagPowerModel L K base step flat mul j)

/-- The model's concrete inputs are the published positive powers, identity zero and
successor identifications, flat signed twists, and normalized root multiplication.
Source: def-coefficient-twists-detailed and blueprint Step 4
(blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagPowerNormalization (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) {H₀ : Type (u + 1)} (γ : H₀) (j : ℕ) : Prop :=
  LocalizedFlagPowerCharacterization (B := ModuleCat.{u + 1} P.Coefficient) (X := X)
    (P.localizedFlagTwist X) (P.diagonalTwistEtale X)
    (Iso.refl (P.diagonalTwistEtale X 0))
    (fun n : ℕ ↦ Iso.refl (P.diagonalTwistEtale X (n + 1)))
    (fun n : ℕ ↦ P.localizedFlagTwist_flat X aX (n : ℤ))
    (localizedFlagTwistProductNext (P.localizedFlagTwist X)
      (functorialCupTwistProductGeneral P.Coefficient P.diagonalExponent
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
        P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit aX))) γ j

/-- The explicitly normalized power comparison has a unique concrete realization.
Source: blueprint Step 4, signed/positive Tate identifications
(blueprint: lem-pur-flag-localized-product).
Proof: unfold diagonalTwistEtale as affineLinearBaseCoefficient. Its zero is the
constant single object and its successor is the preceding power tensor the shifted
root line, so identity gives the specified base and successor comparisons. The
signed twist at a nonnegative integer is the same finite sheaf power. Its flatness
and the normalized root product supply the remaining two inputs. Transport the
explicit localizedFlagPowerModel along these equal endpoint presentations. Eliminating
the HEq equations fixes every input and the output, proving uniqueness. -/
theorem localizedFlagPower_realization (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (j : ℕ) :
    ∃! γ : P.diagonalTwistEtale X j ≅
      ((P.localizedFlagSingle X).obj (P.localizedFlagTwist X (j : ℤ)))⟦2 * (j : ℤ)⟧,
      P.LocalizedFlagPowerNormalization X aX γ j := by
  sorry

/-- The actual canonical comparison between positive shifted powers and signed twists.
Its unique normalization retains the flat tensor comparison, shifts, and root product.
Source: def-coefficient-twists-detailed and blueprint Step 4
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagPowerComparison (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (j : ℕ) :
    P.diagonalTwistEtale X j ≅
      ((P.localizedFlagSingle X).obj (P.localizedFlagTwist X (j : ℤ)))⟦2 * (j : ℤ)⟧ :=
  localizedFlagUniqueWitness (P.localizedFlagPower_realization X aX j)

/-- The first i quotient Chern classes, in their given order. This restricts the
existing Kummer root family and introduces no new first Chern class.
Source: lem-pur-kummer-additivity and lem-pur-chern-flag-formula
(blueprint: lem-pur-flag-localized-product). -/
def localizedFlagRoots (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k)) {r : ℕ}
    (D : LocalizedFlagFiltration S r) (i : Fin (r + 1)) :
    Fin i.val → (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧) :=
  fun j ↦ P.ordinaryFiniteFlagRoot aS
    (cokernel (D.step (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)))
    (D.line (Fin.castLE (Nat.le_of_lt_succ i.isLt) j))

/-- Forget support, change target coordinates and apply the specified exact comparison.
Source: Stacks 099R and blueprint Step 4 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagForgetModel {C : Type c₁} {D : Type c₂}
    [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {U V : C} {K L : DerivedCategory C} (ρ : U ⟶ V)
    (θ : (DerivedCategory.singleFunctor C 0).obj V ⟶ K) (e : L ≅ K) :=
  F.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map ρ ≫ θ ≫ e.inv)

/-- The exact forget-support model with every input fixed, allowing only endpoint transport.
Source: Stacks 099R and blueprint Step 4 (blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagForgetCharacterization {C : Type c₁} {D : Type c₂}
    [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F₀ : Type (max c₁ c₂ v₁ v₂)} (functor₀ : F₀)
    {R₀ : Type v₁} (restriction : R₀) {T₀ E₀ : Type w₁} (theta : T₀) (power : E₀)
    {H₀ : Type w₂} (γ : H₀) : Prop :=
  ∃ (F : C ⥤ D) (_ : F.Additive) (_ : PreservesFiniteLimits F)
    (_ : PreservesFiniteColimits F) (U V : C) (K L : DerivedCategory C)
    (ρ : U ⟶ V) (θ : (DerivedCategory.singleFunctor C 0).obj V ⟶ K) (e : L ≅ K),
    HEq F functor₀ ∧ HEq ρ restriction ∧ HEq θ theta ∧ HEq e power ∧
      HEq γ (localizedFlagForgetModel F ρ θ e)

/-- Fix the site comparison, actual restriction, nested class and power coordinates.
Source: Stacks 099R and blueprint Step 4 (blueprint: lem-pur-flag-localized-product). -/
def LocalizedFlagForgottenNormalization (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) (i : Fin (r + 1))
    {H₀ : Type (u + 1)} (γ : H₀) : Prop :=
  LocalizedFlagForgetCharacterization
    (C := Sheaf (P.localizedFlagBundle aS D i).E.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))
    (D := Sheaf (Scheme.ProEt.topology (P.localizedFlagBundle aS D i).E)
      (ModuleCat.{u + 1} P.Coefficient))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      (P.localizedFlagBundle aS D i).E)
    (P.localizedFlagRestriction (P.localizedFlagBundle aS D i).zeroSection)
    (P.localizedFlagTheta aS D i)
    (P.localizedFlagPowerComparison (P.localizedFlagBundle aS D i).E
      ((P.localizedFlagBundle aS D i).p ≫ aS) i.val) γ

/-- The normalized exact comparison has one realization in ordinary finite cohomology.
Source: Stacks 099R and blueprint Step 4 (blueprint: lem-pur-flag-localized-product).
Proof: take the published comparison inverse image and the displayed restriction,
nested class and power comparison in localizedFlagForgetModel. Its source is the
comparison image of the ordinary constant single object, hence projectiveBundleUnit;
its target is diagonalTwist by its definition. Transport along these identical
presentations. Eliminating the HEq equations fixes the functor and all three input
maps, and therefore their composite, proving uniqueness. No coefficient map is chosen. -/
theorem localizedFlagForgotten_realization (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) (i : Fin (r + 1)) :
    ∃! γ : ordinaryFiniteCohomology P (P.localizedFlagBundle aS D i).E i.val,
      P.LocalizedFlagForgottenNormalization aS D i γ := by
  sorry

/-- Forget support, change power coordinates and apply the canonical exact site comparison.
The unique normalization fixes every map of this composite.
Source: Stacks 099R and blueprint Step 4 (blueprint: lem-pur-flag-localized-product). -/
def localizedFlagForgotten (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    {r : ℕ} (D : LocalizedFlagFiltration S r) (i : Fin (r + 1)) :
    ordinaryFiniteCohomology P (P.localizedFlagBundle aS D i).E i.val :=
  localizedFlagUniqueWitness (P.localizedFlagForgotten_realization aS D i)

/-- Forgetting the nested supported Cartier composite gives the pullback of the
ordered product of the first i quotient Chern classes, for every i including zero.
The geometry conjunct records Cartier closedness, its associated quotient line,
smoothness, and the projection/zero-section identities for the actual total spaces.
Source: blueprint main-20261015, localized-top-Chern proof Steps 2 and 4;
Stacks Tags 01X0, 03PL and 0B56 (blueprint: lem-pur-flag-localized-product).

Proof, following the eight steps of the node:
1. Lift local generators of the line quotients to obtain simultaneous adapted frames.
The total spaces are Spec R[t_1,...,t_i], and the successive maps set t_i=0.
This is a nonzerodivisor over every R; its divisor line is pi_i*Q_i (Stacks 01X0).
2. These polynomial charts make each projection smooth. They also show separatedness,
finite type, closedness, and quasi-compactness of the open complements, over S and k.
3. Closed direct images are exact. Their composition comparison identifies the
restriction rho_i with a_i*(rho_(i-1)) after restriction to E_(i-1). Thus the
left side is exactly forgetting support in the recursively specified Theta_i.
4. For T=A(i-1)[2i-2], the projection map is the counit-normalized map P_T.
Its invertibility follows from the finite rank-one twist projection formula;
the shifted divisor arrow is (d_i tensor 1) P_T inverse, as in localizedFlagCompose.
5. Naturality and the unit normalization give P_T inverse a_i*(a_i*x) q_i=q_i tensor x.
This follows equally by taking adjuncts and using the adjunction triangle identity.
6. Induct on i, starting with E_0=S and the identity class. The projection equation
identifies a_i*(the forgotten preceding class) with the pullback of the preceding
root product, so the recursive composite becomes (d_i tensor 1)(q_i tensor x).
7. Bifunctoriality turns this into (d_i q_i) cup x. The normalized Cartier Kummer
map forgets to c_1(pi_i*Q_i), by lem-amb-cartier-kummer-map.
8. Kummer pullback identifies that class with pi_i*c_1(Q_i). Cup pullback and
associativity multiply by the preceding product. Even degree makes the commutation
sign +1, giving the ordered product Q_1,...,Q_i. The canonical site comparison
and positive Tate power identifications preserve all these maps and signs. -/
theorem localized_flag_product (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of P.field.k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (r : ℕ) (D : LocalizedFlagFiltration S r) :
    P.LocalizedFlagGeometry aS D ∧ ∀ i : Fin (r + 1),
      P.localizedFlagForgotten aS D i =
        P.ordinaryFiniteCohomologyPullback
          (Etale.projectiveLineTraceTransport P.diagonalExponent
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
            P.Coefficient P.diagonalExponent_annihilates)
          (P.localizedFlagBundle aS D i).p (P.diagonalExponent_isUnit aS) i.val
          (P.ordinaryFiniteFlagTopProduct S i.val (P.localizedFlagRoots aS D i)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
