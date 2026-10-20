/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TraceFormulaStrictWeilComplex
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Normalized adic Weil systems

Source: blueprint main-20261015,
`sec-trace-formula/sk-prop-trace-adic/def-trf-adic-system.md`, order 2729
(blueprint: def-trf-adic-system).

Levels are indexed by n : Nat with exponent n+1. The coefficient categories are the
recorded intrinsic constant-ring categories. Realization is a separate property of
an object over the completed coefficient sheaf. No coherent lift to D(Towers) is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u c c₁ v v₁ r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures


/-- The coefficient conventions at every positive exponent, retaining the fixed closure k.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicConventions (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    TraceFormulaCoefficientConventions.{u} :=
  { T with level := n + 1, level_pos := Nat.succ_le_succ (Nat.zero_le n) }

/-- The actual finite category at exponent n+1, with ambient derived morphisms.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicLevel (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :=
  proEtaleDerivedCategory T.geometricBaseChange (adicConventions T n).coefficientRing

/-- Restriction r_(m+1,n+1) along the recorded finite constant-sheaf quotient.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicRes (T : TraceFormulaCoefficientConventions.{u}) {m n : ℕ} (h : n ≤ m) :
    adicLevel T n ⥤ adicLevel T m :=
  normalizedDVRRes T.coefficients.l T.coefficientField T.geometricBaseChange h

/-- The canonical identity comparison, with the finite coefficient category explicit.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicResUnit (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    adicRes T (Nat.le_refl n) ≅ 𝟭 (adicLevel T n) :=
  normalizedDVRResUnit T.coefficients.l T.coefficientField T.geometricBaseChange n

/-- The canonical composition comparison, with its three indices explicit.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicResComp (T : TraceFormulaCoefficientConventions.{u})
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    adicRes T hmn ⋙ adicRes T hrm ≅ adicRes T (le_trans hmn hrm) :=
  normalizedDVRResComp T.coefficients.l T.coefficientField T.geometricBaseChange hrm hmn

/-- The ordinary finite coefficient modules at exponent n+1.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicModules (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :=
  normalizedDVRModules T.coefficients.l T.coefficientField T.geometricBaseChange n

/-- Exact inverse image along D.geometricGaloisFrobenius at exponent n+1.
This is the ordinary functor underlying the recorded strict-Weil pullback.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicModuleFrobenius (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    adicModules T n ⥤ adicModules T n :=
  letI : Finite (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1)) :=
    Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
    (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicPullback (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))
    (T.datum.geometricGaloisFrobenius T.X₀)

/-- Additivity of the recorded ordinary Frobenius inverse image.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
instance adicModuleFrobenius_additive (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    (adicModuleFrobenius T n).Additive :=
  letI := Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
    (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicPullback_additive
    (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))
    (T.datum.geometricGaloisFrobenius T.X₀)

/-- Finite-limit preservation of the recorded ordinary Frobenius inverse image.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
instance adicModuleFrobenius_limits (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    PreservesFiniteLimits (adicModuleFrobenius T n) :=
  letI := Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
    (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicPullback_preservesFiniteLimits
    (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))
    (T.datum.geometricGaloisFrobenius T.X₀)

/-- Finite-colimit preservation of the recorded ordinary Frobenius inverse image.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
instance adicModuleFrobenius_colimits (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    PreservesFiniteColimits (adicModuleFrobenius T n) :=
  letI := Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
    (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicPullback_preservesFiniteColimits
    (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))
    (T.datum.geometricGaloisFrobenius T.X₀)

/-- The corresponding ordinary direct image, with its canonical constant-scalar action.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicModuleFrobeniusPush (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    adicModules T n ⥤ adicModules T n :=
  proEtaleConstantModuleDirectImage (T.datum.geometricGaloisFrobenius T.X₀)
    (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))

/-- The normalized adjunction transported through the recorded intrinsic realization.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicModuleFrobeniusAdjunction (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    adicModuleFrobenius T n ⊣ adicModuleFrobeniusPush T n :=
  letI : Finite (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1)) :=
    Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
    (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicConstantModuleAdjunction (T.datum.geometricGaloisFrobenius T.X₀)
    (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))

/-- Ordinary coefficient restriction, before exact derived descent.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicModuleRes (T : TraceFormulaCoefficientConventions.{u}) {m n : ℕ} (h : n ≤ m) :
    adicModules T n ⥤ adicModules T m :=
  normalizedDVRModuleRes T.coefficients.l T.coefficientField T.geometricBaseChange h

/-- The scalar-change comparison for a commuting ring square is uniquely identity on
sections. Stating it before specializing coefficients avoids unfolding the coefficient
extension fields while checking equality of section types.
Source: blueprint order 2729, canonical coefficient identification
(blueprint: def-trf-adic-system).
Proof: both composites evaluate M on F(U), with R(U) acting through the two equal
ring maps of the square. Identity is therefore linear, natural and invertible.
Every section map of a comparison satisfying the displayed equation is identity,
so the comparison is unique. -/
theorem adicPushRestriction_existsUnique
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (F : C ⥤ C) [F.IsContinuous J J] {R S : Sheaf J RingCat.{r}}
    (ρ : R ⟶ S)
    (δR : R ⟶ (F.sheafPushforwardContinuous RingCat.{r} J J).obj R)
    (δS : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J J).obj S)
    (h : ρ ≫ δS = δR ≫ (F.sheafPushforwardContinuous RingCat.{r} J J).map ρ) :
    ∃! e : SheafOfModules.pushforward.{w} δS ⋙ SheafOfModules.restrictScalars ρ ≅
        SheafOfModules.restrictScalars ρ ⋙ SheafOfModules.pushforward δR,
      ∀ (M : SheafOfModules.{w} S) (U : Cᵒᵖ)
        (x : M.val.obj (F.op.obj U)), (e.hom.app M).val.app U x = x := by
  sorry

/-- The specified comparison, selected while its site and rings remain abstract.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicPushRestriction
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (F : C ⥤ C) [F.IsContinuous J J] {R S : Sheaf J RingCat.{r}}
    (ρ : R ⟶ S)
    (δR : R ⟶ (F.sheafPushforwardContinuous RingCat.{r} J J).obj R)
    (δS : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J J).obj S)
    (h : ρ ≫ δS = δR ≫ (F.sheafPushforwardContinuous RingCat.{r} J J).map ρ) :
    SheafOfModules.pushforward.{w} δS ⋙ SheafOfModules.restrictScalars ρ ≅
      SheafOfModules.restrictScalars ρ ⋙ SheafOfModules.pushforward δR :=
  (adicPushRestriction_existsUnique F ρ δR δS h).choose

/-- The constant-scalar unit for Frobenius, forgetting commutativity.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicFrobeniusRingMap (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    integralCoefficientSheaf T.coefficients.l T.coefficientField T.geometricBaseChange n ⟶
      ((proEtaleBaseChange (T.datum.geometricGaloisFrobenius T.X₀)).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology T.geometricBaseChange)
        (ProEt.topology T.geometricBaseChange)).obj
          (integralCoefficientSheaf T.coefficients.l T.coefficientField
            T.geometricBaseChange n) :=
  ⟨Functor.whiskerRight (proEtaleCoefficientDirectImageMap
    (T.datum.geometricGaloisFrobenius T.X₀)
    (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Naturality of the constant-scalar unit with respect to the actual finite quotient.
Source: blueprint order 2729 (blueprint: def-trf-adic-system).
Proof: the constant-sheaf adjunction unit is natural in its coefficient ring. Apply
this naturality to each adjacent reduction, and compose along the quotient sequence;
identity quotients use the unit identity. Forget commutativity to get this equation. -/
theorem adicFrobeniusRingMap_square
    (T : TraceFormulaCoefficientConventions.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRQuotient T.coefficients.l T.coefficientField T.geometricBaseChange h ≫
        adicFrobeniusRingMap T n =
      adicFrobeniusRingMap T m ≫
        ((proEtaleBaseChange (T.datum.geometricGaloisFrobenius T.X₀)).sheafPushforwardContinuous
          RingCat.{u + 1} (ProEt.topology T.geometricBaseChange)
          (ProEt.topology T.geometricBaseChange)).map
            (normalizedDVRQuotient T.coefficients.l T.coefficientField
              T.geometricBaseChange h) := by
  sorry

/-- The canonical comparison is identity on sections, determined by the general
commuting ring square above.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicRestrictionFrobeniusPush (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) :
    adicModuleFrobeniusPush T n ⋙ adicModuleRes T h ≅
      adicModuleRes T h ⋙ adicModuleFrobeniusPush T m :=
  adicPushRestriction
    (proEtaleBaseChange (T.datum.geometricGaloisFrobenius T.X₀))
    (normalizedDVRQuotient T.coefficients.l T.coefficientField T.geometricBaseChange h)
    (adicFrobeniusRingMap T m) (adicFrobeniusRingMap T n)
    (adicFrobeniusRingMap_square T h)

/-- The coefficient comparison mate, with abstract module categories kept explicit.
This is the existing mates correspondence applied to the scalar restriction square;
abstracting its endpoints avoids repeatedly expanding the coefficient field model.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicCoefficientRestrictionMate
    {C : Type c} {D : Type c₁} [Category.{v} C] [Category.{v₁} D]
    {F₁ G₁ : C ⥤ C} {F₂ G₂ : D ⥤ D}
    (a : F₁ ⊣ G₁) (b : F₂ ⊣ G₂) (R : C ⥤ D)
    (e : G₁ ⋙ R ≅ R ⋙ G₂) : R ⋙ F₂ ⟶ F₁ ⋙ R :=
  ((mateEquiv (G := R) (H := R) a b).symm
    (TwoSquare.mk _ _ _ _ e.hom)).natTrans

/-- The inverse-image comparison is the mate of the specified identity on sections.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicRestrictionFrobeniusMate (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) :
    adicModuleRes T h ⋙ adicModuleFrobenius T m ⟶
      adicModuleFrobenius T n ⋙ adicModuleRes T h :=
  adicCoefficientRestrictionMate (adicModuleFrobeniusAdjunction T n)
    (adicModuleFrobeniusAdjunction T m) (adicModuleRes T h)
      (adicRestrictionFrobeniusPush T h)


/-- The prescribed mate is an isomorphism; no coefficient flatness is needed.
Source: blueprint order 2729, coefficient identification
(blueprint: def-trf-adic-system).
Proof: the normalized intrinsic inverse-image adjunction is the ordinary inverse
image of the underlying abelian sheaf with its transported constant scalar action.
The mate above is identity on that inverse image: its unit/counit expression evaluates
the sectionwise identity comparison. Both scalar actions agree on constant sections
and hence after sheafification. This gives a linear inverse, naturally in the module. -/
theorem adicRestrictionFrobeniusMate_isIso
    (T : TraceFormulaCoefficientConventions.{u}) {m n : ℕ} (h : n ≤ m) :
    IsIso (adicRestrictionFrobeniusMate T h) := by
  sorry

/-- The specified invertible ordinary mate, with its inverse supplied by IsIso.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicRestrictionFrobeniusOrdinary (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) :
    adicModuleRes T h ⋙ adicModuleFrobenius T m ≅
      adicModuleFrobenius T n ⋙ adicModuleRes T h :=
  @asIso _ _ _ _ (adicRestrictionFrobeniusMate T h)
    (adicRestrictionFrobeniusMate_isIso T h)

/-- Exact descent of a specified coefficient comparison, with abstract categories.
This composes the recorded canonical exact-descent comparison isomorphisms.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicExactDerivedComparison
    {A : Type c} [Category.{v} A] [Abelian A] [HasDerivedCategory.{r} A]
    {B : Type c₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w} B]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (F : B ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : A ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : R ⋙ F ≅ G ⋙ R) :
    R.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  letI : PreservesFiniteLimits (R ⋙ F) := comp_preservesFiniteLimits R F
  letI : PreservesFiniteColimits (R ⋙ F) := comp_preservesFiniteColimits R F
  letI : PreservesFiniteLimits (G ⋙ R) := comp_preservesFiniteLimits G R
  letI : PreservesFiniteColimits (G ⋙ R) := comp_preservesFiniteColimits G R
  (Functor.mapDerivedCategoryCompIso R F).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso G R

/-- Exact termwise descent of the ordinary Frobenius inverse image, at explicit endpoints.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicDerivedFrobenius (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    adicLevel T n ⥤ adicLevel T n :=
  letI := HasDerivedCategory.standard (adicModules T n)
  (adicModuleFrobenius T n).mapDerivedCategory

/-- The recorded strict-Weil pullback is this same exact termwise descent.
Source: blueprint order 2729 (blueprint: def-trf-adic-system).
Proof: unfold strictWeilFrobeniusPullback, derivedPullback and finiteDerivedPullback.
The positive-level rewrite identifies (n+1)-1 with n. Both sides then descend the
same sfIntrinsicPullback along the same standard derived localization. The finite-ring
instance proofs agree by proof irrelevance, so the two functors are equal. -/
theorem adicDerivedFrobenius_eq (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    adicDerivedFrobenius T n = (adicConventions T n).strictWeilFrobeniusPullback := by
  sorry

/-- Exact descent of the specified ordinary coefficient mate, before identifying the
recorded strict-Weil pullback. Source: blueprint order 2729
(blueprint: def-trf-adic-system). -/
def adicRestrictionFrobeniusExact (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) :
    adicRes T h ⋙ adicDerivedFrobenius T m ≅
      adicDerivedFrobenius T n ⋙ adicRes T h :=
  letI := HasDerivedCategory.standard (adicModules T m)
  letI := HasDerivedCategory.standard (adicModules T n)
  adicExactDerivedComparison (A := adicModules T n) (B := adicModules T m)
    (adicModuleRes T h) (adicModuleFrobenius T m) (adicModuleFrobenius T n)
    (adicRestrictionFrobeniusOrdinary T h)

/-- The canonical derived coefficient identification used in the transition square.
It is exact termwise descent of the normalized ordinary mate, transported through
the equality with the recorded strict-Weil pullback.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicRestrictionFrobenius (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) :
    adicRes T h ⋙ (adicConventions T m).strictWeilFrobeniusPullback ≅
      (adicConventions T n).strictWeilFrobeniusPullback ⋙ adicRes T h :=
  Functor.isoWhiskerLeft (adicRes T h) (eqToIso (adicDerivedFrobenius_eq T m)).symm ≪≫
    adicRestrictionFrobeniusExact T h ≪≫
      Functor.isoWhiskerRight (eqToIso (adicDerivedFrobenius_eq T n)) (adicRes T h)

/-- The same actual quotient map, retaining commutativity for derived change of rings.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicQuotientComm (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) :
    integralCoefficientCommRingSheaf.{u, u} T.coefficients.l T.coefficientField
        T.geometricBaseChange m ⟶
      integralCoefficientCommRingSheaf.{u, u} T.coefficients.l T.coefficientField
        T.geometricBaseChange n where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom
        ((normalizedDVRQuotient T.coefficients.l T.coefficientField
          T.geometricBaseChange h).hom.app U).hom
      naturality := fun _ _ f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
        ((normalizedDVRQuotient T.coefficients.l T.coefficientField
          T.geometricBaseChange h).hom.naturality f) }

/-- A presentation of the recorded universal derived extension along the finite quotient.
The theorem fixes the ordinary tensor on both objects and maps, and its universal
counit fixes the derived pair up to its unique compatible isomorphism. This is not
a choice of an arbitrary functor with the right source and target.
Source: blueprint order 2729; Stacks 06YY (blueprint: def-trf-adic-system). -/
def adicDerivedChangeModel (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) :
    @SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      T.geometricBaseChange.ProEt inferInstance (essentiallySmallSelf.{0} _) _
      inferInstance inferInstance inferInstance _ _ (adicQuotientComm T h)
      (HasDerivedCategory.standard (adicModules T m))
      (HasDerivedCategory.standard (adicModules T n)) :=
  letI : EssentiallySmall.{u + 1} T.geometricBaseChange.ProEt := essentiallySmallSelf.{0} _
  letI := HasDerivedCategory.standard (adicModules T m)
  letI := HasDerivedCategory.standard (adicModules T n)
  Classical.choice
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (adicQuotientComm T h))

/-- The recorded derived extension with its finite-level endpoints made explicit.
This is exactly the functor of adicDerivedChangeModel, without a new choice.
Source: blueprint order 2729; Stacks 06YY (blueprint: def-trf-adic-system). -/
def adicDerivedExtension (T : TraceFormulaCoefficientConventions.{u})
    {m n : ℕ} (h : n ≤ m) : adicLevel T m ⥤ adicLevel T n :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.T.{u + 1, u, u + 1, u + 2, u + 2}
    T.geometricBaseChange.ProEt inferInstance (essentiallySmallSelf.{0} _) _
    inferInstance inferInstance inferInstance _ _ (adicQuotientComm T h)
    (HasDerivedCategory.standard (adicModules T m))
    (HasDerivedCategory.standard (adicModules T n)) (adicDerivedChangeModel T h)

section SystemMaps

variable {C : ℕ → Type c} [∀ n : ℕ, Category.{v} (C n)]
  {B : ℕ → Type c₁} [∀ n : ℕ, Category.{v₁} (B n)]
  (F : ∀ n : ℕ, B n ⥤ C n)
  (res : ∀ {m n : ℕ}, n ≤ m → C n ⥤ C m)

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A family of level morphisms whose underlying arrows commute with transitions.
The functor F is identity for A-systems and the recorded forgetful functor for Weil systems.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
structure TraceFormulaSystemMap
    (K L : ∀ n : ℕ, B n)
    (tK : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (K m) ⟶ (res h).obj ((F n).obj (K n)))
    (tL : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (L m) ⟶ (res h).obj ((F n).obj (L n))) where
  f : ∀ n : ℕ, K n ⟶ L n
  comm : ∀ {m n : ℕ} (h : n ≤ m),
    tK h ≫ (res h).map ((F n).map (f n)) = (F m).map (f m) ≫ tL h

variable {F res}

/-- Identities preserve each transition.
Source: blueprint order 2729 (blueprint: def-trf-adic-system).
Proof: both functors preserve identities, and the two composites reduce to tK. -/
theorem TraceFormulaSystemMap.id_comm (K : ∀ n : ℕ, B n)
    (tK : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (K m) ⟶ (res h).obj ((F n).obj (K n)))
    {m n : ℕ} (h : n ≤ m) :
    tK h ≫ (res h).map ((F n).map (𝟙 (K n))) = (F m).map (𝟙 (K m)) ≫ tK h := by
  sorry

/-- The identity family, with its transition square.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def TraceFormulaSystemMap.id (K : ∀ n : ℕ, B n)
    (tK : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (K m) ⟶ (res h).obj ((F n).obj (K n))) :
    TraceFormulaSystemMap F res K K tK tK :=
  ⟨fun n ↦ 𝟙 (K n), TraceFormulaSystemMap.id_comm K tK⟩

variable {K L M N : ∀ n : ℕ, B n}
  {tK : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (K m) ⟶ (res h).obj ((F n).obj (K n))}
  {tL : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (L m) ⟶ (res h).obj ((F n).obj (L n))}
  {tM : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (M m) ⟶ (res h).obj ((F n).obj (M n))}
  {tN : ∀ {m n : ℕ} (h : n ≤ m), (F m).obj (N m) ⟶ (res h).obj ((F n).obj (N n))}

/-- Levelwise composition preserves the transition square.
Source: blueprint order 2729 (blueprint: def-trf-adic-system).
Proof: expand both functors on composition, use the squares for f and g successively,
and reassociate. This gives the required square at every pair of indices. -/
theorem TraceFormulaSystemMap.comp_comm
    (f : TraceFormulaSystemMap F res K L tK tL)
    (g : TraceFormulaSystemMap F res L M tL tM) {m n : ℕ} (h : n ≤ m) :
    tK h ≫ (res h).map ((F n).map (f.f n ≫ g.f n)) =
      (F m).map (f.f m ≫ g.f m) ≫ tM h := by
  sorry

/-- Levelwise composition, with its transition square.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def TraceFormulaSystemMap.comp
    (f : TraceFormulaSystemMap F res K L tK tL)
    (g : TraceFormulaSystemMap F res L M tL tM) : TraceFormulaSystemMap F res K M tK tM :=
  ⟨fun n ↦ f.f n ≫ g.f n, TraceFormulaSystemMap.comp_comm f g⟩

/-- Left identity for the levelwise morphisms.
Source: blueprint order 2729 (blueprint: def-trf-adic-system).
Proof: extensionality of the f fields reduces to the level category identity law;
the comm fields are propositions, so proof irrelevance identifies them. -/
theorem TraceFormulaSystemMap.id_comp (f : TraceFormulaSystemMap F res K L tK tL) :
    (TraceFormulaSystemMap.id K tK).comp f = f := by
  sorry

/-- Right identity for the levelwise morphisms.
Source: blueprint order 2729 (blueprint: def-trf-adic-system).
Proof: extensionality of the f fields reduces to the level category identity law;
the comm fields are propositions, so proof irrelevance identifies them. -/
theorem TraceFormulaSystemMap.comp_id (f : TraceFormulaSystemMap F res K L tK tL) :
    f.comp (TraceFormulaSystemMap.id L tL) = f := by
  sorry

/-- Associativity for the levelwise morphisms.
Source: blueprint order 2729 (blueprint: def-trf-adic-system).
Proof: extensionality of the f fields reduces to associativity at each level;
the comm fields are propositions, so proof irrelevance identifies them. -/
theorem TraceFormulaSystemMap.assoc
    (f : TraceFormulaSystemMap F res K L tK tL)
    (g : TraceFormulaSystemMap F res L M tL tM)
    (h : TraceFormulaSystemMap F res M N tM tN) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  sorry

end SystemMaps

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Presentation of the system fields with abstract level categories. Specialization
below uses the recorded ctf and strict-Weil carriers, with the actual scalar restrictions.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
structure TraceFormulaSystemData
    (C : ℕ → Type c) [∀ n : ℕ, Category.{v} (C n)]
    (B : ℕ → Type c₁) (carrier : ∀ n : ℕ, B n → C n)
    (res : ∀ {m n : ℕ}, n ≤ m → C n ⥤ C m)
    (unit : ∀ n : ℕ, res (Nat.le_refl n) ≅ 𝟭 (C n))
    (comp : ∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      res hmn ⋙ res hrm ≅ res (le_trans hmn hrm)) where
  K : ∀ n : ℕ, B n
  t : ∀ {m n : ℕ} (h : n ≤ m), carrier m (K m) ⟶ (res h).obj (carrier n (K n))
  t_refl : ∀ n : ℕ, t (Nat.le_refl n) ≫ (unit n).hom.app (carrier n (K n)) =
    𝟙 (carrier n (K n))
  t_comp : ∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
    t (le_trans hmn hrm) ≫ (comp hrm hmn).inv.app (carrier n (K n)) =
      t hrm ≫ (res hrm).map (t hmn)

/-- An A-system with all composite transitions. The identity and cocycle say that
these are precisely the composites of the adjacent arrows, without extra choices.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaASystem (T : TraceFormulaCoefficientConventions.{u}) :=
  TraceFormulaSystemData (adicLevel T)
    (fun n ↦ (adicConventions T n).boundedConstructibleFiniteTor.FullSubcategory)
    (fun _ K ↦ K.obj) (fun h ↦ adicRes T h)
    (adicResUnit T) (fun hrm hmn ↦ adicResComp T hrm hmn)

/-- Normalization of the specified transitions. Under the recorded derived
extension/restriction adjunction, this Hom map is precomposition with the adjoint
nu_(m,n); bijectivity for every P is exactly invertibility of nu by Yoneda. Thus the
map tested is induced by t, rather than an unrelated isomorphism of tensor objects.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def TraceFormulaASystem.IsNormalized {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaASystem T) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (P : adicLevel T n),
    Function.Bijective (fun f : (S.K n).obj ⟶ P ↦ S.t h ≫ (adicRes T h).map f)

/-- The transition's adjoint under a supplied presentation of the derived adjunction.
Its extension functor is the recorded universal K-flat derived change of rings above;
the input is the actual t, so no unrelated normalization arrow is introduced.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def TraceFormulaASystem.adjointTransition {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaASystem T) {m n : ℕ} (h : n ≤ m)
    (a : adicDerivedExtension T h ⊣ adicRes T h) :
    (adicDerivedExtension T h).obj (S.K m).obj ⟶ (S.K n).obj :=
  (a.homEquiv _ _).symm (S.t h)

/-- Morphisms of A-systems are levelwise derived arrows commuting with transitions.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaASystem.Hom {T : TraceFormulaCoefficientConventions.{u}}
    (S S' : TraceFormulaASystem T) :=
  TraceFormulaSystemMap (fun n ↦ 𝟭 (adicLevel T n)) (fun h ↦ adicRes T h)
    (fun n ↦ (S.K n).obj) (fun n ↦ (S'.K n).obj) S.t S'.t

/-- The identity A-system morphism is identity at each level.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaASystem.Hom.id {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaASystem T) : S.Hom S :=
  TraceFormulaSystemMap.id _ _

/-- Composition of A-system morphisms is levelwise derived composition.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaASystem.Hom.comp {T : TraceFormulaCoefficientConventions.{u}}
    {S S' S'' : TraceFormulaASystem T} (f : S.Hom S') (g : S'.Hom S'') : S.Hom S'' :=
  TraceFormulaSystemMap.comp f g

/-- The composite of the recorded strict-Weil forgetful functor with the full inclusion.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def adicWeilForget (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    (adicConventions T n).strictWeilComplex ⥤ adicLevel T n :=
  (adicConventions T n).strictWeilForget ⋙
    (adicConventions T n).boundedConstructibleFiniteTor.ι

/-- Forget a recorded strict Weil complex to its ambient derived object.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicWeilCarrier (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ)
    (K : (adicConventions T n).strictWeilComplex) : adicLevel T n :=
  ((adicConventions T n).strictWeilForget.obj K).obj

/-- The actual strict structure isomorphism, using D.geometricGaloisFrobenius.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicWeilPhi (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ)
    (K : (adicConventions T n).strictWeilComplex) :=
  (adicConventions T n).strictWeilFrobenius K

/-- Ambient arrow of a recorded strict Weil morphism; its Frobenius square is built in.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicWeilMap (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ)
    {K L : (adicConventions T n).strictWeilComplex} (f : K ⟶ L) :
    adicWeilCarrier T n K ⟶ adicWeilCarrier T n L :=
  ((adicConventions T n).strictWeilForget.map f).hom

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The normalized Weil-system fields over abstract level categories. Specialization
below supplies the recorded strict-Weil carriers, pullbacks and coefficient comparisons.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
structure TraceFormulaWeilSystemData
    (C : ℕ → Type c) [∀ n : ℕ, Category.{v} (C n)]
    (B : ℕ → Type c₁) (carrier : ∀ n : ℕ, B n → C n)
    (res : ∀ {m n : ℕ}, n ≤ m → C n ⥤ C m)
    (unit : ∀ n : ℕ, res (Nat.le_refl n) ≅ 𝟭 (C n))
    (comp : ∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      res hmn ⋙ res hrm ≅ res (le_trans hmn hrm))
    (F : ∀ n : ℕ, C n ⥤ C n)
    (phi : ∀ (n : ℕ) (K : B n), (F n).obj (carrier n K) ≅ carrier n K)
    (e : ∀ {m n : ℕ} (h : n ≤ m), res h ⋙ F m ≅ F n ⋙ res h) extends
      TraceFormulaSystemData C B carrier res unit comp where
  normalized : ∀ {m n : ℕ} (h : n ≤ m) (P : C n),
    Function.Bijective (fun f : carrier n (K n) ⟶ P ↦ t h ≫ (res h).map f)
  weil_comm : ∀ n : ℕ,
    (phi (n + 1) (K (n + 1))).hom ≫ t (Nat.le_succ n) =
      (F (n + 1)).map (t (Nat.le_succ n)) ≫
        (e (Nat.le_succ n)).hom.app (carrier n (K n)) ≫
          (res (Nat.le_succ n)).map (phi n (K n)).hom

/-- A normalized A-system with a recorded strict Weil complex at every positive level.
The transition square uses the canonical exact coefficient comparison constructed above.
Realization is a separate predicate and is not an object or existence field here.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaAdicSystem (T : TraceFormulaCoefficientConventions.{u}) :=
  TraceFormulaWeilSystemData (adicLevel T)
    (fun n ↦ (adicConventions T n).strictWeilComplex) (adicWeilCarrier T)
    (fun h ↦ adicRes T h)
    (adicResUnit T) (fun hrm hmn ↦ adicResComp T hrm hmn)
    (fun n ↦ (adicConventions T n).strictWeilFrobeniusPullback)
    (adicWeilPhi T) (fun h ↦ adicRestrictionFrobenius T h)

/-- Forget strict Weil structures, retaining the specified finite transitions.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def TraceFormulaAdicSystem.toASystem {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaAdicSystem T) : TraceFormulaASystem T where
  K n := (adicConventions T n).strictWeilForget.obj (S.K n)
  t := S.t
  t_refl := S.t_refl
  t_comp := S.t_comp

/-- A morphism is a levelwise strict Weil morphism commuting with the transitions.
Its strict-Weil Hom condition is exactly f_n phi_n = phi'_n (Lg* f_n).
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaAdicSystem.Hom {T : TraceFormulaCoefficientConventions.{u}}
    (S S' : TraceFormulaAdicSystem T) :=
  TraceFormulaSystemMap (adicWeilForget T) (fun h ↦ adicRes T h) S.K S'.K S.t S'.t

/-- The identity is the family of identities in the recorded strict Weil categories.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaAdicSystem.Hom.id {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaAdicSystem T) : S.Hom S :=
  TraceFormulaSystemMap.id _ _

/-- Composition is levelwise composition in the recorded strict Weil categories.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev TraceFormulaAdicSystem.Hom.comp {T : TraceFormulaCoefficientConventions.{u}}
    {S S' S'' : TraceFormulaAdicSystem T} (f : S.Hom S') (g : S'.Hom S'') : S.Hom S'' :=
  TraceFormulaSystemMap.comp f g

/-- D^b_ctf,W,adic, with exactly the specified levelwise Hom, identities and composition.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
instance traceFormulaAdicSystemCategory (T : TraceFormulaCoefficientConventions.{u}) :
    Category (TraceFormulaAdicSystem T) where
  Hom := TraceFormulaAdicSystem.Hom
  id := TraceFormulaAdicSystem.Hom.id
  comp := TraceFormulaAdicSystem.Hom.comp
  id_comp := fun f ↦ TraceFormulaSystemMap.id_comp f
  comp_id := fun f ↦ TraceFormulaSystemMap.comp_id f
  assoc := fun f g h ↦ TraceFormulaSystemMap.assoc f g h

/-- The common completed-coefficient target; it is not the discrete constant ring sheaf.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicCompletedCategory (T : TraceFormulaCoefficientConventions.{u}) :=
  completedIntegralDerivedCategory T.coefficients.l T.coefficientField T.geometricBaseChange
    T.datum T.coefficients.different

/-- Res_(n+1,X) is exact termwise restriction along the limit projection pi_(n+1).
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
abbrev adicCompletedRes (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    adicLevel T n ⥤ adicCompletedCategory T :=
  normalizedDVRResCompleted T.coefficients.l T.coefficientField T.geometricBaseChange
    T.datum T.coefficients.different n

/-- The restricted objects M_n, over the single completed coefficient sheaf.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def TraceFormulaASystem.restrictedObjects {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaASystem T) (n : ℕ) : adicCompletedCategory T :=
  (adicCompletedRes T n).obj (S.K n).obj

/-- The restricted adjacent transition, using the actual projection identity pi_m r=pi_n.
Source: blueprint order 2729 (blueprint: def-trf-adic-system). -/
def TraceFormulaASystem.restrictedStep {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaASystem T) (n : ℕ) :
    S.restrictedObjects (n + 1) ⟶ S.restrictedObjects n :=
  (adicCompletedRes T (n + 1)).map (S.t (Nat.le_succ n)) ≫
    (normalizedDVRResCompletedComp T.coefficients.l T.coefficientField
      T.geometricBaseChange T.datum T.coefficients.different (Nat.le_succ n)).hom.app
        (S.K n).obj

/-- Countable products exist in this completed-coefficient derived category.
Source: blueprint order 2729, product-existence clause
(blueprint: def-trf-adic-system).
Proof: apply lem-weil-proetale-countable-products-exact to the completed commutative
ring sheaf, whose underlying ring sheaf is the recorded completion. Its epimorphism
clause and sectionwise kernels give CountableAB4Star. Then apply
lem-weil-derived-limit-products-core with the standard derived localization. -/
theorem adicCompletedCountableProducts (T : TraceFormulaCoefficientConventions.{u}) :
    HasCountableProducts (adicCompletedCategory T) := by
  sorry

attribute [instance] adicCompletedCountableProducts

/-- Integral realization is the separate Roos-triangle property of L. In particular
there is no choice of a realization functor or an existence requirement on the system.
IsDerivedLimit uses the transition endomorphism 1-s with pr_n s=t_n pr_(n+1).
Source: blueprint order 2729; Stacks Tag 08TC (blueprint: def-trf-adic-system). -/
def TraceFormulaASystem.IsIntegralRealization {T : TraceFormulaCoefficientConventions.{u}}
    (S : TraceFormulaASystem T) (L : adicCompletedCategory T) : Prop :=
  IsDerivedLimit S.restrictedStep L

end WeilConjectures
