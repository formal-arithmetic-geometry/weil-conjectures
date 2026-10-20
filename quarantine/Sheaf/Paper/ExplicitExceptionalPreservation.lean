/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction
public import Sheaf.Paper.ConstructibleIntervalsUnordered
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteCoefficientReductionFlatModel
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.FiniteTensorConstructibleCohomology
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Explicit preservation for open and finite etale exceptional inverse images

Source: Weil blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
order 2063 (blueprint: thm-exc-explicit-preservation).

We use the inverse-image identifications of the ambient exceptional right adjoints.
The coefficient comparison is specified as the mate of the canonical restriction/direct
image comparison, with scalar-extension adjunctions normalized on K-flat representatives.
The index n denotes exponent n+1, so every positive coefficient level occurs.

## Main definitions

- `explicitReductionModuleAdjunction`: tensor-unit normalized scalar adjunction.
- `explicitReductionAdjunction`: its K-flat normalized derived adjunction.
- `explicitExceptionalCoefficientComparison`: the canonical coefficient mate.

## Main statements

- `explicitExceptional_preservation`: all interval and coefficient-preservation clauses.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v₁ v₂ w₁ w₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical constant-ring identification, obtained from the existing constant-ring
comparison, with its original constant-section normalization.
Source: Stacks 0H7J; blueprint order 2063 (blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitCoefficientIso {V X : Scheme.{u}} (f : V ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A) ≅
      proEtaleConstantRing V A :=
  letI : Finite (ULift.{u + 1} A) := Equiv.finite_iff Equiv.ulift |>.mpr inferInstance
  letI : TopologicalSpace (ULift.{u + 1} A) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} A) := ⟨rfl⟩
  @asIso _ _ _ _ (proEtaleCoefficientInverseImageMap f A)
    (ProEtale.finiteCoefficientCommRingMap_isIso f (ULift.{u + 1} A))

/-- Exact inverse image on the ordinary unbounded derived categories, representing
Rf^times under the open/finite-etale adjunction identifications of the statement.
Source: blueprint order 2063, paragraph 1 (blueprint: thm-exc-explicit-preservation). -/
noncomputable abbrev explicitExceptionalPullback {V X : Scheme.{u}} (f : V ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory V A :=
  proEtaleRingDerivedPullback f (proEtaleConstantRing X A) (proEtaleConstantRing V A)
    (explicitCoefficientIso f A)

/-- The corresponding ordinary derived direct image with the same canonical ring map.
Source: Stacks 07A6; blueprint order 2063 (blueprint: thm-exc-explicit-preservation). -/
noncomputable abbrev explicitExceptionalDirectImage {V X : Scheme.{u}} (f : V ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory V A ⥤ proEtaleDerivedCategory X A :=
  proEtaleRingDerivedDirectImage f (proEtaleConstantRing X A) (proEtaleConstantRing V A)
    (explicitCoefficientIso f A)

/-- The canonical pullback/direct-image adjunction, retaining the tensor-unit normalization.
Source: Stacks 07A6; blueprint order 2063 (blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitExceptionalPullbackAdjunction {V X : Scheme.{u}} (f : V ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    explicitExceptionalPullback f A ⊣ explicitExceptionalDirectImage f A :=
  proEtaleRingDerivedAdjunction f (proEtaleConstantRing X A) (proEtaleConstantRing V A)
    (explicitCoefficientIso f A)

set_option linter.defProp false in
/-- Sectionwise tensor-unit normalization, stated with arbitrary ring sheaves so that
specialization does not unfold a coefficient ring or a chosen derived-functor witness.
Source: Stacks 03EK; blueprint order 2063 (blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitScalarUnitNormalized {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (F : proEtaleRingModules T R ⥤ proEtaleRingModules T S)
    (h : ∀ M : proEtaleRingModules T R, F.obj M = SheafOfModules.changeOfRings φ M)
    (adj : F ⊣ proEtaleRingRestrictScalars φ) : Prop :=
  ∀ (M : proEtaleRingModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
    (adj.unit.app M).val.app U x =
      (eqToHom (h M).symm).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u + 1}
          (𝟙 ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U
            ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
              (φ.hom.app U).hom).unit.app (M.val.obj U) x))

set_option linter.defProp false in
/-- The derived unit is fixed on every complex representative by the ordinary
unit and universal derived counit. This categorical formula keeps localization sizes
independent of the site used in its specialization.
Source: Stacks 06YY and 07A6 (blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitDerivedUnitNormalized
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (a : F ⊣ G)
    (b : LF ⊣ G.mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex C ℤ,
    b.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) ≫
      G.mapDerivedCategory.map
        (ε.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) =
    DerivedCategory.Qh.map
      ((a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u})

/-- Exact restriction along the specified quotient. Source: Stacks 03DA
(blueprint: thm-exc-explicit-preservation). -/
noncomputable abbrev explicitReductionRestriction :=
  proEtaleRingRestrictScalars
    (flatModelReductionRingMap l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)

/-- Tensor/restriction adjunction with its tensor-generator normalization.
Source: Stacks 03EK and 06YY (blueprint: thm-exc-explicit-preservation).
Proof: transpose v by x ↦ v(1 tensor x), and transpose w by b tensor x ↦ b w(x).
Balancing gives linear maps; restriction compatibility descends them through sheafification.
Their composites are identities on generators. The unit is therefore 1 tensor x, and
that formula determines the adjunction uniquely. This is the ordinary calculation in step 4. -/
theorem explicitReductionModuleAdjunction_existsUnique :
    ∃! adj : flatModelReductionChange l E (m + 1) (n + 1)
        (Nat.add_le_add_right hmn 1) T ⊣ explicitReductionRestriction l E m n hmn T,
      explicitScalarUnitNormalized.{u}
        (flatModelReductionRingMap l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)
        (flatModelReductionChange l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)
        (flatModelReductionData l E (m + 1) (n + 1)
          (Nat.add_le_add_right hmn 1) T).choose_spec.choose adj := by
  sorry

/-- The uniquely tensor-unit normalized ordinary adjunction. Source: Stacks 03EK
(blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitReductionModuleAdjunction :=
  (explicitReductionModuleAdjunction_existsUnique l E m n hmn T).choose

/-- Restriction is additive by the scalar adjunction. Source: Stacks 03DA
(blueprint: thm-exc-explicit-preservation). -/
noncomputable instance explicitReductionRestrictionAdditive :
    (explicitReductionRestriction l E m n hmn T).Additive :=
  (explicitReductionModuleAdjunction l E m n hmn T).right_adjoint_additive

/-- The universal K-flat computation map of derived change of rings. Source: Stacks 06YY
(blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitReductionCounit :
    DerivedCategory.Qh.{u + 2, u + 1, u + 2} ⋙
        flatModelReduction l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T ⟶
      (flatModelReductionChange l E (m + 1) (n + 1)
        (Nat.add_le_add_right hmn 1) T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh.{u + 2, u + 1, u + 2} :=
  (flatModelReductionDerivedData l E (m + 1) (n + 1)
    (Nat.add_le_add_right hmn 1) T).choose_spec.choose

/-- Restriction preserves finite limits. Source: Stacks 03DA
(blueprint: thm-exc-explicit-preservation). -/
noncomputable instance explicitReductionRestrictionLimits :
    PreservesFiniteLimits (explicitReductionRestriction l E m n hmn T) :=
  (proEtaleRingRestrictScalars_properties
    (flatModelReductionRingMap l E (m + 1) (n + 1)
      (Nat.add_le_add_right hmn 1) T)).1

/-- Restriction preserves finite colimits. Source: Stacks 03DA
(blueprint: thm-exc-explicit-preservation). -/
noncomputable instance explicitReductionRestrictionColimits :
    PreservesFiniteColimits (explicitReductionRestriction l E m n hmn T) :=
  (proEtaleRingRestrictScalars_properties
    (flatModelReductionRingMap l E (m + 1) (n + 1)
      (Nat.add_le_add_right hmn 1) T)).2.1

/-- Derived scalar adjunction uniquely normalized on every complex representative.
Source: Stacks 06YY and 07A6 (blueprint: thm-exc-explicit-preservation).
Proof: derive the tensor-unit normalized ordinary adjunction. Exact restriction is
termwise on derived categories. The universal left-derived tensor has invertible
counit on K-flat complexes, so transporting the ordinary unit through this counit
and the exact factorization gives the displayed equation. Every object has a K-flat
resolution; naturality extends the equation to every complex representative and
determines the unit everywhere, proving uniqueness. -/
theorem explicitReductionAdjunction_existsUnique :
    ∃! adj : flatModelReduction l E (m + 1) (n + 1)
        (Nat.add_le_add_right hmn 1) T ⊣
      (explicitReductionRestriction l E m n hmn T).mapDerivedCategory.{u + 2, u + 2,
        u + 1, u + 1, u + 2, u + 2},
      explicitDerivedUnitNormalized.{u + 1, u + 1, u + 2, u + 2, u + 2, u + 2}
        (C := proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (n + 1))))
        (D := proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (m + 1))))
        (flatModelReductionChange l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)
        (explicitReductionRestriction l E m n hmn T)
        (flatModelReduction l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)
        (explicitReductionCounit l E m n hmn T)
        (explicitReductionModuleAdjunction l E m n hmn T)
        adj := by
  sorry

/-- The uniquely K-flat normalized derived adjunction. Source: Stacks 06YY
(blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitReductionAdjunction :=
  (explicitReductionAdjunction_existsUnique l E m n hmn T).choose

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n)
  {V X : Scheme.{u}} (f : V ⟶ X)

/-- The canonical restriction/direct-image comparison, identity on sections and
normalized by the universal right-derived unit. Source: Stacks 0D6E
(blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitReductionDirectImageComparison :
    explicitExceptionalDirectImage f (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        (explicitReductionRestriction l E m n hmn X).mapDerivedCategory ≅
      (explicitReductionRestriction l E m n hmn V).mapDerivedCategory ⋙
        explicitExceptionalDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  proEtaleRingRestrictionDerivedDirectImage f
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (m + 1)))
    (proEtaleConstantRing V (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleConstantRing V (Padic.coefficientExtensionRing l E (m + 1)))
    (flatModelReductionRingMap l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) X)
    (flatModelReductionRingMap l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) V)
    (explicitCoefficientIso f (Padic.coefficientExtensionRing l E (n + 1)))
    (explicitCoefficientIso f (Padic.coefficientExtensionRing l E (m + 1)))
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (flatModelReductionCoefficientMap l E (m + 1) (n + 1)
        (Nat.add_le_add_right hmn 1)))).symm

/-- The specified derived coefficient comparison is the mate of identity on sections
under canonical pullback and K-flat-normalized scalar-extension adjunctions.
Its tensor formula is p tensor b ↦ p tensor b, also for the identity quotient.
Source: Stacks 06YY and 03EL (blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitExceptionalCoefficientComparison :
    explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        flatModelReduction l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) V ⟶
      flatModelReduction l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) X ⋙
        explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (m + 1)) :=
  (conjugateEquiv
    ((explicitReductionAdjunction l E m n hmn X).comp
      (explicitExceptionalPullbackAdjunction f (Padic.coefficientExtensionRing l E (m + 1))))
    ((explicitExceptionalPullbackAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1))).comp
        (explicitReductionAdjunction l E m n hmn V))).symm
    (explicitReductionDirectImageComparison l E m n hmn f).hom

/-- Preservation for the open and finite etale exceptional inverse images, expressed
under their ambient inverse-image identifications. All integer intervals are inclusive;
the same bounds work for every positive source and quotient coefficient exponent.
Source: Weil blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-exc-explicit-preservation, order 2063 (blueprint: thm-exc-explicit-preservation).

Proof, following all five DAG steps:
1. prop-exc-open-adjoint and prop-exc-finite-etale-adjoint identify the ambient right
adjoint with exact inverse image. prop-weil-pbc-proetale-constant-exact identifies
cohomology with inverse image of cohomology, on all unbounded complexes.
2. Pull back each locally closed constructible stratum and each trivializing covering.
lem-pur-scheme-constructible-preimage gives constructible underlying strata;
def-weil-proetale-inverse-image supplies base change of covers. Finite-limit and
colimit preservation (lem-weil-pbc-left-exact-site-inverse-image-tensor) preserve constant
sheaves and their module operations. prop-weil-pbc-proetale-constant-ring-map identifies
the scalar action. Finite module labels remain the same. This proves constructibility
and, with step 1, the cohomological interval of def-weil-constructible-intervals.
3. lem-sf-flat-model supplies a bounded flat model in the Tor interval.
lem-weil-pbc-ringed-topos-flat-module-pullback preserves its termwise flatness and
support. lem-pc-bounded-above-flat-kflat-site makes it K-flat. Tensoring with every
test module on V remains supported in that interval, proving the exact Tor bound.
4. Resolve an arbitrary input by flat K-flat terms (lem-pc-kflat-resolution).
lem-weil-pbc-ringed-pullback-preserves-kflat retains such a representative on V.
lem-pur-derived-change-of-rings computes both scalar extensions there. The ordinary
comparison lem-weil-pbc-ringed-topoi-module-pullback-tensor, with the constant-ring
identification, is identity on pure tensors. It represents the specified adjunction
mate, so the comparison is an isomorphism without a boundedness or flat-quotient
hypothesis.
5. For bounded constructible input with the given Tor bound,
lem-pur-finite-tensor-constructible-cohomology gives constructible reduction cohomology.
The Tor test with B gives vanishing outside the same interval. The action factors
through B; quotienting each local constant label by the kernel gives finite B-module
labels, including on empty covering members. lem-sf-reduction-flat-model gives the
same Tor interval over B. Apply steps 2 and 3 over B to the right side and transport
these properties across step 4 to the left side. Every bound is the original integer
bound, independent of both coefficient exponents. -/
theorem explicitExceptional_preservation
    (hn : ℕ) (_hf : IsOpenImmersion f ∨ (IsFinite f ∧ Etale f))
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v)) :
    (∀ (a b : ℤ) (_hab : a ≤ b)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (hn + 1))),
      WeilConjectures.constructibleInterval l E (hn + 1) (Nat.le_add_left 1 hn) X a b K →
      WeilConjectures.constructibleInterval l E (hn + 1) (Nat.le_add_left 1 hn) V a b
        ((explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (hn + 1))).obj K)) ∧
    (∀ (c d : ℤ) (_hcd : c ≤ d)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (hn + 1))),
      intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) X K →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (hn + 1)) K c d →
      HasProEtaleTorAmplitude V (Padic.coefficientExtensionRing l E (hn + 1))
        ((explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (hn + 1))).obj K)
          c d) ∧
    (∀ (hm : ℕ) (hmn' : hm ≤ hn)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (hn + 1))),
      IsIso ((explicitExceptionalCoefficientComparison l E hm hn hmn' f).app K)) ∧
    ∀ (hm : ℕ) (hmn' : hm ≤ hn) (c d : ℤ) (_hcd : c ≤ d)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (hn + 1))),
      intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) X K →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (hn + 1)) K c d →
      (intrinsicFiniteTorsionConstructible l E (hm + 1) (Nat.le_add_left 1 hm) V
        ((flatModelReduction l E (hm + 1) (hn + 1) (Nat.add_le_add_right hmn' 1) V).obj
          ((explicitExceptionalPullback f
            (Padic.coefficientExtensionRing l E (hn + 1))).obj K)) ∧
      HasProEtaleTorAmplitude V (Padic.coefficientExtensionRing l E (hm + 1))
        ((flatModelReduction l E (hm + 1) (hn + 1) (Nat.add_le_add_right hmn' 1) V).obj
          ((explicitExceptionalPullback f
            (Padic.coefficientExtensionRing l E (hn + 1))).obj K)) c d) ∧
      (intrinsicFiniteTorsionConstructible l E (hm + 1) (Nat.le_add_left 1 hm) V
        ((explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (hm + 1))).obj
          ((flatModelReduction l E (hm + 1) (hn + 1) (Nat.add_le_add_right hmn' 1) X).obj K)) ∧
      HasProEtaleTorAmplitude V (Padic.coefficientExtensionRing l E (hm + 1))
        ((explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (hm + 1))).obj
          ((flatModelReduction l E (hm + 1) (hn + 1) (Nat.add_le_add_right hmn' 1) X).obj K))
        c d) := by
  sorry

end AlgebraicGeometry.Scheme

