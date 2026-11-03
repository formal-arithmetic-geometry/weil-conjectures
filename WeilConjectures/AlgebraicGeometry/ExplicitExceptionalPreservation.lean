/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Invertible
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

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
set_option synthInstance.maxSize 4096

universe u v₁ v₂ w₁ w₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

attribute [local irreducible] AlgebraicGeometry.Scheme.flatModelReductionData
  AlgebraicGeometry.Scheme.flatModelReductionDerivedData

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.Scheme

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

set_option maxHeartbeats 800000 in
-- Elaborating the sheafification tensor adjunction involves large site instances.
private theorem normalizedScalarAdjunction_existsUnique {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (F : proEtaleRingModules T R ⥤ proEtaleRingModules T S)
    (h : ∀ M : proEtaleRingModules T R, F.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (g : M ⟶ N), F.map g = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom φ M g ≫ eqToHom (h N).symm) :
    ∃! adj : F ⊣ proEtaleRingRestrictScalars φ,
      explicitScalarUnitNormalized φ F h adj := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  obtain ⟨adj, hn⟩ :=
    SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications
      (K := ProEt.topology T) φ F h hm
  refine ⟨adj, hn, ?_⟩
  intro other hother
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (hother M U x).trans (hn M U x).symm

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
  exact normalizedScalarAdjunction_existsUnique
    (flatModelReductionRingMap l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)
    (flatModelReductionChange l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)
    (flatModelReductionData l E (m + 1) (n + 1)
      (Nat.add_le_add_right hmn 1) T).choose_spec.choose
    (flatModelReductionData l E (m + 1) (n + 1)
      (Nat.add_le_add_right hmn 1) T).choose_spec.choose_spec.choose

/-- The uniquely tensor-unit normalized ordinary adjunction. Source: Stacks 03EK
(blueprint: thm-exc-explicit-preservation). -/
noncomputable def explicitReductionModuleAdjunction :=
  (explicitReductionModuleAdjunction_existsUnique l E m n hmn T).choose

attribute [local irreducible] Functor.mapHomotopyCategory DerivedCategory.Qh DerivedCategory.Q
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactorsh
  explicitReductionModuleAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n)
  {V X : Scheme.{u}} (f : V ⟶ X)

private theorem torAmplitude_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude Y A K a b) : HasProEtaleTorAmplitude Y A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC g hg hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ g hg hP M i hi

private theorem intrinsicConstructible_iso (Y : Scheme.{u}) (hn : ℕ)
    {K L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (hn + 1))}
    (e : K ≅ L)
    (h : intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) Y K) :
    intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) Y L := by
  constructor
  · apply h.1.subset
    intro i hi hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · intro i
    exact constructibleProEtale_of_iso Y _
      ((DerivedCategory.homologyFunctor _ i).mapIso e) (h.2 i)

end AlgebraicGeometry.Scheme
