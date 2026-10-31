/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction
public import WeilConjectures.AlgebraicGeometry.ConstructibleIntervalsUnordered
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingMap
import all WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor

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

private theorem normalizedDerivedAdjunction_unique
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (a : F ⊣ G) (b b' : LF ⊣ G.mapDerivedCategory)
    (hres : ∀ X : HomotopyCategory C (.up ℤ),
      ∃ (P : CochainComplex C ℤ)
        (s : (HomotopyCategory.quotient C (.up ℤ)).obj P ⟶ X),
        IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ∧
          HomotopyCategory.quasiIso C (.up ℤ) s)
    (hb : explicitDerivedUnitNormalized F G LF ε a b)
    (hb' : explicitDerivedUnitNormalized F G LF ε a b') : b = b' := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro X
  obtain ⟨P, s, hsε, hs⟩ := hres X
  have : IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := hsε
  have hu : b.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)) =
      b'.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := by
    apply (cancel_mono
      (G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient C (.up ℤ)).obj P)))).mp
    exact (hb P).trans (hb' P).symm
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh _ _ hs
  apply (cancel_epi (DerivedCategory.Qh.map s)).mp
  change (𝟭 (DerivedCategory C)).map (DerivedCategory.Qh.map s) ≫ b.unit.app _ =
    (𝟭 (DerivedCategory C)).map (DerivedCategory.Qh.map s) ≫ b'.unit.app _
  rw [b.unit.naturality, b'.unit.naturality, hu]

private theorem normalizedDerivedAdjunction_existsUnique
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (a : F ⊣ G)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ)))
    (hres : ∀ X : HomotopyCategory C (.up ℤ),
      ∃ (P : CochainComplex C ℤ)
        (s : (HomotopyCategory.quotient C (.up ℤ)).obj P ⟶ X),
        IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ∧
          HomotopyCategory.quasiIso C (.up ℤ) s) :
    ∃! b : LF ⊣ G.mapDerivedCategory, explicitDerivedUnitNormalized F G LF ε a b := by
  obtain ⟨b, hb⟩ := ScalarReductionDerivedProof.derivedAdjunction_of_resolutions
    F G a LF ε hLF (fun X ↦ by
      obtain ⟨P, s, hP, hs⟩ := hres X
      exact ⟨_, s, hP, hs⟩)
  have hn : explicitDerivedUnitNormalized F G LF ε a b :=
    fun P ↦ hb ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  refine ⟨b, hn, ?_⟩
  intro other hother
  exact normalizedDerivedAdjunction_unique F G LF ε a other b hres hother hn

attribute [local irreducible] Functor.mapHomotopyCategory DerivedCategory.Qh DerivedCategory.Q
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

private theorem normalizedRingDerivedAdjunction
    {Y : Scheme.{u}} [EssentiallySmall.{u + 1} Y.ProEt]
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    [HasDerivedCategory.{u + 2} (proEtaleRingModules Y R)]
    [HasDerivedCategory.{u + 2} (proEtaleRingModules Y S)]
    (F : proEtaleRingModules Y R ⥤ proEtaleRingModules Y S) [F.Additive]
    (G : proEtaleRingModules Y S ⥤ proEtaleRingModules Y R) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G)
    (H : ∃ (LF : DerivedCategory (proEtaleRingModules Y R) ⥤
        DerivedCategory (proEtaleRingModules Y S))
      (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (proEtaleRingModules Y R) ℤ,
          P.IsKFlatIndependentCoefficients →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    ∃! b : H.choose ⊣ G.mapDerivedCategory,
      explicitDerivedUnitNormalized F G H.choose H.choose_spec.choose adj b := by
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  apply normalizedDerivedAdjunction_existsUnique F G H.choose H.choose_spec.choose adj
    H.choose_spec.choose_spec.1
  intro Z
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨P, s, hP, hs⟩ := ScalarReductionDerivedProof.kFlatResolutions
    (J := ProEt.topology Y) (O := R) K
  exact ⟨P, (HomotopyCategory.quotient _ _).map s,
    H.choose_spec.choose_spec.2.2 P hP,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactorsh
  explicitReductionModuleAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact @normalizedRingDerivedAdjunction.{u} T inferInstance
    (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (m + 1)))
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (flatModelReductionChange l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)
    inferInstance (explicitReductionRestriction l E m n hmn T)
    inferInstance inferInstance inferInstance
    (explicitReductionModuleAdjunction l E m n hmn T)
    (flatModelReductionDerivedData l E (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) T)

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

private theorem explicitExceptionalCoefficientComparison_isIso
    (hm hn : ℕ) (hmn' : hm ≤ hn) :
    IsIso (explicitExceptionalCoefficientComparison l E hm hn hmn' f) := by
  dsimp only [explicitExceptionalCoefficientComparison]
  infer_instance

private theorem constructible_pullback {U Y : Scheme.{u}} (g : U ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hM : IsConstructibleProEtaleModuleSheaf Y A M) :
    IsConstructibleProEtaleModuleSheaf U A
      ((proEtaleConstantRingPullback A g).obj M) := by
  let B := ULift.{u + 1, u} A
  have hc := (proEtaleModuleRestriction_constructible_iff Y A M).mp hM
  obtain ⟨N, hN, ⟨eN⟩⟩ :=
    ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj B hc
  let := hN
  have := IsConstructibleSheaf.upperStar g N
  have hd := ProEtale.isConstructible_comparisonUpperStar_obj
    ((Etale.upperStar (ModuleCat.{u + 1} B) g).obj N)
  obtain ⟨eM⟩ := proEtaleModuleRestriction_pullback g A M
  apply (proEtaleModuleRestriction_constructible_iff U A _).mpr
  apply ProEtale.isConstructible_of_iso
    (((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) g).app N).symm ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} B) g).mapIso eN ≪≫ eM.symm) hd

private theorem constructible_interval_pullback (hn : ℕ) (a b : ℤ)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (hn + 1)))
    (hK : WeilConjectures.constructibleInterval l E (hn + 1) (Nat.le_add_left 1 hn)
      X a b K) :
    WeilConjectures.constructibleInterval l E (hn + 1) (Nat.le_add_left 1 hn) V a b
      ((explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (hn + 1))).obj K) := by
  let A := Padic.coefficientExtensionRing l E (hn + 1)
  let F := proEtaleConstantRingPullback A f
  change (intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) V
    (F.mapDerivedCategory.obj K)) ∧ _
  have hv (i : ℤ) (hi : ¬ i ∈ Set.Icc a b) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj (F.mapDerivedCategory.obj K)) := by
    have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
      by_contra h
      exact hi (hK.2 h)
    exact (F.map_isZero hz).of_iso ((F.mapDerivedCategoryHomologyFunctorIso i).app K).symm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply (Set.finite_Icc a b).subset
    intro i hi
    by_contra h
    exact hi (hv i h)
  · intro i
    exact constructibleProEtale_of_iso V A
      ((F.mapDerivedCategoryHomologyFunctorIso i).app K)
      (constructible_pullback f A _ (hK.1.2 i))
  · intro i hi
    by_contra h
    exact hi (hv i h)

private theorem torAmplitude_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude Y A K a b) : HasProEtaleTorAmplitude Y A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC g hg hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ g hg hP M i hi

private theorem torAmplitude_pullback (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    HasProEtaleTorAmplitude V A ((explicitExceptionalPullback f A).obj K) a b := by
  let ex := sfIntrinsicDerivedEquivalence X A
  let ev := sfIntrinsicDerivedEquivalence V A
  let H := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  let L := ex.inverse.obj K
  have hx : HasProEtaleTorAmplitude X A (ex.functor.obj L) a b :=
    torAmplitude_iso X A (ex.counitIso.app K).symm a b h
  have hL := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A X a b h.1 L).mp hx
  have hP : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V a b (H.mapDerivedCategory.obj L) :=
    (ProEtale.DerivedCategory.torAmplitudeIn _ V a b).prop_of_iso
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ f).app L)
      (ProEtale.torAmplitudeIn_leftDerivedUpperStar _ f a b hL)
  let e : (explicitExceptionalPullback f A).obj K ≅
      ev.functor.obj (H.mapDerivedCategory.obj L) :=
    (openSquareDerivedPullbackModel A f).app K ≪≫
      (Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence X A).inverse
        (H ⋙ (sfIntrinsicModuleEquivalence V A).functor)).app K ≪≫
      (Functor.mapDerivedCategoryCompIso H (sfIntrinsicModuleEquivalence V A).functor).app L
  exact torAmplitude_iso V A e.symm a b
    ((ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A V a b h.1 _).mpr hP)

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

private theorem coefficientReduction_preservation (Y : Scheme.{u})
    (hm hn : ℕ) (hmn' : hm ≤ hn)
    (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (hn + 1)))
    (hK : intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) Y K)
    (a b : ℤ)
    (ht : HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (hn + 1)) K a b) :
    intrinsicFiniteTorsionConstructible l E (hm + 1) (Nat.le_add_left 1 hm) Y
      ((flatModelReduction l E (hm + 1) (hn + 1) (Nat.add_le_add_right hmn' 1) Y).obj K) ∧
    HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (hm + 1))
      ((flatModelReduction l E (hm + 1) (hn + 1) (Nat.add_le_add_right hmn' 1) Y).obj K) a b := by
  let q := Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (hn + 1))
    (T := Padic.coefficientExtensionIdeal l E (hm + 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn' 1))
  let e : flatModelReduction l E (hm + 1) (hn + 1)
        (Nat.add_le_add_right hmn' 1) Y ≅ ProEtale.scalarExtensionFunctor q Y :=
    Adjunction.leftAdjointUniq (explicitReductionAdjunction l E hm hn hmn' Y)
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) q))
  have hc := ProEtale.scalarExtension_constructible q Y K hK.1 hK.2
  have ht' := ProEtale.scalarExtension_tor q Y K a b ht
  have hb := ProEtale.scalarExtension_bounded_of_tor Y _ _ a b ht'
  exact ⟨intrinsicConstructible_iso l E Y hm (e.app K).symm ⟨hb, hc⟩,
    torAmplitude_iso Y _ (e.app K).symm a b ht'⟩

private theorem intrinsicConstructible_pullback (hn : ℕ)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (hn + 1)))
    (hK : intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) X K) :
    intrinsicFiniteTorsionConstructible l E (hn + 1) (Nat.le_add_left 1 hn) V
      ((explicitExceptionalPullback f (Padic.coefficientExtensionRing l E (hn + 1))).obj K) := by
  classical
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.bddAbove
  exact (constructible_interval_pullback l E f hn a b K
    ⟨hK, fun i hi ↦ ⟨ha hi, hb hi⟩⟩).1

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab K hK
    exact constructible_interval_pullback l E f hn a b K hK
  · intro c d hcd K hK ht
    exact torAmplitude_pullback f _ K c d ht
  · intro hm hmn' K
    have := explicitExceptionalCoefficientComparison_isIso l E f hm hn hmn'
    infer_instance
  · intro hm hmn' c d hcd K hK ht
    obtain ⟨hc, ht'⟩ := coefficientReduction_preservation l E X hm hn hmn' K hK c d ht
    have hp := intrinsicConstructible_pullback l E f hm _ hc
    have htp := torAmplitude_pullback f _ _ c d ht'
    have := explicitExceptionalCoefficientComparison_isIso l E f hm hn hmn'
    let e := asIso ((explicitExceptionalCoefficientComparison l E hm hn hmn' f).app K)
    exact ⟨⟨intrinsicConstructible_iso l E V hm e.symm hp,
      torAmplitude_iso V _ e.symm c d htp⟩, hp, htp⟩

end AlgebraicGeometry.Scheme
