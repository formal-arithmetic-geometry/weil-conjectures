/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction

/-! # Integration normalization of vector purity

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-normalization).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The existing derived monoidal structure, elaborated with the same abstract coefficient
interface as `Etale.derivedTensor`. This is a cache of the existing structure.
Source: `Etale.TensorStructure`, implementation notes
(blueprint: def-pur-vector-purity-normalization). -/
@[implicit_reducible]
def purityEtaleMonoidal (A : Type v₁) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) : MonoidalCategory
      (DerivedCategory (Sheaf T.smallEtaleTopology A)) :=
  inferInstance

/-- Cache the published tensor structure at concrete module coefficients, retaining the
generic coefficient instance choices. Source: `Etale.TensorStructure`, implementation notes
(blueprint: def-pur-vector-purity-normalization). -/
instance (priority := high) purityModuleEtaleMonoidal
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  purityEtaleMonoidal (ModuleCat.{u + 1} A) T

/-- Ordinary compact support using the chosen global Nagata compactification.
Source: ordinary six operations (blueprint: def-pur-vector-purity-normalization). -/
abbrev RfShriek (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :=
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
/-- The Brown right adjoint of ordinary compact support, determined with its adjunction.
Source: ordinary six operations (blueprint: def-pur-vector-purity-normalization). -/
abbrev RfUpper (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :=
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f
/-- The existing ordinary K-flat derived inverse image.
Source: ordinary six operations (blueprint: def-pur-vector-purity-normalization). -/
abbrev RfPullback (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Etale.ordinaryFinitePullback A f
/-- The ordinary finite Tate coefficient of integration, with its canonical annihilator.
Source: vector-bundle integration, C_pi (blueprint: def-pur-vector-purity-normalization). -/
noncomputable abbrev vectorPurityEtaleCoefficient (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) (F : B.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :=
  AlgebraicGeometry.Etale.vectorIntegrationCoefficient P.Coefficient
    (ringChar P.Coefficient) ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B d F

/-- The actual ordinary-etale integration trace, with no site-comparison transport.
Source: vector-bundle integration (blueprint: def-pur-vector-purity-normalization). -/
def vectorPurityTrace (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) (F : B.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [Finite P.Coefficient]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (hN : IsUnit (ringChar P.Coefficient : Γ(B, ⊤))) :
    (RfShriek P.Coefficient (VectorBundleZeroSection.π B d F)).obj
        (P.vectorPurityEtaleCoefficient B d F) ⟶
          𝟙_ (DerivedCategory (Sheaf B.smallEtaleTopology
            (ModuleCat.{u + 1} P.Coefficient))) :=
  Etale.vectorBundleIntegration (ringChar P.Coefficient)
    (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
    P.Coefficient ((ringChar.spec P.Coefficient _).mpr dvd_rfl)
    B hN d F ≫ (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom

/-- Purity specified by the counit equations of integration, in arbitrary categories.
This helper only factors the expression; all its arguments below are the actual operations.
Source: blueprint vector-bundle purity (blueprint: def-pur-vector-purity-normalization). -/
def IntegrationPurityNormalized {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R)
    (W : C) (t : L.obj W ⟶ 𝟙_ D)
    {S T : D ⥤ D} (projection : S ⟶ T) (Q : ObjectProperty D)
    (α : Q.ι ⋙ R ≅ Q.ι ⋙ (P ⋙ tensorLeft W)) : Prop :=
  ∀ K : Q.FullSubcategory, ∃ m : T.obj K.obj ⟶ K.obj,
    HEq (L.map (α.inv.app K) ≫ adj.counit.app K.obj) m ∧
      HEq (projection.app K.obj ≫ m) ((t ▷ K.obj) ≫ (λ_ K.obj).hom)

/-- The unique purity family normalized by the actual projection and integration counit,
with its coefficient-unit value. Source: sk-prop-an, integration and Proposition
(blueprint: def-pur-vector-purity-normalization). -/
def IntegrationPurity {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R)
    (W : C) (t : L.obj W ⟶ 𝟙_ D)
    {S T : D ⥤ D} (projection : S ⟶ T) (Q : ObjectProperty D) : Prop :=
  (∀ K : Q.FullSubcategory, IsIso (projection.app K.obj)) ∧
    (∃! α : Q.ι ⋙ R ≅ Q.ι ⋙ (P ⋙ tensorLeft W),
      IntegrationPurityNormalized L R P adj W t projection Q α) ∧
    (∃! β : R.obj (𝟙_ D) ≅ W, L.map β.inv ≫ adj.counit.app (𝟙_ D) = t)

/-- The normalized purity family and its unit value in ordinary derived coordinates.
Uniqueness fixes the family by integration and the actual Brown-adjunction counit.
Source: vector-bundle purity (blueprint: def-pur-vector-purity-normalization). -/
def VectorPurityFunctorConclusion (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (Q : ObjectProperty (DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} A))))
    (W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (t : (RfShriek A f).obj W ⟶ 𝟙_ _) : Prop :=
  IntegrationPurity (RfShriek A f) (RfUpper A f) (RfPullback A f)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
    W t
    ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W) Q


/-- The normalized transport of finite Tate lines. Its roots and pure-tensor equations
fix both fields uniquely. Source: sk-prop-an, Tate pullback comparisons
(blueprint: def-pur-vector-purity-normalization). -/
def purityTwistTransport (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :=
  (Etale.exists_ordinaryFiniteP1Adjunction N hN A hA).choose

/-- The inverse-purity family has the actual twist/pullback source and Brown target.
Source: sk-prop-an, integration adjunct (blueprint: def-pur-vector-purity-normalization). -/
abbrev VectorPurityGamma (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (B : Scheme.{u}) [IsNoetherian B]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)] :=
  RfPullback A (VectorBundleZeroSection.π B d F) ⋙
      tensorLeft (Etale.vectorIntegrationCoefficient A N hA B d F) ⟶
    RfUpper A (VectorBundleZeroSection.π B d F)

/-- The counit/projection equations determine every component uniquely: transpose
under the Brown adjunction after inverse projection. HEq retains the published
projection functor's exact presentation. Source: sk-prop-an, Steps 1--2
(blueprint: def-pur-vector-purity-normalization). -/
def IntegrationGammaNormalized {C : Type v₁} {D : Type v₂}
    [Category.{w₁} C] [Category.{w₂} D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R) (W : C) (t : L.obj W ⟶ 𝟙_ D)
    {S T : D ⥤ D} (projection : S ⟶ T)
    (γ : P ⋙ tensorLeft W ⟶ R) : Prop :=
  ∀ K : D, ∃ m : T.obj K ⟶ K,
    HEq (L.map (γ.app K) ≫ adj.counit.app K) m ∧
      HEq (projection.app K ≫ m) ((t ▷ K) ≫ (λ_ K).hom)

/-- The independently normalized inverse-purity family for one bundle. This condition
uses no base-change, sum or reduction equation; in each component the adjunction and
invertible projection uniquely fix gamma. Source: sk-prop-an, Steps 1--2
(blueprint: def-pur-vector-purity-normalization). -/
def VectorPurityGammaNormalized (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F) : Prop :=
  IntegrationGammaNormalized
    (RfShriek A (VectorBundleZeroSection.π B d F))
    (RfUpper A (VectorBundleZeroSection.π B d F))
    (RfPullback A (VectorBundleZeroSection.π B d F))
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π B d F))
    (Etale.vectorIntegrationCoefficient A N hA B d F)
    (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom)
    ((Etale.projectionMap (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π B d F)).app
        (Etale.vectorIntegrationCoefficient A N hA B d F)) γ


end WeilConjectures.PurityFiniteSetting
