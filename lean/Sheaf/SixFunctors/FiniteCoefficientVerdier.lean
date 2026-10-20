/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.DualityPairing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.SixFunctors.FiniteDualitySiteComparison
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.SixFunctors.FiniteDualizing
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.FiniteCoefficientHomChange

/-! # Finite coefficient change for Verdier duality

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
node `cor-coef-finite-verdier` (blueprint: cor-coef-finite-verdier).

## Main definitions

* `FiniteVerdierCoherentComparison`: the evaluation, biduality, identity and cocycle diagrams.
* `FiniteVerdierSiteComparison`: those diagrams with the normalized scalar tensorator.
* `FiniteCoefficientVerdierComparison`: specialization to both finite coefficient sites.

## Main statements

* `finite_coefficient_verdier`: coefficient compatibility on finite-Tor constructible objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

namespace WeilConjectures

open AlgebraicGeometry.ProEtale

/-- Ordinary scalar extension on either of the two finite-coefficient sites.
Source: blueprint cor-coef-finite-verdier, proof step 6, ordinary balanced tensor.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierOrdinaryExtension
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- The ordinary scalar adjunction, with its actual sectionwise unit.
Source: blueprint cor-coef-finite-verdier, proof step 6.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierOrdinaryAdjunction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : finiteVerdierOrdinaryExtension J φ ⊣ Sheaf.restrictScalars J φ :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Additivity inherited from the ordinary scalar adjunction.
Source: blueprint cor-coef-finite-verdier, proof step 6.
(blueprint: cor-coef-finite-verdier). -/
instance finiteVerdierOrdinaryExtension_additive
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (finiteVerdierOrdinaryExtension J φ).Additive :=
  (finiteVerdierOrdinaryAdjunction J φ).left_adjoint_additive

/-- The oplax structure is ordinary scalar balancing, rather than a free tensorator.
Source: blueprint cor-coef-finite-verdier, proof step 6.
(blueprint: cor-coef-finite-verdier). -/
instance finiteVerdierOrdinaryExtension_oplax
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (finiteVerdierOrdinaryExtension J φ).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- The adjunct of the localized ordinary scalar unit, with the abelian structures
shared before specializing to sheaves. This is a construction, not an assumed map.
Source: blueprint cor-coef-finite-verdier, proof steps 1 and 6.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierScalarRepresentativeAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [HasDerivedCategory.{u + 1} C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [HasDerivedCategory.{u + 1} D]
    (L : C ⥤ D) [L.Additive] (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (ordinary : L ⊣ R) {S : DerivedCategory C ⥤ DerivedCategory D}
    (derived : S ⊣ R.mapDerivedCategory) (P : CochainComplex C ℤ) :
    S.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) :=
  (derived.homEquiv _ _).symm
    (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso C (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex ordinary.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ R)) (.up ℤ)).inv.app P) ≫
      R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj P))

/-- The derived scalar counit on a cochain representative. This is the adjunct of
localizing the ordinary unit, so it fixes the scalar tensor normalization without
assuming flatness of the quotient.
Source: blueprint cor-coef-finite-verdier, proof steps 1 and 6.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierScalarRepresentative
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (pbcFixedScalarExtension J φ).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((finiteVerdierOrdinaryExtension J φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  finiteVerdierScalarRepresentativeAux
    (finiteVerdierOrdinaryExtension J φ) (Sheaf.restrictScalars J φ)
    (finiteVerdierOrdinaryAdjunction J φ)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)) P

/-- The coefficient compatibility diagrams with all ambient structures shared explicitly.
This helper is specialized below to the two prescribed derived module categories.
Source: blueprint cor-coef-finite-verdier, proof steps 2--6.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierCoherentComparison
    (V : ℕ → Type v) [∀ n, Category.{w} (V n)]
    (T : ∀ n, V n ⥤ V n ⥤ V n) (H : ∀ n, (V n)ᵒᵖ ⥤ V n ⥤ V n)
    (W : ∀ n, V n) (P : ∀ n, ObjectProperty (V n))
    (Tor : ∀ n, ℤ → ℤ → ObjectProperty (V n))
    (S : ∀ {n m : ℕ}, m ≤ n → V n ⥤ V m)
    (unit : ∀ n, S (le_refl n) ≅ 𝟭 (V n))
    (comp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m), S h ⋙ S g ≅ S (g.trans h))
    (μ : ∀ {n m : ℕ} (h : m ≤ n),
      Functor.uncurry.obj (T n) ⋙ S h ≅
        (S h).prod (S h) ⋙ Functor.uncurry.obj (T m))
    (ev : ∀ n (K : V n), ((T n).obj (((H n).obj (op K)).obj (W n))).obj K ⟶ W n)
    (δ : ∀ n (K : V n),
      K ⟶ (dualityDoubleFunctor (H n) (W n)).obj K)
    (uMap : ∀ {n m : ℕ} (h : m ≤ n), (S h).obj (W n) ⟶ W m) (d : ℕ) : Prop :=
  ∃ comparison : ∀ {n m : ℕ} (h : m ≤ n),
      (H n).flip.obj (W n) ⋙ S h ⟶
        (S h).op ⋙ (H m).flip.obj (W m),
    (∀ {n m : ℕ} (h : m ≤ n) (K : V n), P n K →
      P m ((S h).obj K) ∧ IsIso ((comparison h).app (op K)) ∧
      ((T m).map ((comparison h).app (op K))).app ((S h).obj K) ≫ ev m ((S h).obj K) =
        (μ h).inv.app ((((H n).obj (op K)).obj (W n)), K) ≫
          (S h).map (ev n K) ≫ uMap h ∧
      (S h).map (δ n K) ≫
          (comparison h).app (op (((H n).obj (op K)).obj (W n))) =
        δ m ((S h).obj K) ≫
          ((H m).flip.obj (W m)).map (((comparison h).app (op K)).op) ∧
      (∀ a b : ℤ, a ≤ b → Tor n a b K →
        Tor m (-b - 2 * (d : ℤ)) (-a)
          ((S h).obj (((H n).obj (op K)).obj (W n))) ∧
        Tor m (-b - 2 * (d : ℤ)) (-a)
          (((H m).obj (op ((S h).obj K))).obj (W m)))) ∧
    (∀ (n : ℕ) (K : V n), P n K → (comparison (le_refl n)).app (op K) =
      (unit n).hom.app (((H n).obj (op K)).obj (W n)) ≫
        ((H n).flip.obj (W n)).map (((unit n).hom.app K).op)) ∧
    (∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m) (K : V n), P n K →
      (S g).map ((comparison h).app (op K)) ≫
          (comparison g).app (op ((S h).obj K)) ≫
          ((H r).flip.obj (W r)).map (((comp h g).inv.app K).op) =
        (comp h g).hom.app (((H n).obj (op K)).obj (W n)) ≫
          (comparison (g.trans h)).app (op K))

/-- The complete coefficient comparison on one fixed site. The dualizing maps `uMap`,
evaluations `ev`, and transposes `δ` are fixed before the comparisons are quantified.
The tensorator is normalized on ordinary cochain representatives, using the published
normalization predicate. Invertibility is asserted only on `P`, never on the whole
unbounded category. The two final equations are the identity and quotient cocycle,
with the canonical scalar associators displayed.
Source: blueprint cor-coef-finite-verdier, all clauses and proof steps 2--6.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierSiteComparison
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1}
      (R n))))
    (P : ∀ n : ℕ, ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1}
      (R n)))))
    (Tor : ∀ n : ℕ, ℤ → ℤ → ObjectProperty (DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} (R n)))))
    (T : ∀ n : ℕ,
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))) ⥤
          DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))
    (H : ∀ n : ℕ,
      (DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))ᵒᵖ ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))) ⥤
          DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))
    (ev : ∀ (n : ℕ) (K : DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} (R n)))),
      ((T n).obj (((H n).obj (op K)).obj (W n))).obj K ⟶ W n)
    (δ : ∀ (n : ℕ) (K : DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} (R n)))),
      K ⟶ (dualityDoubleFunctor (H n) (W n)).obj K)
    (uMap : ∀ {n m : ℕ} (h : m ≤ n),
      (pbcFixedScalarExtension J (φ h)).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  letI {n m : ℕ} (h : m ≤ n) : (finiteVerdierOrdinaryExtension J (φ h)).IsLeftAdjoint :=
    (finiteVerdierOrdinaryAdjunction J (φ h)).isLeftAdjoint
  ∃ μ : ∀ {n m : ℕ} (h : m ≤ n),
      Functor.uncurry.obj (T n) ⋙ pbcFixedScalarExtension J (φ h) ≅
        (pbcFixedScalarExtension J (φ h)).prod (pbcFixedScalarExtension J (φ h)) ⋙
          Functor.uncurry.obj (T m),
    (∀ {n m : ℕ} (h : m ≤ n), ∃ e,
      Etale.ExceptionalCoefficients.TensorNormalizationAux
        (finiteVerdierOrdinaryExtension J (φ h)) (pbcFixedScalarExtension J (φ h))
        (finiteVerdierScalarRepresentative J (φ h)) e ∧ HEq (μ h) e) ∧
    @FiniteVerdierCoherentComparison
      (fun n ↦ DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))
      (fun _n ↦ inferInstance) T H W P Tor
      (fun {_ _} h ↦ pbcFixedScalarExtension J (φ h))
      (fun n ↦ normalizedOriginScalarUnit J (φ (le_refl n)) (φId n))
      (fun {_ _ _} h g ↦ pbcFixedScalarExtensionComp J (φ h) (φ g) (φ (g.trans h))
        (φComp h g)) μ ev δ (fun {_ _} h ↦ uMap h) d

/-- Evaluation projected from the recorded, normalized etale pairing.
The coefficient category is shared before specializing to modules.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleEvaluation
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) {W : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (h : Etale.AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((Etale.derivedTensor A X).obj (((Etale.derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  h.choose_spec.2.choose K

/-- Evaluation projected from the recorded, normalized pro-etale pairing.
The coefficient category is shared before specializing to modules.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4 and 7.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleEvaluation
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : ProEtale.AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((ProEtale.derivedTensor A X).obj
      (((ProEtale.derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  h.choose_spec.2.choose K

/-- The recorded pro-etale double-dual arrow with the published Hom wrapper.
Source: blueprint cor-coef-finite-verdier, proof step 4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleBiduality
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : ProEtale.AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ (dualityDoubleFunctor (ProEtale.derivedHom A X) W).obj K :=
  ProEtale.AmbientDualityPairing.bidualityMap A X h K

/-- The published Etale derived tensor, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleTensorAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  Etale.derivedTensor (ModuleCat.{u + 1} R) X

/-- The published Etale derived hom, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleHomAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))ᵒᵖ ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  Etale.derivedHom (ModuleCat.{u + 1} R) X

/-- The recorded normalized Etale pairing, specialized to module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtalePairingAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) : Prop :=
  Etale.AmbientDualityPairing (ModuleCat.{u + 1} R) X W

/-- The specified Etale evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleEvaluationAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    (h : finiteVerdierEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    ((finiteVerdierEtaleTensorAt R X).obj 
      (((finiteVerdierEtaleHomAt R X).obj (op K)).obj W)).obj K ⟶
      W :=
  finiteVerdierEtaleEvaluation (ModuleCat.{u + 1} R) X h K

/-- The specified Etale transpose of evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleBidualityAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    (h : finiteVerdierEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    K ⟶ (dualityDoubleFunctor (finiteVerdierEtaleHomAt R X) W).obj K :=
  Etale.AmbientDualityPairing.bidualityMap (ModuleCat.{u + 1} R) X h K

/-- The published ProEtale derived tensor, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleTensorAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :=
  ProEtale.derivedTensor (ModuleCat.{u + 1} R) X

/-- The published ProEtale derived hom, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleHomAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))ᵒᵖ ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :=
  ProEtale.derivedHom (ModuleCat.{u + 1} R) X

/-- The recorded normalized ProEtale pairing, specialized to module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtalePairingAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) : Prop :=
  ProEtale.AmbientDualityPairing (ModuleCat.{u + 1} R) X W

/-- The specified ProEtale evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleEvaluationAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (h : finiteVerdierProEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    ((finiteVerdierProEtaleTensorAt R X).obj 
      (((finiteVerdierProEtaleHomAt R X).obj (op K)).obj W)).obj K ⟶
      W :=
  finiteVerdierProEtaleEvaluation (ModuleCat.{u + 1} R) X h K

/-- The specified ProEtale transpose of evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleBidualityAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (h : finiteVerdierProEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    K ⟶ (dualityDoubleFunctor (finiteVerdierProEtaleHomAt R X) W).obj K :=
  finiteVerdierProEtaleBiduality (ModuleCat.{u + 1} R) X h K

/-- The etale specialization of the full coefficient diagrams.
Source: blueprint cor-coef-finite-verdier, proof steps 2--7.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierEtaleComparison
    (X : Scheme.{u}) (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n, Etale.DerivedCategoryModule (R n) X)
    (Pet : ∀ n, ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (_Ppro : ∀ n, ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (TorEt : ∀ n, ℤ → ℤ → ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (_TorPro : ∀ n, ℤ → ℤ → ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (uEt : ∀ {n m : ℕ} (h : m ≤ n), (Etale.scalarExtension (φ h) X).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  (∃ hEt : ∀ n : ℕ, finiteVerdierEtalePairingAt
      (R n) X (W n),
    @FiniteVerdierSiteComparison _ _ _ X.smallEtaleTopology R
      (fun _n ↦ inferInstance) (fun {_ _} h ↦ φ h)
      φId (fun {_ _ _} h g ↦ φComp h g)
      W
      Pet
      TorEt
      (fun n ↦ finiteVerdierEtaleTensorAt (R n) X)
      (fun n ↦ finiteVerdierEtaleHomAt (R n) X)
      (fun n ↦ finiteVerdierEtaleEvaluationAt (R n) X (hEt n))
      (fun n ↦ finiteVerdierEtaleBidualityAt (R n) X (hEt n))
      (fun {_ _} h ↦ uEt h) d)

/-- The pro-etale specialization, with transported dualizing object and coefficient map.
Source: blueprint cor-coef-finite-verdier, proof steps 2--7.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierProEtaleComparison
    (X : Scheme.{u}) (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n, Etale.DerivedCategoryModule (R n) X)
    (_Pet : ∀ n, ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (Ppro : ∀ n, ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (_TorEt : ∀ n, ℤ → ℤ → ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (TorPro : ∀ n, ℤ → ℤ → ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (uEt : ∀ {n m : ℕ} (h : m ≤ n), (Etale.scalarExtension (φ h) X).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  let F := fun n ↦ (comparisonUpperStar (ModuleCat.{u + 1}
    (R n)) X).mapDerivedCategory
  (∃ hPro : ∀ n : ℕ, finiteVerdierProEtalePairingAt
      (R n) X ((F n).obj (W n)),
    @FiniteVerdierSiteComparison _ _ _ (Scheme.ProEt.topology X) R
      (fun _n ↦ inferInstance) (fun {_ _} h ↦ φ h)
      φId (fun {_ _ _} h g ↦ φComp h g)
      (fun n ↦ (F n).obj (W n))
      Ppro
      TorPro
      (fun n ↦ finiteVerdierProEtaleTensorAt (R n) X)
      (fun n ↦ finiteVerdierProEtaleHomAt (R n) X)
      (fun n ↦ finiteVerdierProEtaleEvaluationAt (R n) X (hPro n))
      (fun n ↦ finiteVerdierProEtaleBidualityAt (R n) X (hPro n))
      (fun {n m} h ↦ (pbcComparisonReduction X (φ h)).hom.app
        (W n) ≫ (F m).map (uEt h)) d)

/-- Both sites with the same coefficient tower and dimension bound.
Source: blueprint cor-coef-finite-verdier, proof steps 2--7.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierTwoSitesComparison
    (X : Scheme.{u}) (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n, Etale.DerivedCategoryModule (R n) X)
    (Pet : ∀ n, ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (Ppro : ∀ n, ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (TorEt : ∀ n, ℤ → ℤ → ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (TorPro : ∀ n, ℤ → ℤ → ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (uEt : ∀ {n m : ℕ} (h : m ≤ n), (Etale.scalarExtension (φ h) X).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  FiniteVerdierEtaleComparison X R (fun {_ _} h ↦ φ h) φId
    (fun {_ _ _} h g ↦ φComp h g) W Pet Ppro TorEt TorPro (fun {_ _} h ↦ uEt h) d ∧
  FiniteVerdierProEtaleComparison X R (fun {_ _} h ↦ φ h) φId
    (fun {_ _ _} h g ↦ φComp h g) W Pet Ppro TorEt TorPro (fun {_ _} h ↦ uEt h) d

/-- Both finite coefficient sites, with the pro-etale dualizing object explicitly
transported from the etale object. Positive levels are indexed by `n+1`; hence all
levels in the node, including level one and all identity quotients, occur.
Source: blueprint cor-coef-finite-verdier, proof steps 1 and 7.
(blueprint: cor-coef-finite-verdier). -/
def FiniteCoefficientVerdierComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (d : ℕ) (X : Scheme.{u})
    (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] : Prop :=
  @FiniteVerdierTwoSitesComparison X (finiteDualizingCoeff l E)
    (fun _n ↦ inferInstance) (fun {_ _} h ↦ finiteDualizingQuotient l E h)
    (finiteDualizingQuotient_id l E) (fun {_ _ _} h g ↦ finiteDualizingQuotient_comp l E h g)
    (finiteDualizingEtaleTerm l E D X)
    (fun n ↦ finiteTorConstructibleEtale l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun n ↦ finiteTorConstructibleProEtaleModule l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun n ↦ Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E n) X)
    (fun n a b K ↦ Scheme.HasProEtaleTorAmplitude X
      (Padic.coefficientExtensionRing l E (n + 1))
      ((ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj K) a b)
    (fun {_ _} h ↦ finiteDualizingEtaleComparison l E D X h) d

/-- Finite reductions of Verdier duality, including both sites and all coefficient
quotients. The compatibility equations use the specified evaluation and its transpose.
Source: Weil conjectures blueprint, cor-coef-finite-verdier, order 2142 (main: 2486).
(blueprint: cor-coef-finite-verdier).

Proof:
1. By lem-weil-verdier-preservation-strata the etale dualizing object is finite-Tor
   constructible. A bounded flat model (lem-sf-flat-model) stays bounded and flat
   after reduction; thm-constructible-serre gives constructibility of its cohomology.
2. Apply thm-coef-finite-hom to (K,omega_A), then compose with Hom(K_B,u) for
   the counit-defined u of lem-coef-finite-dualizing. This gives the natural comparison
   and its invertibility on finite-Tor constructible K, without asserting it elsewhere.
3. Its tensor-Hom transpose is scalar extension of evaluation followed by u. The
   balancing tensor comparison gives exactly the displayed evaluation equation.
4. Transpose that equation once more using lem-weil-duality-pairing. Naturality in
   K and the symmetry identify the two transposes, yielding the double-dual square
   S(delta_K);d_DK = delta_KB;D_B(d_K).
5. The quotient cocycles of thm-coef-finite-hom and lem-coef-finite-dualizing,
   together with lem-fix-operation-reduction, give the displayed composite equation.
   Their unit normalizations give the identity case, including at level one.
6. Verdier preservation gives [-b-2d,-a] for D_AK. For every B-module sheaf N,
   (P tensor_A B) tensor_B N is isomorphic to P tensor_A N by balancing, with
   inverse p tensor z mapping to (p tensor 1) tensor z. K-flat computation from
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves the interval after
   reduction. The comparison isomorphism gives the same interval for D_B(K_B).
7. Use lem-sf-proetale-constructible-origin and lem-sf-comparison-tor-amplitude to
   represent a pro-etale input by an etale input with the same interval. Transport
   omega and u by comparison pullback and pbcComparisonReduction. The evaluation
   comparisons of lem-weil-finite-duality-site-comparison identify the Hom map and
   its transpose. Thus steps 2--5 give both equations and the cocycle there, and the
   same balanced-tensor argument in step 6 gives both pro-etale Tor bounds.
-/
theorem finite_coefficient_verdier
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (d : ℕ) (X : Scheme.{u})
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    FiniteCoefficientVerdierComparison D l hl E d X hd := by
  sorry

end WeilConjectures
