/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Algebra.Homology.InternalHomLocalizationComparison
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Algebra.Homology.InternalHomLocalizationComparison
import Sheaf.Paper.IntegralSectionScalarTelescope
import Sheaf.Paper.IntegralSectionHomContinuity
import Sheaf.Algebra.Homology.ScalarTelescopeHomComparison
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian


/-! # Integral internal Hom and inversion of ell

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
with the coefficient-specific general-lfp bridge and internal-sheaf extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion).

The section-module presentation is the existing exact equivalence from internal modules.
The comparison is the existing evaluation transpose. Scalar telescopes are termwise
colimits of complexes, in the ordinary unbounded derived category.
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

attribute [local irreducible] derivedInternalHomOfUniverses SheafOfModules.monoidalCategory
  CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Localization.Monoidal.instMonoidalCategoryLocalizedMonoidal
  CategoryTheory.Localization.Monoidal.monoidalCategoryStruct
  HasDerivedCategory.ofIsGrothendieckAbelian CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint CategoryTheory.homComplexFunctor
  WeilConjectures.coefficientHomResolution WeilConjectures.coefficientHomResolutionIso
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf
  CategoryTheory.InternalAbelianSheafModule.sectionScalarMap
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  CategoryTheory.sheafCompose
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint
  AlgebraicGeometry.ProEtale.laxBraided_upperStarFromPoint
  AlgebraicGeometry.ProEtale.upperStar
  Profinite.continuousMapRingSheaf

namespace AlgebraicGeometry.ProEtale.IntegralHomInversion

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u})

/-- The canonical sheafification instance, named to share its construction.
Source: Stacks 00W1; the existing small pro-etale sheafification.
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable local instance siteSheafify :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance

/-- The existing monoidal sheaf structure, named to share its instance term.
Source: Stacks 00W1; sheafification of the tensor product of abelian presheaves.
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable local instance siteMonoidal :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) := inferInstance

/-- The existing integral condensed coefficient object pulled to X.
Source: Bhatt--Scholze 6.8.11--6.8.14
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev integral := condensedRingObj (Profinite.padicIntegersRingObj l E.1) X

/-- The canonical coefficient multiplication, named without changing its construction.
Source: Bhatt--Scholze 6.8.11; pullback of the condensed coefficient ring.
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable local instance integralMonObj : MonObj (integral l E X) := inferInstance

/-- The canonical rational multiplication, named to share its construction.
Source: Bhatt--Scholze 6.8.14; pullback of the condensed coefficient field.
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable local instance rationalMonObj :
    MonObj (condensedRingObj (Profinite.continuousMapRingObj E.1) X) := inferInstance

/-- Its reconstructed commutative section-ring sheaf, without changing coefficients.
Source: Bhatt--Scholze 6.8.14(2); Stacks 00YV
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
def ring := ModuleObjectRingedComparison.ring (Profinite.padicIntegersRingObj l E.1) X

/-- The actual inclusion of integral into rational coefficients, on section rings.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
def coefficientMap : ring l E X ⟶
    ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X :=
  sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
  (padicIntegersToPadicSubfield.{u} X l E)

/-- The fixed exact equivalence on ordinary derived categories.
Source: Stacks 00YV, 05RU; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev forward := ModuleObjectRingedComparison.forward (Profinite.padicIntegersRingObj l E.1) X


/-- The existing locally-bijective description of sheafification equivalences.
Source: Stacks 00W1; the small-site sheafification instance
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable instance locallyBijective :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u+1, u+1, u+2, u+1, u+1, u+1}
    (Scheme.ProEt.topology X) (A := AddCommGrpCat.{u + 1})

/-- The canonical small derived categories, supplied uniformly for the scalar models.
Source: Stacks 07A5; the existing section-module Grothendieck instance
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable instance derivedCategories :
    ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 1, u + 1, u + 2}
        (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R) :=
  fun R ↦ HasDerivedCategory.ofIsGrothendieckAbelian
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R)

/-- Repeated multiplication by ell, formed in complexes of sheaf modules.
Source: Bhatt--Scholze 6.8.12--6.8.14, scalar telescope extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
def tower (A : CochainComplex
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ) :
    ℕ ⥤ CochainComplex (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ :=
  Functor.ofSequence (X := fun _ : ℕ ↦ A) (fun _ ↦ l • 𝟙 A)

/-- The canonical colimit of each scalar tower, named to share its instance term.
Source: Stacks 07A5; termwise colimits of complexes of sheaf modules.
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable local instance towerHasColimit (P : CochainComplex
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ) :
    HasColimit (tower l E X P) := inferInstance

variable (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))

attribute [local irreducible] sectionModuleEquivalence localizationHomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The nth localization leg: unit followed by inverse multiplication by ell^n.
Its pairing with K is ell^(-n) times scalar-extended evaluation.
Source: Bhatt--Scholze 6.8.14(2), telescope-stage normalization
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
def leg (A : DerivedCategory
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X))) (n : ℕ)
    (h : IsIso ((l ^ n) • 𝟙 ((M.scalar (coefficientMap l E X)).derived.obj A))) :
    A ⟶ (scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} (coefficientMap l E X)).obj
      ((M.scalar (coefficientMap l E X)).derived.obj A) :=
  letI := h
  (M.scalar (coefficientMap l E X)).adjunction.unit.app A ≫
    (scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} (coefficientMap l E X)).map
      (inv ((l ^ n) • 𝟙 ((M.scalar (coefficientMap l E X)).derived.obj A)))

/-- The recorded ambient derived internal Hom on the sectionwise presentation.
Source: Stacks 08J9; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev hom := derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
  (Scheme.ProEt.topology X) (ring l E X)

/-- Ordinary derived scalar extension along the actual integral inclusion.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev extension := (M.scalar (coefficientMap l E X)).derived

/-- Ordinary exact derived restriction along the integral inclusion.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev restriction := scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
  (coefficientMap l E X)

variable
  (μ : ∀ {A B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (b : A ⟶ B),
    ScalarHomTensorComparison.{u + 1, u, u, u + 1} M b)
  (α : ScalarInternalHomAdjunction.{u + 1, u, u, u + 1} M μ)

/-- The canonical evaluation-transpose comparison, using the dependency's normalized map.
Source: Bhatt--Scholze 6.8.14(2), internal-sheaf extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev comparison := localizationHomComparison.{u + 1, u, u, u + 1}
  M (coefficientMap l E X) (μ (coefficientMap l E X))

/-- Restriction followed by the evaluation-normalized scalar internal-Hom adjunction.
Source: Bhatt--Scholze 6.8.14(2), internal-sheaf extraction
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev restrictedComparison := localizationHomRestrictedComparison.{u + 1, u, u, u + 1}
  M (coefficientMap l E X) μ α

/-- The integral module derived category, in its sectionwise sheaf presentation.
Source: Stacks 00YV, 05RU; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev D := DerivedCategory (scalarModules.{u + 1, u, u + 1}
  (Scheme.ProEt.topology X) (ring l E X))

/-- The exact inverse to the recorded internal-to-sectionwise equivalence.
Source: Stacks 00YV, 05RU
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
abbrev internal :=
  (ModuleObjectRingedComparison.equivalence (Profinite.padicIntegersRingObj l E.1) X).inverse
    |>.mapDerivedCategory

/-- The canonical category structure on the integral derived category.
Source: Stacks 05RU; the existing localization category structure.
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable local instance integralDerivedCategory : Category.{u + 1} (D l E X) :=
  inferInstance

/-- The canonical additive structure on the integral derived category.
Source: Stacks 05RU; additivity of the localization of complexes.
(blueprint: lem-sfb-integral-general-lfp-hom-inversion). -/
noncomputable local instance integralDerivedPreadditive : Preadditive (D l E X) :=
  inferInstance

attribute [local irreducible] localizationHomComparison localizationHomRestrictedComparison
  CoefficientClosedStructure.tensor CoefficientClosedStructure.evaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency true in
private theorem unit_on_representative
    {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    {P T C : A} (e : P ≅ T) (b : C ≅ U.obj (F.obj P)) (j : P ⟶ C)
    (h : j ≫ b.hom = adj.unit.app P) :
    j ≫ (b ≪≫ (F ⋙ U).mapIso e).hom = e.hom ≫ adj.unit.app T := by
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, CategoryTheory.Functor.comp_map]
  rw [← CategoryTheory.Category.assoc, h]
  exact (adj.unit.naturality e.hom).symm

private theorem leg_zero (T : D l E X) :
    leg l E X M T 0 (by simpa using (inferInstance : IsIso (𝟙 _))) =
      (M.scalar (coefficientMap l E X)).adjunction.unit.app T := by
  dsimp only [leg]
  simp only [pow_zero, one_nsmul, IsIso.inv_id, CategoryTheory.Functor.map_id]
  exact CategoryTheory.Category.comp_id _

private theorem scalar_data :
    (∀ N : DerivedCategory (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X)),
      IsIso (l • 𝟙 N)) ∧
    (restriction l E X).Full ∧
    ∃ β : ∀ P : CochainComplex
        (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ,
      DerivedCategory.Q.obj (colimit (tower l E X P)) ≅
        (restriction l E X).obj ((extension l E X M).obj (DerivedCategory.Q.obj P)),
      ∀ P, DerivedCategory.Q.map (colimit.ι (tower l E X P) 0) ≫ (β P).hom =
        (M.scalar (coefficientMap l E X)).adjunction.unit.app (DerivedCategory.Q.obj P) :=
  integralSectionScalarTelescope l E X (M.scalar (coefficientMap l E X))

attribute [local instance 2000] hasSmallestColimitsOfHasColimits
  Limits.instHasColimitOfHasColimitsOfShape
attribute [local irreducible] coefficientMap scalarDerivedRestriction
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false in
private theorem rational_derived_iso
    (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
    (N : DerivedCategory (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X))) :
    IsIso (l • 𝟙 N) :=
  (scalar_data l E X M).1 N

private theorem mapped_nat_iso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (t : ℕ) (P : A) [IsIso (t • 𝟙 P)] :
    IsIso (t • 𝟙 (F.obj P)) := by
  simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using
    F.map_isIso (t • 𝟙 P)

private theorem scalar_sequence_nat
    {B : Type*} [Category B] [Preadditive B] {P Q : B}
    (t : ℕ) [Mono (t • 𝟙 Q)] (f g : ℕ → (P ⟶ Q))
    (hf : ∀ n, (t • 𝟙 P) ≫ f (n + 1) = f n)
    (hg : ∀ n, (t • 𝟙 P) ≫ g (n + 1) = g n)
    (hzero : f 0 = g 0) : ∀ n, f n = g n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    apply (cancel_mono (t • 𝟙 Q)).mp
    calc
      _ = (t • 𝟙 P) ≫ f (n + 1) := by simp only
        [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
          CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]
      _ = f n := hf n
      _ = g n := ih
      _ = (t • 𝟙 P) ≫ g (n + 1) := (hg n).symm
      _ = _ := by simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
        CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

private theorem scalar_sequence_functor
    {A : Type*} [Category A] [Preadditive A]
    (H : A ⥤ A) [H.Additive] (t : ℕ) {P Q R : A}
    [Mono (t • 𝟙 (H.obj Q))]
    (v : ℕ → (P ⟶ Q)) (w : ℕ → (H.obj P ⟶ R))
    (ρ : R ⟶ H.obj Q)
    (hv : ∀ n, (t • 𝟙 P) ≫ v (n + 1) = v n)
    (hw : ∀ n, (t • 𝟙 (H.obj P)) ≫ w (n + 1) = w n)
    (hzero : w 0 ≫ ρ = H.map (v 0)) :
    ∀ n, w n ≫ ρ = H.map (v n) := by
  apply scalar_sequence_nat t (fun n ↦ w n ≫ ρ) (fun n ↦ H.map (v n))
  · intro n
    exact (CategoryTheory.Category.assoc _ _ _).symm.trans
      (congrArg (fun f ↦ f ≫ ρ) (hw n))
  · intro n
    have hh := congrArg H.map (hv n)
    rw [H.map_comp, H.map_nsmul, H.map_id] at hh
    exact hh
  · exact hzero

private theorem scalar_power_iso
    {A : Type*} [Category A] [Preadditive A] (t : ℕ) (N : A)
    [IsIso (t • 𝟙 N)] (n : ℕ) : IsIso ((t ^ n) • 𝟙 N) := by
  induction n with
  | zero => simpa only [pow_zero, one_nsmul] using (inferInstance : IsIso (𝟙 N))
  | succ n ih =>
    have he : (t ^ (n + 1)) • 𝟙 N = (t ^ n • 𝟙 N) ≫ (t • 𝟙 N) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        CategoryTheory.Category.id_comp, pow_succ, mul_smul]
      exact smul_comm _ _ _
    rw [he]
    infer_instance

private theorem derived_power_iso (T : D l E X) (n : ℕ) :
    IsIso ((l ^ n) • 𝟙 ((extension l E X M).obj T)) := by
  have := rational_derived_iso l E X M ((extension l E X M).obj T)
  exact scalar_power_iso l _ n

private theorem abstract_leg_step
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (t : ℕ) (F : A ⥤ B) (U : B ⥤ A) [U.Additive]
    (η : 𝟭 A ⟶ F ⋙ U) (T : A) (n : ℕ)
    [IsIso (t • 𝟙 (F.obj T))] [IsIso ((t ^ n) • 𝟙 (F.obj T))]
    [IsIso ((t ^ (n + 1)) • 𝟙 (F.obj T))] :
    (t • 𝟙 T) ≫ (η.app T ≫ U.map (inv ((t ^ (n + 1)) • 𝟙 (F.obj T)))) =
      η.app T ≫ U.map (inv ((t ^ n) • 𝟙 (F.obj T))) := by
  have he : ((t ^ (n + 1)) • 𝟙 (F.obj T)) =
      (t • 𝟙 (F.obj T)) ≫ ((t ^ n) • 𝟙 (F.obj T)) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      CategoryTheory.Category.id_comp, pow_succ, mul_smul]
  have hi : (t • 𝟙 (F.obj T)) ≫ inv ((t ^ (n + 1)) • 𝟙 (F.obj T)) =
      inv ((t ^ n) • 𝟙 (F.obj T)) := by
    apply (cancel_mono ((t ^ n) • 𝟙 (F.obj T))).mp
    have hc : inv ((t ^ (n + 1)) • 𝟙 (F.obj T)) ≫ ((t ^ n) • 𝟙 (F.obj T)) =
        ((t ^ n) • 𝟙 (F.obj T)) ≫ inv ((t ^ (n + 1)) • 𝟙 (F.obj T)) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]
    rw [CategoryTheory.Category.assoc, hc, ← CategoryTheory.Category.assoc, ← he,
      IsIso.hom_inv_id, IsIso.inv_hom_id]
  have hw : (t • 𝟙 T) ≫ η.app T = η.app T ≫ U.map (t • 𝟙 (F.obj T)) := by
    simp
  rw [← CategoryTheory.Category.assoc, hw, CategoryTheory.Category.assoc, ← U.map_comp, hi]

private theorem leg_step (T : D l E X) (n : ℕ) :
    (l • 𝟙 T) ≫ leg l E X M T (n + 1) (derived_power_iso l E X M T (n + 1)) =
      leg l E X M T n (derived_power_iso l E X M T n) := by
  have := rational_derived_iso l E X M ((extension l E X M).obj T)
  have := derived_power_iso l E X M T n
  have := derived_power_iso l E X M T (n + 1)
  have : (restriction l E X).IsRightAdjoint :=
    (M.scalar (coefficientMap l E X)).adjunction.isRightAdjoint
  have : (restriction l E X).Additive :=
    (restriction l E X).additive_of_preserves_binary_products
  exact abstract_leg_step l (extension l E X M) (restriction l E X)
    (M.scalar (coefficientMap l E X)).adjunction.unit T n

attribute [local irreducible] leg DerivedCategory.Q
  localizationHomResolutionIso

private theorem telescope_presentation
    {B C : Type*} [Category B] [Category C] [Preadditive B]
    (t : ℕ) (P C0 : B) (j : ℕ → (P ⟶ C0))
    (hj : ∀ n, (t • 𝟙 P) ≫ j (n + 1) = j n)
    (F : B ⥤ C) (U : C ⥤ B) (adj : F ⊣ U)
    (b0 : C0 ≅ U.obj (F.obj P)) (hb0 : j 0 ≫ b0.hom = adj.unit.app P)
    (T : B) (e : P ≅ T) (v : ℕ → (T ⟶ U.obj (F.obj T)))
    [Mono (t • 𝟙 (U.obj (F.obj T)))]
    (hzero : v 0 = adj.unit.app T)
    (hstep : ∀ n, (t • 𝟙 T) ≫ v (n + 1) = v n) :
    ∃ b : C0 ≅ U.obj (F.obj T), ∀ n, j n ≫ b.hom = e.hom ≫ v n := by
  let b : C0 ≅ U.obj (F.obj T) := b0 ≪≫ U.mapIso (F.mapIso e)
  have hf (n : ℕ) : (t • 𝟙 P) ≫ (j (n + 1) ≫ b.hom) = j n ≫ b.hom :=
    (CategoryTheory.Category.assoc _ _ _).symm.trans
      (congrArg (fun f ↦ f ≫ b.hom) (hj n))
  have hg (n : ℕ) : (t • 𝟙 P) ≫ (e.hom ≫ v (n + 1)) = e.hom ≫ v n := by
    calc
      _ = e.hom ≫ ((t • 𝟙 T) ≫ v (n + 1)) := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          CategoryTheory.Category.id_comp]
      _ = _ := congrArg (fun f ↦ e.hom ≫ f) (hstep n)
  have hz : j 0 ≫ b.hom = e.hom ≫ v 0 := by
    rw [hzero]
    exact unit_on_representative adj e b0 _ hb0
  have hh := @scalar_sequence_nat B inferInstance inferInstance P (U.obj (F.obj T))
    t inferInstance (fun n ↦ j n ≫ b.hom) (fun n ↦ e.hom ≫ v n) hf hg hz
  exact Exists.intro b hh

private theorem mapped_colimit_step
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (Q : A ⥤ B) [Q.Additive] (t : ℕ) (P : A)
    [HasColimit (Functor.ofSequence (fun _ : ℕ ↦ t • 𝟙 P))] (n : ℕ) :
    (t • 𝟙 (Q.obj P)) ≫
      Q.map (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ t • 𝟙 P)) (n + 1)) =
      Q.map (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ t • 𝟙 P)) n) := by
  have hw := congrArg Q.map
    (colimit.w (Functor.ofSequence (fun _ : ℕ ↦ t • 𝟙 P))
      (homOfLE (Nat.le_succ n)))
  rw [Functor.ofSequence_map_homOfLE_succ] at hw
  erw [Q.map_comp, Q.map_nsmul, Q.map_id] at hw
  exact hw

set_option maxHeartbeats 60000 in
-- The normalized derived scalar and closed structures require larger instance searches.
private theorem presentation
    (T : D l E X)
    (P : CochainComplex
      (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ T) :
    ∃ b : DerivedCategory.Q.obj (colimit (tower l E X P)) ≅
        (restriction l E X).obj ((extension l E X M).obj T),
      ∀ n, DerivedCategory.Q.map (colimit.ι (tower l E X P) n) ≫ b.hom =
        e.hom ≫ leg l E X M T n (derived_power_iso l E X M T n) := by
  classical
  have := rational_derived_iso l E X M ((extension l E X M).obj T)
  have : (restriction l E X).IsRightAdjoint :=
    (M.scalar (coefficientMap l E X)).adjunction.isRightAdjoint
  have : (restriction l E X).Additive :=
    (restriction l E X).additive_of_preserves_binary_products
  have := mapped_nat_iso (restriction l E X) l ((extension l E X M).obj T)
  exact telescope_presentation l (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj (colimit (tower l E X P)))
    (fun n ↦ DerivedCategory.Q.map (colimit.ι (tower l E X P) n))
    (mapped_colimit_step DerivedCategory.Q l P) (extension l E X M)
    (restriction l E X) (M.scalar (coefficientMap l E X)).adjunction
    ((scalar_data l E X M).2.2.choose P) ((scalar_data l E X M).2.2.choose_spec P) T e
    (fun n ↦ leg l E X M T n (derived_power_iso l E X M T n))
    (leg_zero l E X M T) (leg_step l E X M T)

set_option backward.defeqAttrib.useBackward true in
private theorem restricted_iso
    [CompactSpace X] [IsLocallyNoetherian X] (K L : D l E X)
    (hK : boundedConstructible (integral l E X) ((internal l E X).obj K))
    (hL : ∃ c : ℤ, L.IsGE c) : IsIso (restrictedComparison l E X M μ α K L) := by
  classical
  let J := Scheme.ProEt.topology X
  let R := ring l E X
  let a := coefficientMap l E X
  have : IsGrothendieckAbelian.{u + 1}
      (scalarModules.{u + 1, u, u + 1} J R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
      J R).1
  have : HasColimitsOfSize.{0, 0} (scalarModules.{u + 1, u, u + 1} J R) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  let F := extension l E X M
  let U := restriction l E X
  let H := hom l E X
  let H' := derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} J
    (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X)
  have : U.Full := (scalar_data l E X M).2.1
  let β := (scalar_data l E X M).2.2.choose
  have hβ := (scalar_data l E X M).2.2.choose_spec
  have hK := integralSectionHomContinuity l E X K hK
  let HK := Prod.sectR (op K) (D l E X) ⋙ H
  have : HK.IsRightAdjoint := (M.closed R).adjunction K |>.isRightAdjoint
  have : HK.Additive := Functor.additive_of_preserves_binary_products HK
  let G := localizationHomComplex.{u + 1, u, u, u + 1} J R K
  let eG : G ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ HK :=
    NatIso.ofComponents (fun P ↦ localizationHomResolutionIso R K P)
      (fun f ↦ localizationHomResolutionIso_naturality R K f)
  have : AB5OfSize.{0, 0} (scalarModules.{u + 1, u, u + 1} J R) :=
    AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
  exact scalarTelescope_normalized_comparison_isIso F U (M.scalar a).adjunction
    l G HK eG β hβ (fun P c hP ↦ hK _ ⟨c, fun _ ↦ hP⟩) L hL
    (H'.obj (op (F.obj K), F.obj L))
    ((α.iso a).app (op K, F.obj L)).symm
    (restrictedComparison l E X M μ α K L)
    (localizationHom_unit M a μ α K L)

private theorem leg_comparison (K L : D l E X) (n : ℕ) :
    leg l E X M ((hom l E X).obj (op K, L)) n (derived_power_iso l E X M _ n) ≫
      restrictedComparison l E X M μ α K L =
        (hom l E X).map (Prod.mkHom (𝟙 (op K))
          (leg l E X M L n (derived_power_iso l E X M L n))) := by
  let F := (Functor.curry.obj (hom l E X)).obj (op K)
  have : F.IsRightAdjoint := (M.closed (ring l E X)).adjunction K |>.isRightAdjoint
  have : F.Additive := F.additive_of_preserves_binary_products
  have : IsIso (l • 𝟙 ((restriction l E X).obj ((extension l E X M).obj L))) := by
    have := rational_derived_iso l E X M ((extension l E X M).obj L)
    have : (restriction l E X).IsRightAdjoint :=
      (M.scalar (coefficientMap l E X)).adjunction.isRightAdjoint
    have : (restriction l E X).Additive :=
      (restriction l E X).additive_of_preserves_binary_products
    exact mapped_nat_iso (restriction l E X) l ((extension l E X M).obj _)
  have : IsIso (l • 𝟙 (F.obj ((restriction l E X).obj ((extension l E X M).obj L)))) := by
    exact mapped_nat_iso F l _
  have hm : Mono (l • 𝟙 ((hom l E X).obj
      (op K, (restriction l E X).obj ((extension l E X M).obj L)))) := by
    simpa only [F, CategoryTheory.Functor.curry_obj_obj_obj] using
      (inferInstance : Mono (l • 𝟙 (F.obj
        ((restriction l E X).obj ((extension l E X M).obj L)))))
  apply scalar_sequence_functor F l
    (fun n ↦ leg l E X M L n (derived_power_iso l E X M L n))
    (fun n ↦ leg l E X M (F.obj L) n (derived_power_iso l E X M _ n))
    (restrictedComparison l E X M μ α K L)
    (leg_step l E X M L) (leg_step l E X M (F.obj L)) ?_ n
  exact (congrArg (fun f ↦ f ≫ restrictedComparison l E X M μ α K L)
    (leg_zero l E X M (F.obj L))).trans
      ((localizationHom_unit M (coefficientMap l E X) μ α K L).trans
        (congrArg F.map (leg_zero l E X M L).symm))

private theorem comparison_naturality (K L K' L' : D l E X)
    (f : K' ⟶ K) (g : L ⟶ L') :
    (extension l E X M).map ((hom l E X).map (Prod.mkHom f.op g)) ≫
      comparison l E X M μ K' L' = comparison l E X M μ K L ≫
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X)
        (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X)).map
          (Prod.mkHom ((extension l E X M).map f).op ((extension l E X M).map g)) := by
  simpa only [comparison, localizationHomComparison, LocalizationHomProof.closedComparison]
    using LocalizationHomProof.closedComparison_naturality
      (M.closed (ring l E X))
      (M.closed (ModuleObjectRingedComparison.ring
        (Profinite.continuousMapRingObj E.1) X))
      (extension l E X M) (μ (coefficientMap l E X)).iso K L K' L' f g

private theorem representative_leg
    {B : Type*} [Category B] (F : B ⥤ B)
    {P Q X Y L UH UL : B} (bH : X ≅ UH) (bL : Y ≅ UL)
    (eH : P ≅ F.obj L) (eL : Q ≅ L) (rho : UH ⟶ F.obj UL)
    (lH : F.obj L ⟶ UH) (lL : L ⟶ UL) (jH : P ⟶ X) (jL : Q ⟶ Y)
    (hH : jH ≫ bH.hom = eH.hom ≫ lH) (hL : jL ≫ bL.hom = eL.hom ≫ lL)
    (hc : lH ≫ rho = F.map lL) :
    jH ≫ (bH.hom ≫ rho ≫ F.map bL.inv) = eH.hom ≫ F.map (eL.inv ≫ jL) := by
  calc
    _ = (jH ≫ bH.hom) ≫ rho ≫ F.map bL.inv := by simp only [CategoryTheory.Category.assoc]
    _ = eH.hom ≫ (lH ≫ rho) ≫ F.map bL.inv := by
      rw [hH]
      simp only [CategoryTheory.Category.assoc]
    _ = eH.hom ≫ F.map (lL ≫ bL.inv) := by
      rw [hc, F.map_comp]
    _ = _ := by
      apply congrArg (fun k ↦ eH.hom ≫ F.map k)
      apply (cancel_mono bL.hom).mp
      simp only [CategoryTheory.Category.assoc, Iso.inv_hom_id, CategoryTheory.Category.comp_id]
      rw [hL, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_naturality
    {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (K : B) {X Y : B} (f : X ⟶ Y) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K)) f)) (𝟙 K)) ≫
      S.evaluation K Y = S.evaluation K X ≫ f := by
  letI := S.monoidal
  unfold CoefficientClosedStructure.tensor CoefficientClosedStructure.evaluation
  simpa only [Functor.comp_map, Functor.id_map, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorRight, Functor.flip_obj_map,
    MonoidalCategory.curriedTensor_map_app, CoefficientClosedStructure.evaluation,
    Prod.sectR_map] using
      (S.adjunction K).counit.naturality f

private theorem representative_comparison
    {B : Type*} [Category B] (F : B ⥤ B)
    {P Q X Y L UH UL : B} (bH : X ≅ UH) (bL : Y ≅ UL)
    (eH : P ≅ F.obj L) (eL : Q ≅ L) (ρ : UH ⟶ F.obj UL) [IsIso ρ]
    (vH : ℕ → (F.obj L ⟶ UH)) (vL : ℕ → (L ⟶ UL))
    (jH : ℕ → (P ⟶ X)) (jL : ℕ → (Q ⟶ Y))
    (hH : ∀ n, jH n ≫ bH.hom = eH.hom ≫ vH n)
    (hL : ∀ n, jL n ≫ bL.hom = eL.hom ≫ vL n)
    (hc : ∀ n, vH n ≫ ρ = F.map (vL n)) :
    ∃ γ : X ≅ F.obj Y, γ.hom ≫ F.map bL.hom = bH.hom ≫ ρ ∧
      ∀ n, jH n ≫ γ.hom = eH.hom ≫ F.map (eL.inv ≫ jL n) := by
  let γ := bH ≪≫ asIso ρ ≪≫ F.mapIso bL.symm
  refine ⟨γ, ?_, ?_⟩
  · change (bH.hom ≫ ρ ≫ F.map bL.inv) ≫ F.map bL.hom = _
    rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
      ← F.map_comp, Iso.inv_hom_id, F.map_id, CategoryTheory.Category.comp_id]
  · intro n
    exact representative_leg F bH bL eH eL ρ (vH n) (vL n) (jH n) (jL n)
      (hH n) (hL n) (hc n)

private theorem pairing_from_leg
    {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (K L U V : B)
    (v : H.obj (op K, L) ⟶ V) (ρ : V ⟶ H.obj (op K, U)) (w : L ⟶ U)
    (hv : v ≫ ρ = H.map (Prod.mkHom (𝟙 (op K)) w)) :
    S.tensor.map (Prod.mkHom (v ≫ ρ) (𝟙 K)) ≫ S.evaluation K U =
      S.evaluation K L ≫ w := by
  rw [hv]
  exact evaluation_naturality S K w

/-- Scalar inversion for general-lfp bounded constructible first inputs, with an arbitrary
bounded-below second input. All scalar and closed models are the already normalized ones.
The existential inverse-scalar proofs only make the explicit nth-leg notation typeable;
they are conclusions, not extra hypotheses. The two beta maps identify termwise scalar
colimits with restricted localization, and gamma is the evaluation-induced comparison.
Its square with beta identifies the actual restricted comparison on every representative.
The final equation is the categorical pairing formula
`(h,k) ↦ ell^(-n) (1 tensor h(k))`, for every n including zero.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
with the internal-sheaf extraction and coefficient-specific general-lfp bridge
(blueprint: lem-sfb-integral-general-lfp-hom-inversion).

Proof:
1. The locally Noetherian, quasi-compact scheme has Noetherian underlying topology by
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal: a minimal member of the set of
members of a descending closed chain forces that chain to stabilize.
2. Apply lem-sfb-integral-lfp-constant-model-comparison to each of the finitely many
nonzero cohomology modules of K. Arbitrary local presentation matrices are permitted.
It gives finite constant models, including torsion models, without completeness.
3. On the small pro-etale site, filtered module colimits are exact by
lem-pur-ringed-site-grothendieck-abelian. Apply
lem-sfb-constructible-internal-hom-continuity to the repeated-ell tower, after the
existing evaluation-preserving module-object/ringed-site equivalence. This supplies
the sequential-continuity hypothesis of lem-sfb-internal-hom-localization-comparison.
4. If L has cohomology zero below c, replace any representative C by its lower
truncation: zero below c, coker(d^(c-1)) in degree c, and C above c. The quotient is a
quasi-isomorphism, and its scalar tower has a common termwise lower bound.
5. sk-prop-sfb-qlbar-colimit-x identifies the actual rational coefficient inclusion
with inversion of ell. Apply lem-sfb-internal-hom-localization-comparison to obtain
invertibility of the evaluation transpose, its restriction, and two-variable naturality.
6. lem-sfb-derived-scalar-localization-reflection and
lem-weil-pbc-scalar-localization-complex-colimit identify the two scalar telescopes
with restricted localization, with nth leg ell^(-n) times the unit.
lem-sfb-kinjective-hom-scalar-telescope replaces the functorial-resolution transition
by the literal scalar transition, preserving every derived colimit leg. Exact
colimits preserve quasi-isomorphisms, so arbitrary representatives A and P are allowed,
with no lower bound on the Hom representative A.
7. The evaluation normalization of lem-sfb-dc-hom-scalar-adjunction identifies the
restricted target with Hom(K,U(L_E)). On stage n scalar linearity gives the last
pairing equation; ell^(-(n+1)) times ell agrees with ell^(-n), so these are a cocone.
The beta square and stage equations identify gamma with the canonical continuity map,
independently of representatives. No completed category is used. -/
theorem integralGeneralLfpHomInversion
    [CompactSpace X] [IsLocallyNoetherian X]
    (K L : D l E X)
    (_hK : boundedConstructible (integral l E X)
      ((internal l E X).obj K))
    (_hL : ∃ c : ℤ, L.IsGE c) :
    IsIso (comparison l E X M μ K L) ∧
    IsIso (restrictedComparison l E X M μ α K L) ∧
    (∀ (K' L' : D l E X) (f : K' ⟶ K) (g : L ⟶ L'),
      (extension l E X M).map ((hom l E X).map (Prod.mkHom f.op g)) ≫
          comparison l E X M μ K' L' =
        comparison l E X M μ K L ≫
          (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
            (Scheme.ProEt.topology X)
            (ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E.1) X)).map
              (Prod.mkHom ((extension l E X M).map f).op ((extension l E X M).map g))) ∧
    ∃ h : ∀ (T : D l E X) (n : ℕ),
        IsIso ((l ^ n) • 𝟙 ((extension l E X M).obj T)),
      (∀ (A P : CochainComplex
          (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (ring l E X)) ℤ)
        (eA : DerivedCategory.Q.obj A ≅ (hom l E X).obj (op K, L))
        (eP : DerivedCategory.Q.obj P ≅ L),
        ∃ (βA : DerivedCategory.Q.obj (colimit (tower l E X A)) ≅
            (restriction l E X).obj
              ((extension l E X M).obj ((hom l E X).obj (op K, L))))
          (βP : DerivedCategory.Q.obj (colimit (tower l E X P)) ≅
            (restriction l E X).obj ((extension l E X M).obj L)),
          (∀ n : ℕ, DerivedCategory.Q.map (colimit.ι (tower l E X A) n) ≫ βA.hom =
            eA.hom ≫ leg l E X M ((hom l E X).obj (op K, L)) n (h _ n)) ∧
          (∀ n : ℕ, DerivedCategory.Q.map (colimit.ι (tower l E X P) n) ≫ βP.hom =
            eP.hom ≫ leg l E X M L n (h _ n)) ∧
          ∃ γ : DerivedCategory.Q.obj (colimit (tower l E X A)) ≅
              (hom l E X).obj (op K, DerivedCategory.Q.obj (colimit (tower l E X P))),
            γ.hom ≫ (hom l E X).map (Prod.mkHom (𝟙 (op K)) βP.hom) =
              βA.hom ≫ restrictedComparison l E X M μ α K L ∧
            ∀ n : ℕ, DerivedCategory.Q.map (colimit.ι (tower l E X A) n) ≫ γ.hom =
              eA.hom ≫ (hom l E X).map
                (Prod.mkHom (𝟙 (op K))
                  (eP.inv ≫ DerivedCategory.Q.map (colimit.ι (tower l E X P) n)))) ∧
      ∀ n : ℕ,
        (M.closed (ring l E X)).tensor.map
            (Prod.mkHom
              (leg l E X M ((hom l E X).obj (op K, L)) n (h _ n) ≫
                restrictedComparison l E X M μ α K L) (𝟙 K)) ≫
          (M.closed (ring l E X)).evaluation K
            ((restriction l E X).obj ((extension l E X M).obj L)) =
        (M.closed (ring l E X)).evaluation K L ≫ leg l E X M L n (h _ n) := by
  have h := derived_power_iso l E X M
  have hr := restricted_iso l E X M μ α K L _hK _hL
  refine ⟨?_, ?_, ?_, h, ?_, ?_⟩
  · exact localizationHom_isIso_of_restricted M (coefficientMap l E X) μ α K L hr
  · exact hr
  · intro K' L' f g
    exact comparison_naturality l E X M μ K L K' L' f g
  · intro A P eA eP
    have pA := presentation l E X M ((hom l E X).obj (op K, L)) A eA
    have pP := presentation l E X M L P eP
    let βA := pA.choose
    let βP := pP.choose
    have hβA := pA.choose_spec
    have hβP := pP.choose_spec
    have := hr
    let F := (Functor.curry.obj (hom l E X)).obj (op K)
    refine ⟨βA, βP, hβA, hβP, ?_⟩
    exact representative_comparison F βA βP eA eP
      (restrictedComparison l E X M μ α K L)
      (fun n ↦ leg l E X M ((hom l E X).obj (op K, L)) n (h _ n)) (fun n ↦ leg l E X M L n (h L n))
      (fun n ↦ DerivedCategory.Q.map (colimit.ι (tower l E X A) n))
      (fun n ↦ DerivedCategory.Q.map (colimit.ι (tower l E X P) n))
      hβA hβP (leg_comparison l E X M μ α K L)
  · intro n
    exact pairing_from_leg (M.closed (ring l E X)) K L
      ((restriction l E X).obj ((extension l E X M).obj L))
      ((restriction l E X).obj ((extension l E X M).obj ((hom l E X).obj (op K, L))))
      (leg l E X M ((hom l E X).obj (op K, L)) n (h _ n))
      (restrictedComparison l E X M μ α K L) (leg l E X M L n (h L n))
      (leg_comparison l E X M μ α K L n)

end AlgebraicGeometry.ProEtale.IntegralHomInversion
