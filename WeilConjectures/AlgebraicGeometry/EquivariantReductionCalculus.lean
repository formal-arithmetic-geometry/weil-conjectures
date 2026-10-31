/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.InverseImageScalarRestrictionComparison
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Equivariant derived scalar extension and simultaneous integral reduction

Source: latest blueprint, `sk-prop-diagonal-tower-system.proof.md`, (2)--(4)
(blueprint: lem-pur-equivariant-reduction-calculus).

## Main definitions

- `Action.EqMod`: actual semilinear modules before localization.
- `ScalarModel`: the tensor/restriction universal pair and its resolving computations.
- `IntegralReductionModel`: the single strict reduction tower and its derived evaluations.
- `KummerModel`: the whole-system identification with positive-unit normalization.

## Main statements

- `scalarModel_nonempty` and the normalized scalar comparison existence theorems.
- `integralReductionModel_nonempty` and its forgetting and pullback comparisons.
- `kummerModel_nonempty`, `kummer_adjunct`, `kummer_forgetting`, and `kummer_pullback`.

## Node proof steps and their statements

1. `Action.additive`, `Action.isEquivalence`, `Action.isKFlat_iff_equivariantAcyclicTest`,
   and `equivariantKFlatResolution` state the actual equivariant resolving construction.
2. `scalarModel_nonempty`, `scalar_preservesQuasiIso`, and
   `scalarForgettingComparison_nonempty` state scalar derivation, its unit and forgetting.
3. `unitComparison_nonempty` and `compositionComparison_nonempty` fix the scalar constraints.
4. `InverseImage.properties`, `derivedRingedPullback_properties`, and
   `scalarPullbackComparison_nonempty` state equivariant ringed inverse-image compatibility.
5. `reductionModel_nonempty` constructs the one strict system and its left derivation.
6. `integralReductionModel_nonempty`, `reductionCompositionComparison_nonempty`,
   `reductionForgetting_nonempty`, and `reductionPullbackComparison_nonempty` fix its
   evaluations, transitions and comparisons.
7. `constantReduction_nonempty` computes the regular integral source and its unit.
8. `kummerPresentation_nonempty` states exactness and the natural power-transition tower.
9. `kummerModel_nonempty` computes the reductions by the two-term coefficient resolutions.
10. `KummerModel.positive` and `kummerModel_nonempty` fix the positive connecting-map sign.
11. `KummerModel.iso`, `KummerModel.evaluation`, and `kummerModel_nonempty` state the
    truncation identification in the derived category of the entire tower category.
12. `kummer_adjunct`, `kummer_forgetting`, and `kummer_pullback` state arbitrary-arrow
    adjuncts and the whole-system forgetting and pullback equations.
Fixed pairs are formed before localization. Ordinary scalar extension, its pure
sections, and K-flatness are the existing ringed-site constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor

namespace SheafOfModules.EquivariantReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}

/-- The coefficient ring and its specified algebraic lift of the topos automorphism.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure Action (σ : Sheaf J (Type r) ≌ Sheaf J (Type r)) where
  ring : Sheaf J CommRingCat.{r}
  lift : AlgebraicInverseImage σ.functor ring ring

variable {σ : Sheaf J (Type r) ≌ Sheaf J (Type r)}

/-- The existing ordinary category of module sheaves for these coefficients.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Action.Mod (A : Action σ) :=
  SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A.ring)

universe uD vD

/-- The universal module-addition graph and naturality of the underlying-sheaf
comparison show that every algebraic inverse image preserves addition of maps.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus). -/
private theorem algebraicImage_additive
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
    {K : GrothendieckTopology D}
    {L : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
    {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
    (E : AlgebraicInverseImage L R S) : E.modules.Additive := by
  let V := toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  constructor
  intro M N f g
  ext U z
  have eval (k : M ⟶ N) :
      (E.moduleUnderlying.inv.app N).hom.app U
          ((L.map (V.map k)).hom.app U
            ((E.moduleUnderlying.hom.app M).hom.app U z)) =
        (E.modules.map k).val.app U z := by
    have h := congrArg
      (fun q ↦ q.hom.app U ((E.moduleUnderlying.hom.app M).hom.app U z))
      (E.moduleUnderlying.inv.naturality k)
    change (E.moduleUnderlying.inv.app N).hom.app U
        ((L.map (V.map k)).hom.app U
          ((E.moduleUnderlying.hom.app M).hom.app U z)) =
      (E.modules.map k).val.app U
        ((E.moduleUnderlying.inv.app M).hom.app U
          ((E.moduleUnderlying.hom.app M).hom.app U z)) at h
    have hz : (E.moduleUnderlying.inv.app M).hom.app U
        ((E.moduleUnderlying.hom.app M).hom.app U z) = z :=
      congrArg (fun q ↦ q.hom.app U z) (E.moduleUnderlying.hom_inv_id_app M)
    rw [hz] at h
    exact h
  have h := E.moduleAdd N (V.obj M)
    (V.map f) (V.map g) (V.map (f + g))
    (fun _ _ ↦ rfl) U ((E.moduleUnderlying.hom.app M).hom.app U z)
  dsimp only [id] at h
  rw [eval (f + g), eval f, eval g] at h
  exact h

/-- Algebraic transport by a topos automorphism is additive.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the universal addition graph in moduleUnderlying turns moduleAdd into
preservation of addition of module maps; its naturality supplies the equality. -/
theorem Action.additive (A : Action σ) : A.lift.modules.Additive := by
  exact algebraicImage_additive A.lift

/-- Algebraic transport by a topos automorphism is an equivalence.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: transport ring and module operations through the inverse topos equivalence.
Its unit and counit preserve operation graphs, hence lift to inverse module functors. -/
theorem Action.isEquivalence (A : Action σ) : A.lift.modules.IsEquivalence := by
  sorry

attribute [instance] Action.additive Action.isEquivalence

/-- Actual semilinear modules, with invertible structure before passage to complexes.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Action.EqMod (A : Action σ) := IsoAlgebra A.lift.modules

/-- Exact forgetting is the recorded fixed-pair forgetful functor.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Action.forget (A : Action σ) := IsoAlgebra.forget A.lift.modules

/-- A coefficient map has the stated compatibility with the two ring identifications.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure Map (A B : Action σ) where
  hom : A.ring ⟶ B.ring
  comm : A.lift.ringUnderlying.hom ≫
      (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map hom =
    σ.functor.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map hom) ≫
      B.lift.ringUnderlying.hom

/-- Ordinary scalar restriction, using the existing functor.
Source: Stacks 03CY (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Map.restrict {A B : Action σ} (f : Map A B) : B.Mod ⥤ A.Mod :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map f.hom)

/-- The restriction commutator is uniquely specified by its underlying sheaf map.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the normalized inverse-image/scalar-restriction comparison ρ of
lem-pur-inverse-image-scalar-restriction-comparison, applied to the ring square of f,
satisfies V(ρ_M) ≫ A.moduleUnderlying = B.moduleUnderlying. Take e = ρ⁻¹; cancelling
the invertible underlying map V(ρ_M) gives the displayed equation. Uniqueness: two
such isomorphisms have equal underlying sheaf maps, and forgetting is faithful. -/
theorem Map.restrictComparison_existsUnique {A B : Action σ} (f : Map A B) :
    ∃! e : f.restrict ⋙ A.lift.modules ≅ B.lift.modules ⋙ f.restrict,
      ∀ M : B.Mod,
        (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})).map (e.hom.app M) =
          A.lift.moduleUnderlying.hom.app (f.restrict.obj M) ≫
            B.lift.moduleUnderlying.inv.app M := by
  obtain ⟨ρ, hρ⟩ := InverseImageScalarRestriction.exists_comparison
    A.lift B.lift f.hom f.hom f.comm.symm
  let V := toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A.ring) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  let e := ρ.symm
  have he (M : B.Mod) :
      V.map (e.hom.app M) =
        A.lift.moduleUnderlying.hom.app (f.restrict.obj M) ≫
          B.lift.moduleUnderlying.inv.app M := by
    change V.map (ρ.inv.app M) = _
    apply (cancel_epi (V.map (ρ.hom.app M))).1
    ext U x
    have h := congrArg (fun k ↦ k ≫ B.lift.moduleUnderlying.inv.app M) (hρ M)
    simp only [Iso.hom_inv_id_app] at h
    have hi := congrArg (fun k ↦ k.hom.app U x) (V.mapIso (ρ.app M)).hom_inv_id
    exact hi.trans (congrArg (fun k ↦ k.hom.app U x) h).symm
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply V.map_injective
  exact (he' M).trans (he M).symm

/-- The canonical commutator; the preceding theorem determines it uniquely.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus). -/
def Map.restrictComparison {A B : Action σ} (f : Map A B) :=
  (f.restrictComparison_existsUnique).exists.choose

/-- Restriction on actual semilinear modules.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Map.eqRestrict {A B : Action σ} (f : Map A B) : B.EqMod ⥤ A.EqMod :=
  IsoAlgebra.mapOfNatIso f.restrictComparison

/-- Exactness of semilinear scalar restriction.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: ordinary scalar restriction preserves finite limits and colimits, and the
existing fixed-pair instances lift this through `IsoAlgebra.mapOfNatIso` along the
invertible commutator; both conjuncts are found by instance search. -/
theorem Map.eqRestrict_exact {A B : Action σ} (f : Map A B) :
    PreservesFiniteLimits f.eqRestrict ∧ PreservesFiniteColimits f.eqRestrict := by
  constructor <;> infer_instance

/-- Scalar restriction preserves finite limits.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance Map.eqRestrict_limits {A B : Action σ} (f : Map A B) :
    PreservesFiniteLimits f.eqRestrict := f.eqRestrict_exact.1

/-- Scalar restriction preserves finite colimits.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance Map.eqRestrict_colimits {A B : Action σ} (f : Map A B) :
    PreservesFiniteColimits f.eqRestrict := f.eqRestrict_exact.2


/-- K-flatness on actual semilinear complexes, detected by their underlying complexes.
Source: blueprint (2), acyclic tensor test (blueprint: lem-pur-equivariant-reduction-calculus).
This uses the existing sheafified total tensor, including all acyclic test complexes. -/
def Action.IsKFlat (A : Action σ) (P : CochainComplex A.EqMod ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := A.ring)
    ((A.forget.mapHomologicalComplex (.up ℤ)).obj P)


/-- The full acyclic test using actual equivariant test complexes. Exact
conservative forgetting detects acyclicity of their semilinear tensor, so this
uses the existing ordinary sheafified total tensor without another tensor notion.
Source: blueprint (2), Stacks 06YN
(blueprint: lem-pur-equivariant-reduction-calculus). -/
def Action.EquivariantAcyclicTest (A : Action σ) (P : CochainComplex A.EqMod ℤ) : Prop :=
  letI := isMonoidal_W_independentCoefficients A.ring
  letI := monoidalCategory A.ring
  letI := preservesZeroMorphisms_curriedTensor_independentCoefficients A.ring
  letI := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A.ring
  ∀ E : CochainComplex A.EqMod ℤ, E.Acyclic →
    (CochainComplex.mapBifunctor
      ((A.forget.mapHomologicalComplex (.up ℤ)).obj E)
      ((A.forget.mapHomologicalComplex (.up ℤ)).obj P)
      (CategoryTheory.MonoidalCategory.curriedTensor A.Mod)).Acyclic

/-- Ordinary forgetting detects full equivariant K-flatness, including every
acyclic test, rather than only bounded tests or flat terms.
Source: blueprint (2), cyclic resolution argument
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: one direction follows by forgetting an equivariant acyclic test. For the
converse induce an arbitrary ordinary acyclic test by the coproduct of all its
integer translates under the module autoequivalence. This is an actual equivariant
acyclic complex. The original test tensor is a direct summand of its forgotten
tensor; exact coproducts and conservativity detect its acyclicity. -/
theorem Action.isKFlat_iff_equivariantAcyclicTest (A : Action σ)
    (P : CochainComplex A.EqMod ℤ) : A.IsKFlat P ↔ A.EquivariantAcyclicTest P := by
  sorry

/-- Every unbounded actual semilinear complex has an actual equivariant K-flat
resolution in the same abelian category, before localization.
Source: blueprint (2), cyclic flat resolutions
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: start with a functorial flat cover of ordinary module sheaves. Induce it
by the coproduct over all integer translates to obtain an equivariant flat cover.
Iterating functorially on kernels and using the unbounded flat resolution
construction gives a quasi-isomorphism with a flat-term K-flat complex. The
full acyclic-test detection just stated identifies this with equivariant K-flatness. -/
theorem equivariantKFlatResolution (A : Action σ) (K : CochainComplex A.EqMod ℤ) :
    ∃ (P : CochainComplex A.EqMod ℤ) (p : P ⟶ K), QuasiIso p ∧ A.IsKFlat P := by
  sorry

attribute [local instance] HasDerivedCategory.standard


universe a₀ b₀ a₁ b₁ h₀ k₀ h₁ k₁ w₀ z₀ w₁ z₁

/-- A derived comparison is normalized when its cochain counits give the specified
ordinary comparison on every resolving complex. This reusable equation keeps the
large sheaf presentations out of elaboration of the comparison's definition.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
@[irreducible] def IsNormalizedDerivedSquare
    {A₀ : Type a₀} [Category.{h₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀]
    {B₀ : Type b₀} [Category.{k₀} B₀] [Abelian B₀] [HasDerivedCategory.{z₀} B₀]
    {A₁ : Type a₁} [Category.{h₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
    {B₁ : Type b₁} [Category.{k₁} B₁] [Abelian B₁] [HasDerivedCategory.{z₁} B₁]
    (E : A₀ ⥤ B₀) [E.Additive] (E' : A₁ ⥤ B₁) [E'.Additive]
    (L : A₀ ⥤ A₁) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (V : B₀ ⥤ B₁) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : DerivedCategory A₀ ⥤ DerivedCategory B₀)
    (G : DerivedCategory A₁ ⥤ DerivedCategory B₁)
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : DerivedCategory.Q ⋙ G ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (e : E ⋙ V ≅ L ⋙ E')
    (d : F ⋙ V.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ G)
    (resolving : CochainComplex A₀ ℤ → Prop) : Prop :=
  ∀ P : CochainComplex A₀ ℤ, resolving P →
    d.hom.app (DerivedCategory.Q.obj P) ≫
      G.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      η.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ E')) (.up ℤ)).hom.app P) =
    V.mapDerivedCategory.map (ε.app P) ≫
      V.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)

/-- The equivariant scalar-extension universal pair, pinned to actual sheaf tensors
and to the underived unit, rather than an unspecified functor or comparison.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ScalarModel {A B : Action σ} (f : Map A B) where
  ordinary : DerivedChangeOfRingsCochainModel.{u, v, r, max (r + 1) u v,
    max (r + 1) u v} f.hom
  E : A.EqMod ⥤ B.EqMod
  [additive : E.Additive]
  underlying : E ⋙ B.forget ≅ A.forget ⋙ ordinary.E
  adj : E ⊣ f.eqRestrict
  unit_sections : ∀ (M : A.EqMod) (U : Cᵒᵖ) (m : M.carrier.val.obj U),
    (eqToHom (ordinary.obj_eq M.carrier)).val.app U
      ((underlying.hom.app M).val.app U ((adj.unit.app M).hom.f.val.app U m)) =
        scalarExtensionConstraintTmul.{u, v, r} f.hom M.carrier U m 1
  T : DerivedCategory A.EqMod ⥤ DerivedCategory B.EqMod
  ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  pointwise : (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
    (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  computes : ∀ P : CochainComplex A.EqMod ℤ, A.IsKFlat P → IsIso (ε.app P)
  preserves_kflat : ∀ P : CochainComplex A.EqMod ℤ, A.IsKFlat P →
    B.IsKFlat ((E.mapHomologicalComplex (.up ℤ)).obj P)
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated
  derived_adj : T ⊣ f.eqRestrict.mapDerivedCategory
  derived_unit : ∀ K : CochainComplex A.EqMod ℤ,
    derived_adj.unit.app (DerivedCategory.Q.obj K) ≫
      f.eqRestrict.mapDerivedCategory.map (ε.app K) ≫
      f.eqRestrict.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K)

attribute [instance] ScalarModel.additive


/-- Normalization of the derived forgetting comparison on the common K-flat model.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ScalarForgettingComparison {A B : Action σ} {f : Map A B}
    (F : ScalarModel f) where
  derived : F.T ⋙ B.forget.mapDerivedCategory ≅ A.forget.mapDerivedCategory ⋙ F.ordinary.T
  normalized : IsNormalizedDerivedSquare F.E F.ordinary.E A.forget B.forget
    F.T F.ordinary.T F.ε F.ordinary.ε F.underlying derived A.IsKFlat

/-- The derived forgetting comparison is the ordinary comparison before localization.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the exact forgetful functor sends the resolving complex to the same ordinary
K-flat complex. Its tensor map is the carrier comparison of the underived adjunction.
Localize this map and compare the two universal counits. Their equality on the
resolving category gives precisely the displayed normalization. -/
theorem scalarForgettingComparison_nonempty {A B : Action σ} {f : Map A B}
    (F : ScalarModel f) : Nonempty (ScalarForgettingComparison F) := by
  sorry

/-- The carrier isomorphism to the specified sheafified tensor.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
def ScalarModel.tensorIso {A B : Action σ} {f : Map A B} (F : ScalarModel f)
    (M : A.EqMod) : (F.E.obj M).carrier ≅ changeOfRings.{v, u, r} f.hom M.carrier :=
  F.underlying.app M ≪≫ eqToIso (F.ordinary.obj_eq M.carrier)

/-- A pure tensor in actual equivariant extension, using its carrier identification.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
def ScalarModel.tmul {A B : Action σ} {f : Map A B} (F : ScalarModel f)
    (M : A.EqMod) (U : Cᵒᵖ) (m : M.carrier.val.obj U) (s : B.ring.obj.obj U) :
    (F.E.obj M).carrier.val.obj U :=
  (F.tensorIso M).inv.val.app U
    (scalarExtensionConstraintTmul.{u, v, r} f.hom M.carrier U m s)

/-- Scalar identity, normalized on pure tensors and on the common K-flat model.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure UnitComparison {A : Action σ} {f : Map A A} (F : ScalarModel f) where
  ordinary : F.E ≅ 𝟭 A.EqMod
  sections : ∀ (M : A.EqMod) (U : Cᵒᵖ) (m : M.carrier.val.obj U)
    (s : A.ring.obj.obj U),
    (ordinary.hom.app M).hom.f.val.app U (F.tmul M U m s) = s • m
  derived : F.T ≅ 𝟭 (DerivedCategory A.EqMod)
  normalized : ∀ (P : CochainComplex A.EqMod ℤ), A.IsKFlat P →
    derived.hom.app (DerivedCategory.Q.obj P) = F.ε.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso A.EqMod (.up ℤ)).hom.app P)

/-- Scalar composition uses multiplication of the two coefficient factors, before
localization, and the same comparison after localization.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure CompositionComparison {A B D : Action σ}
    {f : Map A B} {g : Map B D} {h : Map A D}
    (F : ScalarModel f) (G : ScalarModel g) (H : ScalarModel h) where
  ordinary : F.E ⋙ G.E ≅ H.E
  sections : ∀ (M : A.EqMod) (U : Cᵒᵖ) (m : M.carrier.val.obj U)
    (s : B.ring.obj.obj U) (t : D.ring.obj.obj U),
    (ordinary.hom.app M).hom.f.val.app U
      (G.tmul (F.E.obj M) U (F.tmul M U m s) t) =
        H.tmul M U m (t * g.hom.hom.app U s)
  derived : F.T ⋙ G.T ≅ H.T
  normalized : ∀ (P : CochainComplex A.EqMod ℤ), A.IsKFlat P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫ H.ε.app P =
      G.T.map (F.ε.app P) ≫ G.ε.app ((F.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P)

/-- All scalar models admit the canonical identity comparison.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: multiplication r tensor m maps to rm, inverse m maps to 1 tensor m. These
maps intertwine by the restriction adjunction's normalized unit. Their localization
on the resolving category determines the derived comparison and its equation. -/
theorem unitComparison_nonempty {A : Action σ} (f : Map A A)
    (hf : f.hom = 𝟙 A.ring) (F : ScalarModel f) : Nonempty (UnitComparison F) := by
  sorry

/-- All scalar models admit the canonical composition comparison.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the balanced map t tensor (s tensor m) maps to t*g(s) tensor m; its inverse
inserts 1 in the middle factor. Both are equivariant by the normalized adjunctions.
Scalar extension preserves K-flatness, so successive extensions of one resolution
compute both sides. Localize this ordinary isomorphism and its pure-tensor equation. -/
theorem compositionComparison_nonempty {A B D : Action σ}
    (f : Map A B) (g : Map B D) (h : Map A D)
    (hh : h.hom = f.hom ≫ g.hom)
    (F : ScalarModel f) (G : ScalarModel g) (H : ScalarModel h) :
    Nonempty (CompositionComparison F G H) := by
  sorry

/-- Equivariant derived extension exists on the whole unbounded derived category.
Source: blueprint (2), Stacks 06YY (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: cyclic flat-term K-flat resolutions give actual semilinear complexes.
Tensor before localization, using exact conservative forgetting to detect
quasi-isomorphisms and K-flatness. The resolving localization gives the pointwise
universal pair. The tensor/restriction adjunction has unit 1 tensor m. Shifts and
cones are termwise. The same resolution computes the ordinary forgetful comparison. -/
theorem scalarModel_nonempty {A B : Action σ} (f : Map A B) :
    Nonempty (ScalarModel f) := by
  sorry


/-- The actual scalar functor preserves quasi-isomorphisms between full
acyclic-test equivariant K-flat complexes.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the derived functor T of the scalar model sends the localization of the
quasi-isomorphism p to an isomorphism. Naturality of the counit ε gives
ε_P ≫ Q(E p) = T(Q p) ≫ ε_Q, and ε_P, ε_Q are invertible on the K-flat complexes P, Q
(`computes`). Hence Q(E p) is invertible, i.e. E p is a quasi-isomorphism. -/
theorem scalar_preservesQuasiIso {A B : Action σ} {f : Map A B} (F : ScalarModel f)
    {P Q : CochainComplex A.EqMod ℤ} (p : P ⟶ Q)
    (hP : A.IsKFlat P) (hQ : A.IsKFlat Q) (hp : QuasiIso p) :
    QuasiIso ((F.E.mapHomologicalComplex (.up ℤ)).map p) := by
  have hp' : QuasiIso p := hp
  have hm : IsIso (F.T.map (DerivedCategory.Q.map p)) := by infer_instance
  have hεP : IsIso (F.ε.app P) := F.computes P hP
  have hεQ : IsIso (F.ε.app Q) := F.computes Q hQ
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso B.EqMod _).1
  rw [← isIso_comp_left_iff (F.ε.app P)]
  change IsIso (F.ε.app P ≫
    (F.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map p)
  rw [← F.ε.naturality p]
  change IsIso (F.T.map (DerivedCategory.Q.map p) ≫ F.ε.app Q)
  infer_instance

/-- One strict quotient system, before localization, and its derived universal pair.
The cokernel universal properties fix the quotient action; the transition equation
fixes the actual quotient transitions. The natural counit is a map of whole systems.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ReductionModel {A B : Action σ} {f : Map A B}
    (l : ℕ) (F : ScalarModel f) where
  E : A.EqMod ⥤ (ℕᵒᵖ ⥤ B.EqMod)
  [additive : E.Additive]
  π : ∀ n : ℕ, F.E ⟶ E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)
  zero : ∀ (n : ℕ) (M : A.EqMod),
    (l ^ (n + 1) • 𝟙 (F.E.obj M)) ≫ (π n).app M = 0
  quotient : ∀ (n : ℕ) (M : A.EqMod),
    IsColimit (CokernelCofork.ofπ ((π n).app M) (zero n M))
  transition : ∀ (n : ℕ) (M : A.EqMod),
    (π (n + 1)).app M ≫ (E.obj M).map (homOfLE n.le_succ).op = (π n).app M
  ordinary_unit : ∀ n : ℕ,
    𝟭 A.EqMod ⟶ (E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)) ⋙ f.eqRestrict
  ordinary_unit_eq : ∀ (n : ℕ) (M : A.EqMod),
    (ordinary_unit n).app M =
      F.adj.unit.app M ≫ f.eqRestrict.map ((π n).app M)
  T : DerivedCategory A.EqMod ⥤ DerivedCategory (ℕᵒᵖ ⥤ B.EqMod)
  ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  pointwise : (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
    (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  computes : ∀ P : CochainComplex A.EqMod ℤ, A.IsKFlat P → IsIso (ε.app P)
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated
  level : ∀ _n : ℕ,
    DerivedCategory A.EqMod ⥤ DerivedCategory B.EqMod
  level_counit : ∀ n : ℕ, DerivedCategory.Q ⋙ level n ⟶
    (E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q
  level_universal : ∀ n : ℕ, (level n).IsLeftDerivedFunctor (level_counit n)
    (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  unit : ∀ n : ℕ, 𝟭 (DerivedCategory A.EqMod) ⟶ level n ⋙ f.eqRestrict.mapDerivedCategory
  unit_normalized : ∀ (n : ℕ) (K : CochainComplex A.EqMod ℤ),
    (unit n).app (DerivedCategory.Q.obj K) ≫
      f.eqRestrict.mapDerivedCategory.map ((level_counit n).app K) ≫
      f.eqRestrict.mapDerivedCategoryFactors.hom.app
        (((E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapHomologicalComplex
          (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso A.EqMod (.up ℤ)).inv.app K ≫
          (NatTrans.mapHomologicalComplex (ordinary_unit n) (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl
            ((E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)) ⋙
              f.eqRestrict)) (.up ℤ)).inv.app K)
  evaluation : ∀ n : ℕ,
    T ⋙ ((CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapDerivedCategory ≅ level n
  evaluation_normalized : ∀ (n : ℕ) (P : CochainComplex A.EqMod ℤ),
    (evaluation n).hom.app (DerivedCategory.Q.obj P) ≫ (level_counit n).app P =
      (((CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapDerivedCategory).map
        (ε.app P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl
          (E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n))) (.up ℤ)).hom.app P)

attribute [instance] ReductionModel.additive

/-- Simultaneous reduction exists using one actual equivariant K-flat resolution.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: take level n to be the cokernel of l^(n+1) on scalar extension; cokernel
universality supplies every transition and functorial map. Exact evaluation detects
quasi-isomorphisms. Thus this one functor to the whole tower category inverts
quasi-isomorphisms between equivariant K-flat complexes. Resolve and localize to
obtain its pointwise left derivation. Evaluation is exact, so evaluation of the
universal pair is the specified level left derivation. Shifts and cones commute
with the termwise quotient construction, giving its triangulated structure. -/
theorem reductionModel_nonempty {A B : Action σ} {f : Map A B}
    (l : ℕ) [Fact l.Prime] (F : ScalarModel f) :
    Nonempty (ReductionModel l F) := by
  sorry


/-- Scalar composition compares the entire simultaneous quotient systems. The
projection equation fixes the ordinary tower comparison before localization.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ReductionCompositionComparison {A B D : Action σ}
    {f : Map A B} {g : Map B D} {h : Map A D}
    (F : ScalarModel f) (G : ScalarModel g) (H : ScalarModel h)
    (S : CompositionComparison F G H) (l : ℕ)
    (R : ReductionModel l G) (R' : ReductionModel l H) where
  ordinary : F.E ⋙ R.E ≅ R'.E
  projections : ∀ (n : ℕ) (M : A.EqMod),
    (R.π n).app (F.E.obj M) ≫ (ordinary.hom.app M).app (op n) =
      S.ordinary.hom.app M ≫ (R'.π n).app M
  derived : F.T ⋙ R.T ≅ R'.T
  normalized : ∀ P : CochainComplex A.EqMod ℤ, A.IsKFlat P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫ R'.ε.app P =
      R.T.map (F.ε.app P) ≫ R.ε.app ((F.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P)

/-- Scalar composition descends as a comparison of the single derived systems,
including every transition and the scalar identity specialization.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: multiplication of scalar factors identifies the two underived extensions.
Take cokernels of multiplication by l^(n+1) simultaneously; their universal
properties give the projection equation and force every transition square.
The first scalar extension preserves K-flatness, so successive operations on
one resolving complex compute both derived routes. Localize the ordinary tower
comparison to obtain the counit equation. In the identity specialization the
same construction is multiplication r tensor m to rm; the scalar unit and
associativity laws therefore hold for the whole towers before localization. -/
theorem reductionCompositionComparison_nonempty {A B D : Action σ}
    {f : Map A B} {g : Map B D} {h : Map A D}
    (F : ScalarModel f) (G : ScalarModel g) (H : ScalarModel h)
    (S : CompositionComparison F G H) (l : ℕ)
    (R : ReductionModel l G) (R' : ReductionModel l H) :
    Nonempty (ReductionCompositionComparison F G H S l R R') := by
  sorry

/-- Ring sheafification in the sheaf universe of the site.
Source: Stacks 00W1 (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: replace the essentially small site by its small model. Sheafification of
commutative rings exists there and its adjunction transports back along the site
equivalence. This specifies the usual reflective localization, up to unique isomorphism. -/
theorem commRingSheafify : HasSheafify J CommRingCat.{r} := by
  exact hasSheafifyEssentiallySmallSite.{v, r, u, r + 1, r} J CommRingCat.{r}

attribute [local instance] commRingSheafify

/-- Constant ring sheaves retain the ordinary constant-sheaf construction.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev constantRing (K : CommRingCat.{r}) := (constantSheaf J CommRingCat.{r}).obj K

/-- The actual constant integer-to-p-adic scalar map.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
def integerToPadic (l : ℕ) [Fact l.Prime] :
    constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ)) ⟶
      constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ_[l])) :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Int.castRingHom ℤ_[l]).comp ULift.ringEquiv.toRingHom)))

/-- The actual positive-level constant p-adic quotient.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
def padicQuotient (l : ℕ) [Fact l.Prime] (n : ℕ) :
    constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ_[l])) ⟶
      constantRing (J := J) (CommRingCat.of (ULift.{r} (ZMod (l ^ (n + 1))))) :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)))

/-- Integral coefficients with their actual constant sheaves and residue maps.
These are presentation isomorphisms, not independently chosen coefficient rings.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure IntegralCoefficients (l : ℕ) [Fact l.Prime] where
  Z : Action σ
  C : Action σ
  Q : ℕ → Action σ
  z : Z.ring ≅ constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ))
  c : C.ring ≅ constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ_[l]))
  q : ∀ n : ℕ, (Q n).ring ≅
    constantRing (J := J) (CommRingCat.of (ULift.{r} (ZMod (l ^ (n + 1)))))
  scalar : Map Z C
  scalar_eq : scalar.hom = z.hom ≫ integerToPadic l ≫ c.inv
  quotient : ∀ n : ℕ, Map C (Q n)
  quotient_eq : ∀ n : ℕ, (quotient n).hom = c.hom ≫ padicQuotient l n ≫ (q n).inv
  finite : ∀ n : ℕ, Map Z (Q n)
  finite_eq : ∀ n : ℕ, (finite n).hom = scalar.hom ≫ (quotient n).hom

/-- All constant coefficient rings have their canonical equivariant presentations.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: inverse image commutes with the constant-object functor by its adjunction.
Transport the ring and module operations through that comparison. All residue
maps come from constant ring homomorphisms and therefore commute with this action. -/
theorem integralCoefficients_nonempty (l : ℕ) [Fact l.Prime] :
    Nonempty (IntegralCoefficients (σ := σ) l) := by
  sorry

/-- The simultaneous integral reduction together with its finite coefficient
realizations. The section equation fixes the canonical quotient comparison, while
the derived equation fixes it on the very same K-flat representative.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure IntegralReductionModel (l : ℕ) [Fact l.Prime]
    (P : IntegralCoefficients (σ := σ) l) where
  scalar : ScalarModel P.scalar
  system : ReductionModel l scalar
  finite : ∀ n : ℕ, ScalarModel (P.finite n)
  ordinary : ∀ n : ℕ,
    system.E ⋙ (CategoryTheory.evaluation ℕᵒᵖ P.C.EqMod).obj (op n) ≅
      (finite n).E ⋙ (P.quotient n).eqRestrict
  sections : ∀ (n : ℕ) (M : P.Z.EqMod) (U : Cᵒᵖ)
    (m : M.carrier.val.obj U) (s : P.C.ring.obj.obj U),
    (((finite n).tensorIso M).hom.val.app U)
      (((ordinary n).hom.app M).hom.f.val.app U
        (((system.π n).app M).hom.f.val.app U (scalar.tmul M U m s))) =
      scalarExtensionConstraintTmul.{u, v, r} (P.finite n).hom M.carrier U m
        ((P.quotient n).hom.hom.app U s)
  derived : ∀ n : ℕ,
    system.level n ≅ (finite n).T ⋙ (P.quotient n).eqRestrict.mapDerivedCategory
  normalized : ∀ (n : ℕ) (K : CochainComplex P.Z.EqMod ℤ), P.Z.IsKFlat K →
    (derived n).hom.app (DerivedCategory.Q.obj K) ≫
      (P.quotient n).eqRestrict.mapDerivedCategory.map ((finite n).ε.app K) ≫
      (P.quotient n).eqRestrict.mapDerivedCategoryFactors.hom.app
        (((finite n).E.mapHomologicalComplex (.up ℤ)).obj K) =
      (system.level_counit n).app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (ordinary n).symm (.up ℤ)).inv.app K)

/-- The one derived tower has the prescribed finite scalar extensions and quotient
transitions, with every comparison computed on its common K-flat representative.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: take the scalar model to constant p-adic coefficients and the strict cokernel
system. Its level n is canonically extension to Z/l^(n+1), followed by restriction;
the displayed pure-tensor map determines this comparison. Both routes are computed
on one K-flat complex, so the comparison localizes with the displayed counit equation.
The quotient universal properties force all successor transitions and their compatibility. -/
theorem integralReductionModel_nonempty (l : ℕ) [Fact l.Prime]
    (P : IntegralCoefficients (σ := σ) l) : Nonempty (IntegralReductionModel l P) := by
  sorry

/-- Underlying abelian sheaves of actual semilinear modules.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Action.ab (A : Action σ) : A.EqMod ⥤ Sheaf J AddCommGrpCat.{r} :=
  A.forget ⋙ toSheaf _

/-- The underlying sheaves of sets, retaining the module inverse-image comparison.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Action.moduleSets (A : Action σ) : A.Mod ⥤ Sheaf J (Type r) :=
  toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

/-- The regular module with its specified semilinear ring action. The section
isomorphism is linear into the ring acting on itself; the last equation fixes the action.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure UnitPresentation (A : Action σ) where
  M : A.EqMod
  sections : A.moduleSets.obj M.carrier ≅
    (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj A.ring
  linear : ∀ (U : Cᵒᵖ) (a : A.ring.obj.obj U) (m : M.carrier.val.obj U),
    sections.hom.hom.app U (a • m) = a * (@id (A.ring.obj.obj U) (sections.hom.hom.app U m))
  action : A.moduleSets.map M.str.hom ≫ sections.hom =
    A.lift.moduleUnderlying.hom.app M.carrier ≫ σ.functor.map sections.hom ≫
      A.lift.ringUnderlying.hom

/-- The equivariant regular module exists with its canonical normalization.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: use the ring sheaf acting on itself by multiplication. Its algebraic inverse
image is the regular inverse-image ring module, and the given ring identification
is linear. Its multiplication graph gives the displayed linearity and action equation. -/
theorem unitPresentation_nonempty (A : Action σ) : Nonempty (UnitPresentation A) := by
  let U := unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A.ring)
  let e : A.lift.modules.obj U ≅ U :=
    CochainTensorComparison.UnitConstruction.unitIso A.ring A.ring σ.functor A.lift
  refine ⟨{ M := IsoAlgebra.mk U e
            sections := Iso.refl _
            linear := ?_
            action := ?_ }⟩
  · intro W a m
    rfl
  · simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    ext W x
    rfl

/-- Reduction of the integral regular module is the constant quotient tower. The
section equation identifies each level with the actual finite coefficient ring,
and the strict quotient equations in `system` determine all transitions.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ConstantReduction (l : ℕ) [Fact l.Prime]
    {P : IntegralCoefficients (σ := σ) l} (R : IntegralReductionModel l P)
    (U : UnitPresentation P.Z) where
  finite_unit : ∀ n : ℕ, UnitPresentation (P.Q n)
  level : ∀ n : ℕ, (R.system.E.obj U.M).obj (op n) ≅
    (P.quotient n).eqRestrict.obj (finite_unit n).M
  sections : ∀ (n : ℕ) (V : Cᵒᵖ) (m : U.M.carrier.val.obj V)
      (s : P.C.ring.obj.obj V),
    (finite_unit n).sections.hom.hom.app V
      (((level n).hom).hom.f.val.app V
        (((R.system.π n).app U.M).hom.f.val.app V (R.scalar.tmul U.M V m s))) =
      (P.quotient n).hom.hom.app V s *
        (P.finite n).hom.hom.app V (U.sections.hom.hom.app V m)
  iso : R.system.T.obj ((DerivedCategory.singleFunctor P.Z.EqMod 0).obj U.M) ≅
    (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ P.C.EqMod) 0).obj (R.system.E.obj U.M)
  normalized :
    R.system.T.map ((DerivedCategory.singleFunctorIsoCompQ P.Z.EqMod 0).hom.app U.M) ≫
      R.system.ε.app ((CochainComplex.singleFunctor P.Z.EqMod 0).obj U.M) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex R.system.E (.up ℤ) 0).hom.app U.M) =
    iso.hom ≫ (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ P.C.EqMod) 0).hom.app
      (R.system.E.obj U.M)

/-- The regular integral module computes its own simultaneous reduction.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the regular module is flat and its degree-zero complex is K-flat, since
tensoring with it is the identity. Its scalar extension is the regular C-module
by multiplication on pure tensors. The cokernel of l^(n+1) is the constant finite
quotient ring. Their quotient universal properties give the level isomorphisms
and the actual quotient transitions. The resolving counit gives the whole-system iso. -/
theorem constantReduction_nonempty (l : ℕ) [Fact l.Prime]
    {P : IntegralCoefficients (σ := σ) l} (R : IntegralReductionModel l P)
    (U : UnitPresentation P.Z) : Nonempty (ConstantReduction l R U) := by
  sorry

universe t
open AlgebraicGeometry

/-- The sheaf of sets of units used by the recorded Kummer sequence.
Source: Stacks 03PL (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev unitsSets (T : Scheme.{t}) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj (Scheme.proEtaleUnitsSheaf T)

/-- A scheme automorphism acts on units by the identity on the sections of the
unchanged test scheme. This uniquely specifies the canonical units comparison.
Source: Stacks 03PL (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: postcomposition changes only a test object's structure map to T, not its
underlying scheme or its global units. The identity on these units is natural;
postcomposition with the inverse is its inverse. Sectionwise equality gives uniqueness. -/
theorem unitsAction_existsUnique (T : Scheme.{t}) (g : T ≅ T) :
    ∃! e : (Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1))).obj
        (unitsSets T) ≅ unitsSets T,
      ∀ (V : T.ProEtᵒᵖ) (x : ((Scheme.isoSectionwiseInverseImage g.hom
          (Type (t + 1))).obj (unitsSets T)).obj.obj V),
        HEq (e.hom.hom.app V x) x := by
  let e : (Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1))).obj
      (unitsSets T) ≅ unitsSets T :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  refine ⟨e, ?_, ?_⟩
  · intro V x
    rfl
  · intro e' he'
    apply Iso.ext
    apply ObjectProperty.hom_ext
    ext V x
    exact eq_of_heq (he' V x)

/-- The canonical comparison characterized in `unitsAction_existsUnique`.
Source: Stacks 03PL (blueprint: lem-pur-equivariant-reduction-calculus). -/
def unitsAction (T : Scheme.{t}) (g : T ≅ T) :=
  (unitsAction_existsUnique T g).exists.choose

/-- The actual equivariant Kummer sequence, with the existing kernel sheaves and
power transitions. The structure equation specifies the natural scheme action
on units; the monic inclusions then specify the action on roots.
Source: Stacks 03PL, blueprint (3) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure KummerPresentation (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] (P : IntegralCoefficients (σ := τ) l) where
  G : P.Z.EqMod
  units : P.Z.ab.obj G ≅ Scheme.proEtaleUnitsSheaf T
  action : P.Z.moduleSets.map G.str.hom ≫
      (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map units.hom =
    P.Z.lift.moduleUnderlying.hom.app G.carrier ≫
      τ.functor.map
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map units.hom) ≫
      s.hom.app (unitsSets T) ≫ (unitsAction T g).hom
  U : ℕᵒᵖ ⥤ P.C.EqMod
  roots : U ⋙ P.C.ab ≅ Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)
  inclusion : ∀ n : ℕ, P.scalar.eqRestrict.obj (U.obj (op n)) ⟶ G
  inclusion_eq : ∀ n : ℕ, P.Z.ab.map (inclusion n) ≫ units.hom =
    roots.hom.app (op n) ≫ Scheme.proEtaleRootsOfUnityInclusion T (l ^ (n + 1))
  zero : ∀ n : ℕ, inclusion n ≫ (l ^ (n + 1) • 𝟙 G) = 0
  exact : ∀ n : ℕ,
    (ShortComplex.mk (inclusion n) (l ^ (n + 1) • 𝟙 G) (zero n)).ShortExact

/-- Kummer exactness lifts to actual semilinear module sheaves.
Source: Stacks 03PL, blueprint (3) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: units carry their canonical integral action; roots are the recorded kernel
of the power map. Their l-power torsion gives the canonical action of Z_l through
Z/l^(n+1). Postcomposition by the scheme automorphism respects multiplication,
powers and these inclusions. Invertibility of l makes the power map locally
surjective by the finite etale root cover, also a pro-etale cover. Kernels and
cokernels are created by exact fixed-pair forgetting. The recorded power maps
on roots are linear, equivariant and compose to the specified root tower. -/
theorem kummerPresentation_nonempty (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] [∀ x : T, Invertible (l : T.residueField x)]
    (P : IntegralCoefficients (σ := τ) l) :
    Nonempty (KummerPresentation T g τ s l P) := by
  sorry

/-- The whole-system Kummer identification with its positive scalar-unit
normalization. Evaluation and single/shift comparisons are displayed explicitly.
Source: Stacks 03PL, blueprint (3)-(4)
(blueprint: lem-pur-equivariant-reduction-calculus). -/
structure KummerModel (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] {P : IntegralCoefficients.{t + 1, t, t + 1} (σ := τ) l}
    (R : IntegralReductionModel.{t + 1, t, t + 1} l P) (K : KummerPresentation T g τ s l P) where
  iso : R.system.T.obj (((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj
    K.G)⟦(1 : ℤ)⟧) ≅
    ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} (ℕᵒᵖ ⥤ P.C.EqMod) 0).obj K.U)⟦(2 : ℤ)⟧
  level : ∀ n : ℕ,
    (R.system.level n).obj (((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod
      0).obj K.G)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.C.EqMod 0).obj (K.U.obj (op n)))⟦(2
        : ℤ)⟧
  evaluation : ∀ n : ℕ,
    (R.system.evaluation n).hom.app
        (((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj K.G)⟦(1 : ℤ)⟧) ≫
      (level n).hom =
    ((CategoryTheory.evaluation ℕᵒᵖ P.C.EqMod).obj (op n)).mapDerivedCategory.map iso.hom ≫
      (((CategoryTheory.evaluation ℕᵒᵖ P.C.EqMod).obj (op n)).mapDerivedCategory.commShiftIso
        (2 : ℤ)).hom.app ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} (ℕᵒᵖ ⥤ P.C.EqMod)
          0).obj K.U) ≫
      ((((CategoryTheory.evaluation ℕᵒᵖ P.C.EqMod).obj (op n)).mapDerivedCategorySingleFunctor
        0).hom.app K.U)⟦(2 : ℤ)⟧'
  positive : ∀ n : ℕ,
    (R.system.unit n).app (((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj
      K.G)⟦(1 : ℤ)⟧) ≫
      P.scalar.eqRestrict.mapDerivedCategory.map (level n).hom ≫
      (P.scalar.eqRestrict.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.C.EqMod 0).obj (K.U.obj (op n))) ≫
      ((P.scalar.eqRestrict.mapDerivedCategorySingleFunctor 0).hom.app
        (K.U.obj (op n)))⟦(2 : ℤ)⟧' =
    (ShortComplex.ShortExact.singleδ.{t + 2} (K.exact n))⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory.{t + 2, t + 1, t + 2} P.Z.EqMod) (1 : ℤ) 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj
          (P.scalar.eqRestrict.obj (K.U.obj (op n))))

/-- The normalized Kummer isomorphism exists as an isomorphism of the single
simultaneous derived system, not a family of unrelated evaluated isomorphisms.
Source: Stacks 03PL, blueprint (3)-(4)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: resolve the equivariant units complex once by a flat-term K-flat complex.
At every exponent the two-term multiplication cone computes its derived reduction.
The Kummer short exact sequence identifies that cone with roots shifted once;
choose the cone comparison whose scalar unit is the positive connecting map.
Shift once more and insert the canonical shift-addition comparison. The maps of
Kummer sequences (power l on the kernel and identity on the last units term)
intertwine the quotient maps of the same resolution. Consequently the comparisons
are maps of strict systems and localize to the stated whole-system isomorphism.
The cochain unit normalization gives the displayed positive equation. -/
theorem kummerModel_nonempty (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] {P : IntegralCoefficients.{t + 1, t, t + 1} (σ := τ) l}
    (R : IntegralReductionModel.{t + 1, t, t + 1} l P) (K : KummerPresentation T g τ s l P) :
    Nonempty (KummerModel T g τ s l R K) := by
  sorry

/-- Every arrow has the positive Kummer boundary as its scalar adjunct.
Source: blueprint (4) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: apply naturality of the normalized reduction unit to a, then compose the
positive-unit equation of the Kummer model. This gives the asserted equality
without a choice of representative or a separate sign choice for a. -/
theorem kummer_adjunct (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] {P : IntegralCoefficients.{t + 1, t, t + 1} (σ := τ) l}
    (R : IntegralReductionModel.{t + 1, t, t + 1} l P) (K : KummerPresentation T g τ s l P)
    (I : KummerModel T g τ s l R K) (U : UnitPresentation P.Z) (n : ℕ)
    (a : (DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj U.M ⟶
      ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj K.G)⟦(1 : ℤ)⟧) :
    (R.system.unit n).app ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj
      U.M) ≫
      P.scalar.eqRestrict.mapDerivedCategory.map ((R.system.level n).map a ≫ (I.level n).hom) ≫
      (P.scalar.eqRestrict.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.C.EqMod 0).obj (K.U.obj (op n))) ≫
      ((P.scalar.eqRestrict.mapDerivedCategorySingleFunctor 0).hom.app
        (K.U.obj (op n)))⟦(2 : ℤ)⟧' =
    a ≫ (ShortComplex.ShortExact.singleδ.{t + 2} (K.exact n))⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory.{t + 2, t + 1, t + 2} P.Z.EqMod) (1 : ℤ) 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj
          (P.scalar.eqRestrict.obj (K.U.obj (op n)))) := by
  have hn := (R.system.unit n).naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← hn]
  simpa only [Category.assoc] using congrArg (fun b ↦ a ≫ b) (I.positive n)

universe u' v'

/-- A geometric inverse image, with its given commuting action and inverse-image
ring identification. Only ring and operation data are inputs; the equivariant
module functor and its exactness are constructed below.
Source: Stacks 03D2, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus). -/
structure InverseImage {D : Type u'} [Category.{v'} D] [EssentiallySmall.{r} D]
    {K : GrothendieckTopology D}
    {τ : Sheaf K (Type r) ≌ Sheaf K (Type r)}
    (A : Action σ) (B : Action τ) where
  L : Sheaf J (Type r) ⥤ Sheaf K (Type r)
  right : Sheaf K (Type r) ⥤ Sheaf J (Type r)
  adj : L ⊣ right
  [leftExact : PreservesFiniteLimits L]
  comm : σ.functor ⋙ L ≅ L ⋙ τ.functor
  algebraic : AlgebraicInverseImage L A.ring B.ring
  ring_comm : L.map A.lift.ringUnderlying.hom ≫ algebraic.ringUnderlying.hom =
    comm.hom.app ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj A.ring) ≫
      τ.functor.map algebraic.ringUnderlying.hom ≫ B.lift.ringUnderlying.hom

attribute [instance] InverseImage.leftExact

section Pullback
variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {τ : Sheaf K (Type r) ≌ Sheaf K (Type r)}
  {A : Action σ} {B : Action τ}

/-- The commuting module comparison is fixed on underlying set sheaves.
Source: Stacks 03D2, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: compose the three algebraic underlying-sheaf identifications and the given
topos commuting isomorphism. The ring square and operation graphs imply linearity
and naturality; the inverse uses the inverse comparisons. Faithful underlying
forgetting gives uniqueness. This construction precedes all localizations. -/
theorem InverseImage.comparison_existsUnique (H : InverseImage A B) :
    ∃! e : H.algebraic.modules ⋙ B.lift.modules ≅ A.lift.modules ⋙ H.algebraic.modules,
      ∀ M : A.Mod, B.moduleSets.map (e.hom.app M) =
        B.lift.moduleUnderlying.hom.app (H.algebraic.modules.obj M) ≫
          τ.functor.map (H.algebraic.moduleUnderlying.hom.app M) ≫
          H.comm.inv.app (A.moduleSets.obj M) ≫
          H.L.map (A.lift.moduleUnderlying.inv.app M) ≫
          H.algebraic.moduleUnderlying.inv.app (A.lift.modules.obj M) := by
  sorry

/-- Canonical inverse image on actual semilinear modules.
Source: Stacks 03D2, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus). -/
def InverseImage.eqPullback (H : InverseImage A B) : A.EqMod ⥤ B.EqMod :=
  IsoAlgebra.mapOfNatIso H.comparison_existsUnique.exists.choose

/-- Geometric inverse image is additive.
Source: Stacks 03D2, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the underlying module-addition graph transports addition of maps through
inverse image, and the commuting comparison does not change these maps. -/
theorem InverseImage.additive (H : InverseImage A B) : H.eqPullback.Additive := by
  have := algebraicImage_additive H.algebraic
  exact IsoAlgebra.additive_mapOfNatIso _

attribute [instance] InverseImage.additive

/-- Geometric inverse image is exact and preserves equivariant
K-flat complexes. These are conclusions about the constructed lift.
Source: Stacks 03D2, 06YY, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: inverse image of sets preserves finite limits and all colimits. Operation
graphs transport this to addition, kernels and cokernels of modules. Semilinear
kernels and cokernels are created on carriers. The inverse-image tensor comparison
and the adjunction transport the acyclic tensor test, or equivalently pull back
flat-term K-flat resolutions. Exact conservative forgetting detects the result. -/
theorem InverseImage.properties (H : InverseImage A B) :
    PreservesFiniteLimits H.eqPullback ∧
      PreservesFiniteColimits H.eqPullback ∧
      ∀ P : CochainComplex A.EqMod ℤ, A.IsKFlat P →
        B.IsKFlat ((H.eqPullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

/-- Left exactness of the constructed equivariant inverse image.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance InverseImage.limits (H : InverseImage A B) :
    PreservesFiniteLimits H.eqPullback := H.properties.1

/-- Right exactness of the constructed equivariant inverse image.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance InverseImage.colimits (H : InverseImage A B) :
    PreservesFiniteColimits H.eqPullback := H.properties.2.1

end Pullback


section RingedPullback
variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {τ : Sheaf K (Type r) ≌ Sheaf K (Type r)}
  {A : Action σ} {B V : Action τ}

/-- General ringed inverse image is geometric inverse image followed by the
specified derived scalar extension to the target ring. Both factors are the
normalized constructions, with no flatness hypothesis on the ring morphism.
Source: Stacks 06YY, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus). -/
def derivedRingedPullback (H : InverseImage A B) {f : Map B V} (F : ScalarModel f) :
    DerivedCategory A.EqMod ⥤ DerivedCategory V.EqMod :=
  H.eqPullback.mapDerivedCategory ⋙ F.T

/-- The actual cochain counit of general derived ringed inverse image.
Source: Stacks 06YY, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus). -/
def derivedRingedPullbackCounit (H : InverseImage A B) {f : Map B V} (F : ScalarModel f) :
    DerivedCategory.Q ⋙ derivedRingedPullback H F ⟶
      (H.eqPullback ⋙ F.E).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator DerivedCategory.Q H.eqPullback.mapDerivedCategory F.T).inv ≫
    Functor.whiskerRight H.eqPullback.mapDerivedCategoryFactors.hom F.T ≫
    (Functor.associator (H.eqPullback.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q F.T).hom ≫
    Functor.whiskerLeft (H.eqPullback.mapHomologicalComplex (.up ℤ)) F.ε ≫
    (Functor.associator (H.eqPullback.mapHomologicalComplex (.up ℤ))
      (F.E.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).inv ≫
    Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (Iso.refl (H.eqPullback ⋙ F.E)) (.up ℤ)).hom DerivedCategory.Q

/-- The factored construction is the everywhere-defined derived inverse image
of the actual ringed inverse-image functor and is computed on the same K-flat
complexes. Scalar pullback and scalar composition above give its comparisons.
Source: Stacks 06YY, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: geometric inverse image is exact, preserves full K-flatness, and preserves
quasi-isomorphisms. Apply scalar extension to its image of one resolving complex.
The resulting counit is the displayed composite of the exact localization
comparison and the scalar counit. Resolving localization gives the pointwise
left-derived universal property and its invertibility on K-flat complexes.
The exact geometric functor and the triangulated scalar functor commute with
shifts and cones. Composition is fixed by the balanced scalar comparison, so
their forgetting and pullback comparisons are the preceding normalized ones. -/
theorem derivedRingedPullback_properties (H : InverseImage A B) {f : Map B V}
    (F : ScalarModel f) :
    (derivedRingedPullback H F).IsLeftDerivedFunctor (derivedRingedPullbackCounit H F)
      (HomologicalComplex.quasiIso A.EqMod (.up ℤ)) ∧
    ((H.eqPullback ⋙ F.E).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
        (HomologicalComplex.quasiIso A.EqMod (.up ℤ)) ∧
    (∀ P : CochainComplex A.EqMod ℤ, A.IsKFlat P →
      IsIso ((derivedRingedPullbackCounit H F).app P)) ∧
    ∃ (_ : (derivedRingedPullback H F).CommShift ℤ),
      (derivedRingedPullback H F).IsTriangulated := by
  sorry

end RingedPullback

section ScalarPullback
variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {τ : Sheaf K (Type r) ≌ Sheaf K (Type r)}
  {A B : Action σ} {A' B' : Action τ}

/-- A coefficient square over a geometric inverse image. The equality of the
set-valued functors and commuting comparisons means the same geometric morphism
is used on the two coefficient rings.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure CoefficientSquare (f : Map A B) (f' : Map A' B')
    (H : InverseImage A A') (I : InverseImage B B') : Prop where
  functor_eq : H.L = I.L
  comm_eq : HEq H.comm I.comm
  ring_square : HEq
    (H.algebraic.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map f'.hom)
    (I.L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map f.hom) ≫
      I.algebraic.ringUnderlying.hom)

/-- The canonical pullback/scalar comparison is determined by its tensor-unit
mate before deriving, and by the same cochain map after deriving.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ScalarPullbackComparison {f : Map A B} {f' : Map A' B'}
    (H : InverseImage A A') (I : InverseImage B B')
    (F : ScalarModel f) (G : ScalarModel f')
    (h : CoefficientSquare f f' H I) where
  restriction : f.eqRestrict ⋙ H.eqPullback ≅ I.eqPullback ⋙ f'.eqRestrict
  restriction_sets : ∀ M : B.EqMod,
    A'.moduleSets.map ((restriction.hom.app M).hom.f) =
      H.algebraic.moduleUnderlying.hom.app (f.restrict.obj M.carrier) ≫
        eqToHom (congrArg (fun L ↦ L.obj (B.moduleSets.obj M.carrier)) h.functor_eq) ≫
        I.algebraic.moduleUnderlying.inv.app M.carrier
  ordinary : F.E ⋙ I.eqPullback ≅ H.eqPullback ⋙ G.E
  unit : ∀ M : A.EqMod,
    H.eqPullback.map (F.adj.unit.app M) ≫ restriction.hom.app (F.E.obj M) ≫
      f'.eqRestrict.map (ordinary.hom.app M) = G.adj.unit.app (H.eqPullback.obj M)
  derived : F.T ⋙ I.eqPullback.mapDerivedCategory ≅ H.eqPullback.mapDerivedCategory ⋙ G.T
  normalized : IsNormalizedDerivedSquare F.E G.E H.eqPullback I.eqPullback
    F.T G.T F.ε G.ε ordinary derived A.IsKFlat

/-- Scalar extension commutes canonically with the constructed geometric inverse
image; further scalar extension gives derived inverse image for a general ringed
topos morphism, by the scalar-composition comparison.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: inverse image commutes with the coequalizer defining the balanced tensor.
The two scalar factors multiply and the inverse inserts 1. The coefficient square
makes these maps semilinear. Their restriction mate is the displayed unit equation,
which fixes the comparison. Pull back one flat-term K-flat resolution and use
preservation of K-flatness to localize this same balanced map. The localized
counit equation is precisely the displayed normalization. Multiplication of three
scalar factors proves its composition and identity compatibility before localization. -/
theorem scalarPullbackComparison_nonempty {f : Map A B} {f' : Map A' B'}
    (H : InverseImage A A') (I : InverseImage B B') (h : CoefficientSquare f f' H I)
    (F : ScalarModel f) (G : ScalarModel f') :
    Nonempty (ScalarPullbackComparison H I F G h) := by
  sorry

/-- Postcomposition with exact inverse image preserves finite limits of towers.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance InverseImage.towerLimits (I : InverseImage B B') :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B.EqMod B'.EqMod).obj
      I.eqPullback) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- Postcomposition with exact inverse image preserves finite colimits of towers.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance InverseImage.towerColimits (I : InverseImage B B') :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B.EqMod B'.EqMod).obj
      I.eqPullback) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- Pullback comparison for the entire derived inverse system, normalized before
localization by all quotient projections simultaneously.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ReductionPullbackComparison {f : Map A B} {f' : Map A' B'}
    (H : InverseImage A A') (I : InverseImage B B')
    {F : ScalarModel f} {G : ScalarModel f'}
    {h : CoefficientSquare f f' H I} (S : ScalarPullbackComparison H I F G h) (l : ℕ)
    (R : ReductionModel l F) (R' : ReductionModel l G) where
  ordinary : R.E ⋙ (Functor.whiskeringRight ℕᵒᵖ B.EqMod B'.EqMod).obj I.eqPullback ≅
    H.eqPullback ⋙ R'.E
  projections : ∀ (n : ℕ) (M : A.EqMod),
    I.eqPullback.map ((R.π n).app M) ≫ (ordinary.hom.app M).app (op n) =
      S.ordinary.hom.app M ≫ (R'.π n).app (H.eqPullback.obj M)
  derived : R.T ⋙ ((Functor.whiskeringRight ℕᵒᵖ B.EqMod B'.EqMod).obj
      I.eqPullback).mapDerivedCategory ≅ H.eqPullback.mapDerivedCategory ⋙ R'.T
  normalized : IsNormalizedDerivedSquare R.E R'.E H.eqPullback
    ((Functor.whiskeringRight ℕᵒᵖ B.EqMod B'.EqMod).obj I.eqPullback)
    R.T R'.T R.ε R'.ε ordinary derived A.IsKFlat

/-- The single simultaneous reduction commutes with pullback, including its
transitions, rather than only after applying each evaluation.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: exact inverse image carries each multiplication cokernel and its quotient
projection to the corresponding cokernel. The scalar comparison therefore induces
a natural isomorphism of whole strict towers satisfying the projection equations.
The quotient equations force every transition square. Pulling back the common
K-flat resolution computes both functors, so the tower comparison localizes
with the displayed cochain normalization. -/
theorem reductionPullbackComparison_nonempty {f : Map A B} {f' : Map A' B'}
    (H : InverseImage A A') (I : InverseImage B B')
    {F : ScalarModel f} {G : ScalarModel f'} {h : CoefficientSquare f f' H I} (S :
      ScalarPullbackComparison H I F G h)
    (l : ℕ) (R : ReductionModel l F) (R' : ReductionModel l G) :
    Nonempty (ReductionPullbackComparison H I S l R R') := by
  sorry

end ScalarPullback


section Forgetting
variable {A B : Action σ} {f : Map A B} (F : ScalarModel f)

/-- Postcomposition with exact fixed-pair forgetting preserves finite limits.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance Action.towerForget_limits (A : Action σ) :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A.EqMod A.Mod).obj A.forget) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Postcomposition with exact fixed-pair forgetting preserves finite colimits.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance Action.towerForget_colimits (A : Action σ) :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A.EqMod A.Mod).obj A.forget) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The ordinary simultaneous reduction and the comparison after forgetting the
semilinear structure. Both the strict projections and the derived whole-system
comparison are normalized, so forgetting preserves the canonical comparisons.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ReductionForgetting (l : ℕ) (R : ReductionModel l F) where
  E : A.Mod ⥤ (ℕᵒᵖ ⥤ B.Mod)
  [additive : E.Additive]
  π : ∀ n : ℕ, F.ordinary.E ⟶ E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.Mod).obj (op n)
  zero : ∀ (n : ℕ) (M : A.Mod),
    (l ^ (n + 1) • 𝟙 (F.ordinary.E.obj M)) ≫ (π n).app M = 0
  quotient : ∀ (n : ℕ) (M : A.Mod),
    IsColimit (CokernelCofork.ofπ ((π n).app M) (zero n M))
  transition : ∀ (n : ℕ) (M : A.Mod),
    (π (n + 1)).app M ≫ (E.obj M).map (homOfLE n.le_succ).op = (π n).app M
  ordinary : R.E ⋙ (Functor.whiskeringRight ℕᵒᵖ B.EqMod B.Mod).obj B.forget ≅ A.forget ⋙ E
  projections : ∀ (n : ℕ) (M : A.EqMod),
    B.forget.map ((R.π n).app M) ≫ (ordinary.hom.app M).app (op n) =
      F.underlying.hom.app M ≫ (π n).app M.carrier
  T : DerivedCategory A.Mod ⥤ DerivedCategory (ℕᵒᵖ ⥤ B.Mod)
  ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A.Mod (.up ℤ))
  computes : ∀ P : CochainComplex A.Mod ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := A.ring) P → IsIso (ε.app P)
  derived : R.T ⋙ ((Functor.whiskeringRight ℕᵒᵖ B.EqMod B.Mod).obj
    B.forget).mapDerivedCategory ≅ A.forget.mapDerivedCategory ⋙ T
  normalized : IsNormalizedDerivedSquare R.E E A.forget
    ((Functor.whiskeringRight ℕᵒᵖ B.EqMod B.Mod).obj B.forget)
    R.T T R.ε ε ordinary derived A.IsKFlat

/-- Exact forgetting commutes with the one simultaneous derived reduction functor.
Source: blueprint (2)-(4) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: ordinary forgetting creates the multiplication cokernels and the quotient
transitions. Use ordinary scalar extension and these same quotients to construct
the nonequivariant strict system. A single equivariant K-flat complex is ordinary
K-flat after forgetting, so it computes both systems and their maps. Localization
of the projection-preserving ordinary comparison gives the displayed normalized
whole-system isomorphism. All scalar comparisons agree before localization by
their pure-tensor formulas; the positive Kummer equation is preserved by exact
forgetting, including its single and shift comparisons. -/
theorem reductionForgetting_nonempty (l : ℕ) (R : ReductionModel l F) :
    Nonempty (ReductionForgetting F l R) := by
  sorry

end Forgetting

/-- The whole-system forgetting square, written for arbitrary exact transports so
that its equation does not repeatedly unfold the large coefficient presentations.
Source: blueprint (3)-(4), node proof Step 12
(blueprint: lem-pur-equivariant-reduction-calculus). -/
@[irreducible] def IsForgettingKummerSquare
    {A₀ : Type a₀} [Category.{h₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀]
    {B₀ : Type b₀} [Category.{k₀} B₀] [Abelian B₀] [HasDerivedCategory.{z₀} B₀]
    {A₁ : Type a₁} [Category.{h₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
    {B₁ : Type b₁} [Category.{k₁} B₁] [Abelian B₁] [HasDerivedCategory.{z₁} B₁]
    (L : A₀ ⥤ A₁) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (V : B₀ ⥤ B₁) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : DerivedCategory A₀ ⥤ DerivedCategory B₀)
    (G : DerivedCategory A₁ ⥤ DerivedCategory B₁)
    (d : F ⋙ V.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ G)
    (X : DerivedCategory A₀) (N : B₀)
    (i : F.obj X ≅ ((DerivedCategory.singleFunctor B₀ 0).obj N)⟦(2 : ℤ)⟧)
    (e : G.obj (L.mapDerivedCategory.obj X) ≅
      ((DerivedCategory.singleFunctor B₁ 0).obj (V.obj N))⟦(2 : ℤ)⟧) : Prop :=
  d.hom.app X ≫ e.hom =
    V.mapDerivedCategory.map i.hom ≫
      (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor B₀ 0).obj N) ≫
      ((V.mapDerivedCategorySingleFunctor 0).hom.app N)⟦(2 : ℤ)⟧'

/-- The positive Kummer boundary equation after exact forgetting, including the
canonical single, shift and shift-addition maps. The sequence on the right is the
image of the original short exact sequence under the exact functor.
Source: blueprint (3)-(4), node proof Steps 10--12
(blueprint: lem-pur-equivariant-reduction-calculus). -/
@[irreducible] def IsPositiveBoundaryAfterForgetting
    {A₀ : Type a₀} [Category.{h₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀]
    {A₁ : Type a₁} [Category.{h₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
    (L : A₀ ⥤ A₁) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {S : ShortComplex A₀} (hS : S.ShortExact)
    (b : ((DerivedCategory.singleFunctor A₀ 0).obj S.X₃)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A₀ 0).obj S.X₁)⟦(2 : ℤ)⟧) : Prop :=
  ((L.mapDerivedCategorySingleFunctor 0).inv.app S.X₃)⟦(1 : ℤ)⟧' ≫
      (L.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor A₀ 0).obj S.X₃) ≫
      L.mapDerivedCategory.map b ≫
      (L.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor A₀ 0).obj S.X₁) ≫
      ((L.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(2 : ℤ)⟧' =
    (ShortComplex.ShortExact.singleδ (hS.map_of_exact L))⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory A₁) (1 : ℤ) 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor A₁ 0).obj (L.obj S.X₁))

/-- The forgotten whole-system Kummer isomorphism, together with its comparison
square and the positive boundary equation in the ordinary derived category.
The boundary is that of the actual short exact sequence obtained by exact forgetting.
Source: blueprint (3)-(4), node proof Step 12
(blueprint: lem-pur-equivariant-reduction-calculus). -/
structure KummerForgettingComparison (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] {P : IntegralCoefficients.{t + 1, t, t + 1} (σ := τ) l}
    (R : IntegralReductionModel.{t + 1, t, t + 1} l P) (K : KummerPresentation T g τ s l P)
    (I : KummerModel T g τ s l R K) (D : ReductionForgetting R.scalar l R.system) where
  iso : D.T.obj (P.Z.forget.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj K.G)⟦(1 : ℤ)⟧)) ≅
    ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} (ℕᵒᵖ ⥤ P.C.Mod) 0).obj
      (K.U ⋙ P.C.forget))⟦(2 : ℤ)⟧
  commutes : IsForgettingKummerSquare P.Z.forget
    ((Functor.whiskeringRight ℕᵒᵖ P.C.EqMod P.C.Mod).obj P.C.forget)
    R.system.T D.T D.derived
    (((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj K.G)⟦(1 : ℤ)⟧)
    K.U I.iso iso
  positive : ∀ n : ℕ, IsPositiveBoundaryAfterForgetting P.Z.forget (K.exact n)
    ((R.system.unit n).app
        (((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.Z.EqMod 0).obj
          K.G)⟦(1 : ℤ)⟧) ≫
      P.scalar.eqRestrict.mapDerivedCategory.map (I.level n).hom ≫
      (P.scalar.eqRestrict.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor.{t + 2, t + 1, t + 2} P.C.EqMod 0).obj
          (K.U.obj (op n))) ≫
      ((P.scalar.eqRestrict.mapDerivedCategorySingleFunctor 0).hom.app
        (K.U.obj (op n)))⟦(2 : ℤ)⟧')

universe w w'

set_option backward.defeqAttrib.useBackward true in
/-- Shift compatibility carries a shifted degree-one map through shift addition.
Source: Mathlib's `Functor.commShiftIso_add'`; node proof Step 12
(blueprint: lem-pur-equivariant-reduction-calculus). -/
@[reassoc] private theorem map_shift_boundary
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {X Y : C} (f : X ⟶ Y⟦(1 : ℤ)⟧) :
    (F.commShiftIso (1 : ℤ)).inv.app X ≫
      F.map (f⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Y) ≫
      (F.commShiftIso (2 : ℤ)).hom.app Y =
    (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app Y)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' D (1 : ℤ) 1 2 rfl).inv.app (F.obj Y) := by
  rw [F.commShiftIso_add' (show (1 : ℤ) + 1 = 2 from rfl)]
  simp only [Functor.CommShift.isoAdd'_hom_app, Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc ((shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Y)
    ((shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).hom.app Y)]
  simp only [Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [F.commShiftIso_hom_naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
/-- Exact forgetting carries the positive shifted connecting morphism to that of
its image short exact sequence. Apply exact-functor boundary naturality, commute
with shift addition, and use the degree-zero single comparisons.
Source: Mathlib's `ShortComplex.ShortExact.mapShiftedHom_singleδ'`;
node proof Step 12 (blueprint: lem-pur-equivariant-reduction-calculus). -/
private theorem boundary_after_forgetting
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {S : ShortComplex C} (hS : S.ShortExact) :
    ((L.mapDerivedCategorySingleFunctor 0).inv.app S.X₃)⟦(1 : ℤ)⟧' ≫
      (L.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor C 0).obj S.X₃) ≫
      L.mapDerivedCategory.map
        (hS.singleδ⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 rfl).inv.app
            ((DerivedCategory.singleFunctor C 0).obj S.X₁)) ≫
      (L.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor C 0).obj S.X₁) ≫
      ((L.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(2 : ℤ)⟧' =
    (hS.map_of_exact L).singleδ⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory D) (1 : ℤ) 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor D 0).obj (L.obj S.X₁)) := by
  let δ : (DerivedCategory.singleFunctor D 0).obj (L.obj S.X₃) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (L.obj S.X₁))⟦(1 : ℤ)⟧ :=
    (hS.map_of_exact L).singleδ
  have h := hS.mapShiftedHom_singleδ' L
  change _ = δ at h
  change _ = δ⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd' (DerivedCategory D) (1 : ℤ) 1 2 rfl).inv.app
      ((DerivedCategory.singleFunctor D 0).obj (L.obj S.X₁))
  clear_value δ
  dsimp only [ShiftedHom.map] at h
  simp only [Category.assoc] at h
  rw [map_shift_boundary_assoc]
  erw [← (shiftFunctorAdd' (DerivedCategory D) (1 : ℤ) 1 2 rfl).inv.naturality]
  simp only [Functor.comp_map]
  erw [← (shiftFunctor (DerivedCategory D) (1 : ℤ)).map_comp_assoc,
    ← (shiftFunctor (DerivedCategory D) (1 : ℤ)).map_comp_assoc]
  simp only [Category.assoc]
  rw [h]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Substitute a given positive-boundary normalization before exact forgetting.
Source: node proof Step 12 (blueprint: lem-pur-equivariant-reduction-calculus). -/
private theorem boundary_after_forgetting_eq
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {S : ShortComplex C} (hS : S.ShortExact)
    (b : ((DerivedCategory.singleFunctor C 0).obj S.X₃)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor C 0).obj S.X₁)⟦(2 : ℤ)⟧)
    (hb : b = hS.singleδ⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor C 0).obj S.X₁)) :
    IsPositiveBoundaryAfterForgetting L hS b := by
  unfold IsPositiveBoundaryAfterForgetting
  rw [hb]
  exact boundary_after_forgetting L hS


/-- Construct the ordinary comparison by cancelling the given derived-system comparison.
Source: node proof Step 12 (blueprint: lem-pur-equivariant-reduction-calculus). -/
private theorem forgetting_square
    {A₀ : Type a₀} [Category.{h₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀]
    {B₀ : Type b₀} [Category.{k₀} B₀] [Abelian B₀] [HasDerivedCategory.{z₀} B₀]
    {A₁ : Type a₁} [Category.{h₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
    {B₁ : Type b₁} [Category.{k₁} B₁] [Abelian B₁] [HasDerivedCategory.{z₁} B₁]
    (L : A₀ ⥤ A₁) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (V : B₀ ⥤ B₁) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : DerivedCategory A₀ ⥤ DerivedCategory B₀)
    (G : DerivedCategory A₁ ⥤ DerivedCategory B₁)
    (d : F ⋙ V.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ G)
    (X : DerivedCategory A₀) (N : B₀)
    (i : F.obj X ≅ ((DerivedCategory.singleFunctor B₀ 0).obj N)⟦(2 : ℤ)⟧)
    : ∃ e : G.obj (L.mapDerivedCategory.obj X) ≅
        ((DerivedCategory.singleFunctor B₁ 0).obj (V.obj N))⟦(2 : ℤ)⟧,
      IsForgettingKummerSquare L V F G d X N i e := by
  let e := (d.app X).symm ≪≫ V.mapDerivedCategory.mapIso i ≪≫
    (V.mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor B₀ 0).obj N) ≪≫
    (shiftFunctor (DerivedCategory B₁) (2 : ℤ)).mapIso
      ((V.mapDerivedCategorySingleFunctor 0).app N)
  refine ⟨e, ?_⟩
  unfold IsForgettingKummerSquare
  simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, Iso.app_hom, Iso.hom_inv_id_app_assoc]


set_option maxHeartbeats 1000000 in
-- The concrete Kummer square unfolds large derived functor expressions.
/-- Kummer identification and positive scalar-unit normalization commute with
exact forgetting through the normalized simultaneous-reduction comparison.
Source: blueprint (3)-(4), node proof Step 12
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: use the common equivariant K-flat resolution in ReductionForgetting.normalized.
Exact forgetting preserves the truncation kernels, cohomology quotients and both
quasi-isomorphisms in the whole-system truncation roof of node proof Step 11.
This identifies its ordinary Kummer isomorphism with the image of I.iso through
D.derived, giving commutes as an equation of morphisms of entire derived towers.
For each level, forgetting the short exact Kummer sequence preserves its canonical
connecting map. Apply this exact-functor boundary comparison to I.positive, and
insert Mathlib's canonical single and shift comparisons. Compatibility
of these comparisons with shift addition gives precisely positive, retaining the
plus sign and the power transitions. No faithfulness of derived forgetting is used. -/
theorem kummer_forgetting (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] {P : IntegralCoefficients.{t + 1, t, t + 1} (σ := τ) l}
    (R : IntegralReductionModel.{t + 1, t, t + 1} l P) (K : KummerPresentation T g τ s l P)
    (I : KummerModel T g τ s l R K) (D : ReductionForgetting R.scalar l R.system) :
    Nonempty (KummerForgettingComparison T g τ s l R K I D) := by
  let V := (Functor.whiskeringRight ℕᵒᵖ P.C.EqMod P.C.Mod).obj P.C.forget
  let X := ((DerivedCategory.singleFunctor P.Z.EqMod 0).obj K.G)⟦(1 : ℤ)⟧
  obtain ⟨e, he⟩ := forgetting_square P.Z.forget V R.system.T D.T D.derived X K.U I.iso
  refine ⟨{ iso := e, commutes := he, positive := ?_ }⟩
  intro n
  exact boundary_after_forgetting_eq P.Z.forget (K.exact n) _ (I.positive n)


set_option backward.defeqAttrib.useBackward true in
/-- Canonical commutation of abelian inverse image with underlying sets, normalized
by the two recorded inverse-image units. The direct images commute with forgetting
by their sectionwise definition.
Source: Stacks 03D2, 03PL (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: inverse image preserves finite limits and colimits, hence the group operation
graphs. The inverse image of the underlying set sheaf therefore carries precisely
the inverse-image abelian group. The adjunction units fix the comparison uniquely;
the analogous construction with the inverse comparison supplies its inverse. -/
theorem abelianSetsComparison_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! e : Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{t + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (CategoryTheory.forget AddCommGrpCat.{t + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y)
        (CategoryTheory.forget AddCommGrpCat.{t + 1}) ⋙
          Scheme.proEtaleSheafInverseImage f (Type (t + 1)),
      ∀ M : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{t + 1},
        (Scheme.proEtaleSheafAdjunction f (Type (t + 1))).unit.app
            ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj M) ≫
          (Scheme.proEtaleSheafDirectImage f (Type (t + 1))).map (e.inv.app M) =
        (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
          ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{t + 1}).unit.app M) := by
  let : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : PreservesFilteredColimitsOfSize.{t, t + 1}
      (CategoryTheory.forget AddCommGrpCat.{t + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, t + 1, t, t + 1} _
  let e := sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{t + 1})
  have he : ∀ M : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{t + 1},
      (Scheme.proEtaleSheafAdjunction f (Type (t + 1))).unit.app
          ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj M) ≫
        (Scheme.proEtaleSheafDirectImage f (Type (t + 1))).map (e.inv.app M) =
      (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
        ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{t + 1}).unit.app M) := by
    intro M
    have h : (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
          ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{t + 1}).unit.app M) ≫
        (Scheme.proEtaleSheafDirectImage f (Type (t + 1))).map (e.hom.app M) =
      (Scheme.proEtaleSheafAdjunction f (Type (t + 1))).unit.app
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj M) :=
      sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (Scheme.proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{t + 1}) M
    clear_value e
    rw [← h, Category.assoc, ← Functor.map_comp, e.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  clear_value e
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  apply ((Scheme.proEtaleSheafAdjunction f (Type (t + 1))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (he' M).trans (he M).symm


/-- The unit-normalized underlying-set comparison of abelian inverse image.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus). -/
def abelianSetsComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (abelianSetsComparison_existsUnique f).exists.choose

/-- Canonical pullback data for the two Kummer presentations. All maps are pinned
to the recorded scheme pullback of full units and roots, and all inverse images
are pinned on underlying sets. The square is the map of Kummer sequences.
Source: Stacks 03PL, blueprint (2)-(4)
(blueprint: lem-pur-equivariant-reduction-calculus). -/
structure KummerPullbackData {X Y : Scheme.{t}} (f : X ⟶ Y)
    (gX : X ≅ X) (gY : Y ≅ Y)
    (τX : Sheaf (Scheme.ProEt.topology X) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology X) (Type (t + 1)))
    (τY : Sheaf (Scheme.ProEt.topology Y) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology Y) (Type (t + 1)))
    (sX : τX.functor ≅ Scheme.isoSectionwiseInverseImage gX.hom (Type (t + 1)))
    (sY : τY.functor ≅ Scheme.isoSectionwiseInverseImage gY.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime]
    {PX : IntegralCoefficients (σ := τX) l} {PY : IntegralCoefficients (σ := τY) l}
    (RX : IntegralReductionModel l PX) (RY : IntegralReductionModel l PY)
    (KX : KummerPresentation X gX τX sX l PX) (KY : KummerPresentation Y gY τY sY l PY) where
  Z : InverseImage PY.Z PX.Z
  C : InverseImage PY.C PX.C
  square : CoefficientSquare PY.scalar PX.scalar Z C
  topos : Z.L ≅ Scheme.proEtaleSheafInverseImage f (Type (t + 1))
  scalar : ScalarPullbackComparison Z C RY.scalar RX.scalar square
  system : ReductionPullbackComparison Z C scalar l RY.system RX.system
  abZ : Z.eqPullback ⋙ PX.Z.ab ≅ PY.Z.ab ⋙
    Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{t + 1}
  abZ_sets : ∀ M : PY.Z.EqMod,
    (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
        (abZ.hom.app M) =
      Z.algebraic.moduleUnderlying.hom.app M.carrier ≫
        topos.hom.app (PY.Z.moduleSets.obj M.carrier) ≫
        (abelianSetsComparison f).inv.app (PY.Z.ab.obj M)
  abC : C.eqPullback ⋙ PX.C.ab ≅ PY.C.ab ⋙
    Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{t + 1}
  abC_sets : ∀ M : PY.C.EqMod,
    (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
        (abC.hom.app M) =
      C.algebraic.moduleUnderlying.hom.app M.carrier ≫
        eqToHom (congrArg (fun L ↦ L.obj (PY.C.moduleSets.obj M.carrier))
          square.functor_eq.symm) ≫
        topos.hom.app (PY.C.moduleSets.obj M.carrier) ≫
        (abelianSetsComparison f).inv.app (PY.C.ab.obj M)
  units : Z.eqPullback.obj KY.G ⟶ KX.G
  units_eq : PX.Z.ab.map units ≫ KX.units.hom =
    abZ.hom.app KY.G ≫
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{t + 1}).map KY.units.hom ≫
      (AlgebraicGeometry.ProEtale.SpTowerClasses.unitsPull f).app (op 0)
  roots : ((Functor.whiskeringRight ℕᵒᵖ PY.C.EqMod PX.C.EqMod).obj
    C.eqPullback).obj KY.U ⟶ KX.U
  roots_eq : ∀ n : ℕ, PX.C.ab.map (roots.app (op n)) ≫ KX.roots.hom.app (op n) =
    abC.hom.app (KY.U.obj (op n)) ≫
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{t + 1}).map
        (KY.roots.hom.app (op n)) ≫
      Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1))
  kummer_square : ∀ n : ℕ, Z.eqPullback.map (KY.inclusion n) ≫ units =
    scalar.restriction.hom.app (KY.U.obj (op n)) ≫
      PX.scalar.eqRestrict.map (roots.app (op n)) ≫ KX.inclusion n

/-- The canonical pullback maps lift equivariantly and give a morphism of the
single strict Kummer systems. No isomorphism assertion is made for full units.
Source: Stacks 03PL, blueprint (2)-(4)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the commuting scheme square gives the commuting inverse-image comparison
by base change of charts. Constant coefficients and their quotient maps pull back
canonically, providing the algebraic inverse-image graphs and the coefficient
square. The general scalar and reduction pullback theorems give their normalized
comparisons. Forgetting module structure gives the unit-normalized abelian
inverse-image comparisons. Pull units back along the projection of each
base-changed chart, as in the recorded unitsPull morphism; this commutes with
powers and the scheme automorphisms. Restrict to each recorded root kernel.
The kernel universal property identifies the result with the recorded roots
inverse-image map, and also forces all power-transition squares. Faithful
underlying forgetting gives the equivariant Kummer square. -/
theorem kummerPullbackData_nonempty {X Y : Scheme.{t}} (f : X ⟶ Y)
    (gX : X ≅ X) (gY : Y ≅ Y) (hf : gX.hom ≫ f = f ≫ gY.hom)
    (τX : Sheaf (Scheme.ProEt.topology X) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology X) (Type (t + 1)))
    (τY : Sheaf (Scheme.ProEt.topology Y) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology Y) (Type (t + 1)))
    (sX : τX.functor ≅ Scheme.isoSectionwiseInverseImage gX.hom (Type (t + 1)))
    (sY : τY.functor ≅ Scheme.isoSectionwiseInverseImage gY.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime]
    {PX : IntegralCoefficients (σ := τX) l} {PY : IntegralCoefficients (σ := τY) l}
    (RX : IntegralReductionModel l PX) (RY : IntegralReductionModel l PY)
    (KX : KummerPresentation X gX τX sX l PX) (KY : KummerPresentation Y gY τY sY l PY) :
    Nonempty (KummerPullbackData f gX gY τX τY sX sY l RX RY KX KY) := by
  sorry

/-- The positive Kummer identification commutes with the canonical pullback
morphism on units, as an equality in the derived category of whole systems.
Source: Stacks 03PL, blueprint (2)-(4)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the pullback Kummer square is a map of short exact sequences, so the
positive connecting morphisms commute. Its power-transition squares make this
one map of systems. Apply the cochain normalization of the reduction comparison
on the common resolving complex. The two maps to the root system agree under
the positive cone identification, hence agree after localization, with the
canonical single and shift comparisons displayed below. Exact forgetting
preserves the same equations and the underlying maps are the specified ones. -/
theorem kummer_pullback {X Y : Scheme.{t}} (f : X ⟶ Y)
    (gX : X ≅ X) (gY : Y ≅ Y)
    (τX : Sheaf (Scheme.ProEt.topology X) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology X) (Type (t + 1)))
    (τY : Sheaf (Scheme.ProEt.topology Y) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology Y) (Type (t + 1)))
    (sX : τX.functor ≅ Scheme.isoSectionwiseInverseImage gX.hom (Type (t + 1)))
    (sY : τY.functor ≅ Scheme.isoSectionwiseInverseImage gY.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime]
    {PX : IntegralCoefficients (σ := τX) l} {PY : IntegralCoefficients (σ := τY) l}
    (RX : IntegralReductionModel l PX) (RY : IntegralReductionModel l PY)
    (KX : KummerPresentation X gX τX sX l PX) (KY : KummerPresentation Y gY τY sY l PY)
    (IX : KummerModel X gX τX sX l RX KX) (IY : KummerModel Y gY τY sY l RY KY)
    (H : KummerPullbackData f gX gY τX τY sX sY l RX RY KX KY) :
    ((Functor.whiskeringRight ℕᵒᵖ PY.C.EqMod PX.C.EqMod).obj
        H.C.eqPullback).mapDerivedCategory.map IY.iso.hom ≫
      (((Functor.whiskeringRight ℕᵒᵖ PY.C.EqMod PX.C.EqMod).obj
        H.C.eqPullback).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ PY.C.EqMod) 0).obj KY.U) ≫
      ((((Functor.whiskeringRight ℕᵒᵖ PY.C.EqMod PX.C.EqMod).obj
        H.C.eqPullback).mapDerivedCategorySingleFunctor 0).hom.app KY.U)⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ PX.C.EqMod) 0).map H.roots)⟦(2 : ℤ)⟧' =
    H.system.derived.hom.app
        (((DerivedCategory.singleFunctor PY.Z.EqMod 0).obj KY.G)⟦(1 : ℤ)⟧) ≫
      RX.system.T.map
        ((H.Z.eqPullback.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor PY.Z.EqMod 0).obj KY.G) ≫
          ((H.Z.eqPullback.mapDerivedCategorySingleFunctor 0).hom.app KY.G)⟦(1 : ℤ)⟧' ≫
          ((DerivedCategory.singleFunctor PX.Z.EqMod 0).map H.units)⟦(1 : ℤ)⟧') ≫
      IX.iso.hom := by
  sorry

end SheafOfModules.EquivariantReduction
