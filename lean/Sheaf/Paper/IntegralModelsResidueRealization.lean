/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module
public import Sheaf.Paper.IntegralModelsDefinitions
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.CategoryTheory.ConstantRingModuleSheaves
/-! # Exactness of the canonical finite residue realization

Source: Stacks Tags 00YV, 03CY and 09AL; integral models, proof step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SixFunctors
namespace AlgebraicGeometry.ProEtale
private theorem fixedScalars_preservesFiniteLimits (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    PreservesFiniteLimits (integralModelFixedScalars X A) := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let F := integralModelFixedScalars X A
  let G := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} (ULift.{u, 0} A))) Ab.{u + 1})
  have : PreservesFiniteLimits (F ⋙ G) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u + 1} (continuousMapRingSheaf X A)))
  have : PreservesFiniteLimits G := by
    obtain ⟨e, _, _, _, he⟩ :=
      (constant_ring_module_sheaves (Scheme.ProEt.topology X)
        (ULift.{u + 1, u} (ULift.{u, 0} A))).1
    dsimp only [G]
    rw [← he]
    infer_instance
  have : ReflectsFiniteLimits G :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteLimits_of_reflects_of_preserves F G
private theorem fixedScalars_preservesFiniteColimits (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    PreservesFiniteColimits (integralModelFixedScalars X A) := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let F := integralModelFixedScalars X A
  let G := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} (ULift.{u, 0} A))) Ab.{u + 1})
  have : PreservesFiniteColimits (F ⋙ G) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u + 1} (continuousMapRingSheaf X A)))
  have : PreservesFiniteColimits G := by
    obtain ⟨e, _, _, _, he⟩ :=
      (constant_ring_module_sheaves (Scheme.ProEt.topology X)
        (ULift.{u + 1, u} (ULift.{u, 0} A))).1
    dsimp only [G]
    rw [← he]
    infer_instance
  have : ReflectsFiniteColimits G :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves F G
/-- The specified continuous-to-intrinsic realization of finite discrete coefficients
is exact. The scalar restriction is the actual constant-function action.

Source: Stacks Tags 00YV, 03CY and 09AL; blueprint integral models, proof step 5.
(blueprint: lem-sfb-embedded-integral-residue-realization-exact).

Proof: forget fixed scalar module sheaves to additive sheaves. The constant-ring
module equivalence identifies this forgetful functor with the module forgetful functor
after an equivalence, hence it preserves finite limits and colimits. It reflects them
because it reflects isomorphisms. The composite with constant-scalar restriction is
exactly the original additive forgetful functor. Reflection thus proves exactness of
restriction itself. The continuous section-action encoding and the intrinsic finite-ring
realization are equivalences, hence exact. Compose these three exact functors. -/
theorem integralModelIntrinsicRealization_exact (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    [DiscreteTopology A] :
    PreservesFiniteLimits (integralModelIntrinsicRealization X A) ∧
      PreservesFiniteColimits (integralModelIntrinsicRealization X A) := by
  have := fixedScalars_preservesFiniteLimits X A
  have := fixedScalars_preservesFiniteColimits X A
  unfold integralModelIntrinsicRealization
  constructor <;> infer_instance

/-- The termwise derived functor of the specified finite residue realization.
The exactness instances are fixed explicitly, so uses do not repeat their elaboration.

Source: Stacks Tags 00YV and 09AL; integral models, proof step 5.
(blueprint: lem-sfb-embedded-integral-residue-realization-exact). -/
def integralModelIntrinsicDerivedRealization (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    [DiscreteTopology A] :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) ⥤
        Scheme.proEtaleDerivedCategory X (ULift.{u, 0} A) := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let F := integralModelIntrinsicRealization X A
  letI : PreservesFiniteLimits F := (integralModelIntrinsicRealization_exact X A).1
  letI : PreservesFiniteColimits F := (integralModelIntrinsicRealization_exact X A).2
  exact F.mapDerivedCategory

/-- The specified first reduction, with its source and target module categories fixed
before deriving the scalar extension.

Source: integral models, proof step 4, and Stacks Tag 099I.
(blueprint: lem-sfb-embedded-integral-residue-realization-exact). -/
def integralModelFirstDerivedReduction (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1) :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E)) ⥤
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (completedResidue ℓ E π 0)) X)) := by
  let q : integralCoefficientObject X ℓ E ⟶
      condensedRingObj (Profinite.continuousMapRingObj (completedResidue ℓ E π 0)) X :=
    (integralModelReductionMap.{u} X ℓ E π 1).hom
  letI : IsMonHom q := by
    dsimp only [q]
    infer_instance
  exact (Mod.extendScalars q).leftDerivedFunctor

/-- Constructible cohomology and finite relative Tor amplitude of the first constant
residue reduction. Completeness is a separate condition.

Source: Stacks Tag 09C1; integral models, proof steps 4--5.
(blueprint: lem-sfb-embedded-integral-residue-realization-exact). -/
def integralModelConstantResidueCondition (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1) :
    ObjectProperty (DerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (IntegralModelsEmbedded.discreteObj.{u}
          (PadicAlgCl.integers ℓ E.1)) X))) :=
  fun L ↦
    let R := (Mod.extendScalars
      (IntegralModelsEmbedded.residueMap ℓ E π X)).leftDerivedFunctor.obj L
    (∀ i : ℤ, IsConstantModelConstructible
      (IntegralModelsEmbedded.discreteObj.{u} (completedResidue ℓ E π 0)) X
      ((DerivedCategory.homologyFunctor _ i).obj R)) ∧
    DerivedCategory.finiteTorAmplitude _ R

/-- Constructible cohomology in one ordered finite interval in the canonical
intrinsic constant-ring presentation.

Source: Stacks Tag 09AL; integral models, proof step 5.
(blueprint: lem-sfb-embedded-integral-residue-realization-exact). -/
def integralModelIntrinsicBoundedConstructible (X : Scheme.{u}) (A : Type)
    [CommRing A] [Finite A] :
    ObjectProperty (Scheme.proEtaleDerivedCategory X (ULift.{u, 0} A)) := by
  letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  exact fun R ↦
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X (ULift.{u, 0} A)
      ((DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X
          (ULift.{u, 0} A))) i).obj R)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X
          (ULift.{u, 0} A))) i).obj R)

end AlgebraicGeometry.ProEtale
