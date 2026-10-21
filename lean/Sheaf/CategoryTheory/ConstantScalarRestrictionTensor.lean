/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.SheafTensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Monoidal.DerivedBraided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.BraidedSheafTensorGenerators
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Constant scalar restriction and tensor products

Source: Stacks Project, Modules on Sites, Tags 03CY and 0GMW, and Cohomology on Sites,
Tags 06YN, 06YP, 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).

The coefficient-sized small site implements the size convention. The restriction is the
existing literal restriction along the constant commutative-ring sheafification unit.

## Main statements

* `ordinary_exists`: normalized ordinary symmetric monoidal equivalence.
* `total_symmetry`: coherence of the existing canonical signed-total comparison.
* `flat_iff`, `kflat_iff`: preservation and reflection of the two flatness conditions.
* `derived_comparison`: the normalized coherent comparison on unbounded derived tensors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v wR wB dU dV dW

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.ConstantScalarRestriction

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (B : Type (max u v)) [CommRing B]

/-- The specified constant commutative ring sheaf, not an arbitrary coefficient ring.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ring := (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of B)

/-- The existing ringed-site module category at the constant ring.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
abbrev Modules := SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B))

/-- Exact fixed-coefficient sheafification, transported from the small model of the site.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedSheafify : HasSheafify J (ModuleCat.{max u v} B) :=
  letI : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (CategoryTheory.forget (ModuleCat.{max u v} B)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := B)
  letI : HasSheafify ((equivSmallModel.{max u v} C).inverse.inducedTopology J)
      (ModuleCat.{max u v} B) :=
    inferInstance
  hasSheafifyEssentiallySmallSite J (ModuleCat.{max u v} B)

/-- The existing fixed-coefficient sheaf category.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
abbrev Fixed := Sheaf J (ModuleCat.{max u v} B)

/-- Cache the existing abelian structure of module sheaves.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringAbelian : Abelian (Modules J B) := inferInstance

/-- Cache the abelian structure supplied by exact sheafification.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedAbelian : Abelian (Fixed J B) := inferInstance

/-- Use the additive structure of this same abelian category throughout.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringPreadditive : Preadditive (Modules J B) :=
  (ringAbelian J B).toPreadditive

/-- Use the additive structure of the fixed-coefficient abelian category throughout.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedPreadditive : Preadditive (Fixed J B) :=
  (fixedAbelian J B).toPreadditive

/-- The canonical additive zero morphisms, used uniformly in complex constructions.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringZeroMorphisms : HasZeroMorphisms (Modules J B) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The canonical additive zero morphisms on fixed-coefficient module sheaves.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedZeroMorphisms : HasZeroMorphisms (Fixed J B) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The recorded restriction, with precisely the action induced by the sheafification unit.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def restriction : Modules J B ⥤ Fixed J B :=
  SheafOfModules.restrictScalars
    ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
      (CommRingCat.of B)) ⋙ constantRingModuleRestriction J B

/-- Use the recorded sheafified objectwise tensor structure.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedMonoidal : MonoidalCategory (Fixed J B) :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).monoidal

/-- Use the symmetry of that same sheafified tensor.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedSymmetric : SymmetricCategory (Fixed J B) :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).symmetric

/-- Closedness of the recorded tensor, characterized by its tensor--Hom adjunction.
Source: sk-def-sfb-sheaf-tensor (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedClosed : MonoidalClosed (Fixed J B) :=
  (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).2.1.some

/-- Tensoring preserves the coproducts used in the signed total.
Source: sk-def-sfb-sheaf-tensor (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedLeftColimits (M : Fixed J B) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).2.2 M |>.1

/-- Tensoring on the other side preserves those coproducts.
Source: sk-def-sfb-sheaf-tensor (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedRightColimits (M : Fixed J B) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).2.2 M |>.2.1

/-- Cache additivity of the recorded sheaf tensor.
Source: blueprint sk-def-sfb-sheaf-tensor
(blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedTensorAdditive : MonoidalPreadditive (Fixed J B) :=
  sfbSheafTensor_monoidalPreadditive

/-- Restriction is additive. Source: Stacks 03CY
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: the section homomorphisms are unchanged, so sums of maps are unchanged (step 1). -/
@[instance] theorem additive : (restriction J B).Additive := by
  sorry

/-- Restriction is an equivalence. Source: Stacks 03CY
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 1 uses lem-cbc-constant-ring-module-sheaves. Extend the scalar action locally;
uniqueness on the original abelian sheaf gives the inverse and both inverse identities.
The CommRingCat presentation is identified with RingCat by constantCommuteCompose. -/
@[instance] theorem isEquivalence : (restriction J B).IsEquivalence := by
  sorry

/-- Restriction is exact for the two abelian categories.
Source: Stacks 03CY and 0038 (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 1 applies lem-galois-equivalence-preserves-limits to the equivalence and
its inverse. In particular both preserve kernels and cokernels, hence finite limits
and finite colimits. -/
theorem exact : exactFunctor _ _ (restriction J B) := by
  sorry

/-- The local pure tensor in the ordinary ringed-site tensor.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ringPure (M N : Modules J B) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val)).app U
      (x ⊗ₜ[(ring J B).obj.obj U] y))

/-- The local pure tensor in the sheafified objectwise fixed-ring tensor.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def fixedPure (M N : Fixed J B) (U : Cᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U) :
    (M ⊗ N).obj.obj U :=
  (sfbSheafTensor_comparison J M N).inv.hom.app U
    ((toSheafify J (M.obj ⊗ N.obj)).app U (x ⊗ₜ[B] y))

/-- Identify the fixed tensor unit with the recorded constant module sheaf.
Source: blueprint sk-def-sfb-sheaf-tensor
(blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def fixedUnitIso : 𝟙_ (Fixed J B) ≅ (constantSheaf J (ModuleCat B)).obj (ModuleCat.of B B) :=
  eqToIso (sfbSheafTensor_properties.{u, v, (max u v) + 1, max u v, 0, 0}
    (A := ModuleCat.{max u v} B) J).1

/-- The image of a constant scalar in the fixed tensor unit.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def fixedUnitScalar (U : Cᵒᵖ) (b : B) : (𝟙_ (Fixed J B)).obj.obj U :=
  (fixedUnitIso J B).inv.hom.app U
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of B B))).app U b)

/-- The normalized coherent ordinary comparison. Source: Stacks 0GMW
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
The braided monoidal structure includes naturality, associators, both unitors and symmetry.
The generator equations determine its tensorator and unit, hence determine its data uniquely. -/
structure Ordinary where
  braided : (restriction J B).Braided
  tensor_hom : ∀ (M N : Modules J B) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
    ((@Functor.OplaxMonoidal.δ _ _ _ _ _ _ (restriction J B)
      braided.toMonoidal.toOplaxMonoidal M N).hom.app U) (ringPure J B M N U x y) =
        fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y
  tensor_inv : ∀ (M N : Modules J B) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
    ((@Functor.LaxMonoidal.μ _ _ _ _ _ _ (restriction J B)
      braided.toMonoidal.toLaxMonoidal M N).hom.app U)
        (fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y) =
      ringPure J B M N U x y
  unit_hom : ∀ (U : Cᵒᵖ) (b : B),
    ((@Functor.OplaxMonoidal.η _ _ _ _ _ _ (restriction J B)
      braided.toMonoidal.toOplaxMonoidal).hom.app U)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b) =
      fixedUnitScalar J B U b

/-- Existence of the normalized ordinary tensor comparison.
Source: Stacks 03CY and 0GMW
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 2 extends the fixed-ring pure pairing uniquely across module sheafification
(lem-pc-sites-module-sheafification-bilinear-extension and its interface), then uses the
ringed tensor universal property. The reverse pairing uses
lem-sfb-braided-sheaf-tensor-generators. Both composites fix pure tensors, so are identities.
Step 3 identifies maps out of the regular module with compatible images of 1 and hence
identifies its constant-scalar unit with the sheafified constant module. On generators the
associator sends (m tensor n) tensor l to m tensor (n tensor l), the braiding exchanges
factors, and both unitors act by the same scalar. Equality detection proves all constraints. -/
theorem ordinary_exists : Nonempty (Ordinary J B) := by
  sorry

/-- The canonical ordinary structure, uniquely determined by both pure-tensor equations
and the constant-scalar unit equation in `Ordinary`.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ordinary : Ordinary J B := (ordinary_exists J B).some

/-- The canonical normalized braided structure on restriction.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance restrictionBraided : (restriction J B).Braided := (ordinary J B).braided

/-- The existing Grothendieck structure of module sheaves.
Source: Stacks 03DA (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringGrothendieck : IsGrothendieckAbelian.{max u v} (Modules J B) :=
  SheafOfModules.isGrothendieckAbelian_coefficientUniverse _

/-- Transport the Grothendieck structure along the actual restriction equivalence.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedGrothendieck : IsGrothendieckAbelian.{max u v} (Fixed J B) :=
  IsGrothendieckAbelian.of_equivalence (restriction J B).asEquivalence

/-- Cache countable colimits in fixed-coefficient module sheaves.
Source: Stacks 03CY (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedSmallColimits : HasColimitsOfSize.{0, 0} (Fixed J B) :=
  letI : HasColimitsOfSize.{max u v, max u v} (Fixed J B) :=
    IsGrothendieckAbelian.hasColimits (Fixed J B)
  hasColimitsOfSizeShrink.{0, 0, max u v, max u v} (Fixed J B)

/-- The discrete colimits used in signed totals, at their actual index size.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedDiscreteColimits (I : Type) : HasColimitsOfShape (Discrete I) (Fixed J B) :=
  (fixedSmallColimits J B).has_colimits_of_shape (Discrete I)

/-- Evaluate the preceding discrete-colimit instance without searching for a new size.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedDiscreteColimit {I : Type} (F : Discrete I ⥤ Fixed J B) : HasColimit F :=
  (fixedDiscreteColimits J B I).has_colimit F

/-- Countable coproducts for the two-sided quasi-isomorphism test.
Source: Stacks 06YP (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance fixedCountableCoproducts : HasCountableCoproducts (Fixed J B) where
  out I _ := fixedDiscreteColimits J B I

/-- Closedness of the existing ringed-site tensor at the independent site universes.
Source: Stacks 03EO (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringClosed : MonoidalClosed (Modules J B) :=
  (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := ring J B)).some

/-- The termwise equivalence on unbounded cochain complexes.
Source: Stacks 015F (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
abbrev onComplexes : CochainComplex (Modules J B) ℤ ⥤ CochainComplex (Fixed J B) ℤ :=
  (restriction J B).mapHomologicalComplex (.up ℤ)

/-- Koszul symmetry compatibility for a termwise monoidal functor, expressed once
with abstract coefficient-category structures.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def ComplexSymmetryCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal] : Prop :=
  ∃ h : (G.mapHomologicalComplex (.up ℤ)).Braided,
    h.toMonoidal = (inferInstance : (G.mapHomologicalComplex (.up ℤ)).Monoidal)

/-- The signed total comparison commutes with the Koszul symmetry.
Source: Stacks 06YL (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 4 checks on each (p,q) coproduct injection. Both paths exchange the
ordinary pure tensors and multiply by the same sign (-1)^(pq); additivity retains it.
The coproduct universal property then proves equality. -/
theorem total_symmetry :
    ComplexSymmetryCompatibility (Modules J B) (Fixed J B) (restriction J B) := by
  sorry

/-- Flatness is preserved and reflected.
Source: Stacks 03ER (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 5 conjugates right tensor by the normalized tensor isomorphism and the
exact equivalence from step 1. Exactness is invariant under these conjugations. -/
theorem flat_iff (M : Modules J B) :
    SheafOfModules.IsFlatOnSite (R := ring J B) M ↔
      exactFunctor _ _ (tensorRight ((restriction J B).obj M)) := by
  sorry

/-- The acyclic test and both quasi-isomorphism tests for the termwise image of a
complex, formulated once over abstract coefficient categories.
Source: Stacks 06YN and 06YP (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def KFlatComparison
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasCountableCoproducts D] [HasCountableCoproducts E]
    (G : D ⥤ E) [G.Additive] (κ : CochainComplex D ℤ → Prop)
    (P : CochainComplex D ℤ) : Prop :=
  (κ P ↔ ∀ A : CochainComplex E ℤ, A.Acyclic →
    (HomologicalComplex.tensorObj A ((G.mapHomologicalComplex (.up ℤ)).obj P)).Acyclic) ∧
  (κ P ↔ P.IsKFlatForTotalTensor) ∧
  (κ P ↔ CochainComplex.IsKFlatForTotalTensor
    ((G.mapHomologicalComplex (.up ℤ)).obj P))

/-- The acyclic-test K-flat condition agrees on both sides and agrees with the two-sided
quasi-isomorphism test.
Source: Stacks 06YN and 06YP (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 5 lifts every acyclic fixed-coefficient complex by the inverse exact
equivalence. Step 4 identifies its total tensor with the image of the ringed total tensor.
Step 6 uses lem-pc-tensor-mapping-cone-iso and lem-pur-quasi-iso-cone-acyclic to pass from
acyclic tests to quasi-isomorphism tests; conversely test the map 0 to an acyclic complex.
Symmetry supplies the other tensor argument in both categories. -/
theorem kflat_iff (P : CochainComplex (Modules J B) ℤ) :
    KFlatComparison (Modules J B) (Fixed J B) (restriction J B)
      (fun Q ↦ Q.IsKFlatIndependentCoefficients) P := by
  sorry

/-- The recorded functorial flat resolutions for ringed-site modules.
Source: Stacks 06YS (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
instance ringFlatResolutions : Abelian.HasFunctorialFlatResolution (Modules J B) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi (ring J B)

/-- Transport flat resolutions to fixed-coefficient module sheaves.
Source: Stacks 06YS (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: apply the inverse equivalence to a module sheaf, take the functorial flat cover
used in lem-pc-kflat-resolution, then restrict back. Step 5 identifies flatness and
step 1 preserves the epimorphic augmentation; naturality gives the resolution functor.
This supplies the canonical K-flat derived tensor API without adding a resolution hypothesis. -/
@[instance] theorem fixedFlatResolutions : Abelian.HasFunctorialFlatResolution (Fixed J B) := by
  sorry

/-- The canonical localization tensor square on every pair of K-flat representatives.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedTensorCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (κ : CochainComplex D ℤ → Prop)
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  ∀ (P Q : CochainComplex D ℤ), κ P → κ Q →
    @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
        monoidal.toOplaxMonoidal (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      (G.mapDerivedCategoryFactors.hom.app P ⊗ₘ G.mapDerivedCategoryFactors.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      DerivedCategory.Q.map (Functor.mapCochainComplexμIso G P Q).inv

/-- Compatibility of the derived tensor comparison with the canonical Koszul braiding.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedSymmetryCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence]
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  ∀ (X Y : DerivedCategory D),
    G.mapDerivedCategory.map
        (DerivedMonoidal.braiding' (DerivedCategory.Qh (C := D))
          (HomotopyCategory.quasiIso D (.up ℤ)) X Y).hom ≫
        @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
          monoidal.toOplaxMonoidal Y X =
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
          monoidal.toOplaxMonoidal X Y ≫
        (DerivedMonoidal.braiding' (DerivedCategory.Qh (C := E))
          (HomotopyCategory.quasiIso E (.up ℤ))
          (G.mapDerivedCategory.obj X) (G.mapDerivedCategory.obj Y)).hom

/-- The degree-zero regular-unit normalization of the derived tensor comparison.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedUnitCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  @Functor.LaxMonoidal.ε _ _ _ _ _ _ G.mapDerivedCategory
        monoidal.toLaxMonoidal ≫
      G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      G.mapDerivedCategoryFactors.hom.app (𝟙_ _) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.ε (G.mapHomologicalComplex (.up ℤ)))

/-- The monoidal structure and its specified tensor, symmetry and unit laws.
The subtype stores the same comparison data using the existing logical constructors.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def DerivedComparisonData
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (κ : CochainComplex D ℤ → Prop) :=
  { monoidal : G.mapDerivedCategory.Monoidal //
    derivedTensorCompatibility D E G κ monoidal ∧
    derivedSymmetryCompatibility D E G monoidal ∧
    derivedUnitCompatibility D E G monoidal }


variable [HasDerivedCategory.{wR} (Modules J B)] [HasDerivedCategory.{wB} (Fixed J B)]

/-- The induced equivalence of ordinary unbounded derived categories.
Source: Stacks 015F and 05RT (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
abbrev onDerived : DerivedCategory (Modules J B) ⥤ DerivedCategory (Fixed J B) :=
  (restriction J B).mapDerivedCategory

/-- The derived localization retains the exact equivalence and its termwise inverse.
Source: Stacks 015F and 05RT (blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 7 descends the termwise unit and counit along quasi-isomorphisms; their
triangle identities descend as well, giving the inverse equivalence. -/
@[instance] theorem derived_isEquivalence : (onDerived J B).IsEquivalence := by
  sorry

/-- The normalized coherent comparison on ordinary unbounded K-flat derived tensors.
The monoidal structures here are the existing K-flat derived localization structures.
Source: Stacks 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
The tensor square specifies the comparison on every pair of K-flat representatives,
using precisely `Functor.mapCochainComplexμIso` and the canonical localization maps.
The unit square fixes its normalization at the regular unit complex. -/
abbrev DerivedComparison :=
  DerivedComparisonData (Modules J B) (Fixed J B) (restriction J B)
    (fun P ↦ P.IsKFlatIndependentCoefficients)

/-- Restriction has the coherent derived tensor comparison computed by the total maps.
Source: Stacks 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
Proof: step 7 applies lem-sf-exact-functor-derived-triangulated to the exact equivalence
and its inverse. Their termwise inverse identities descend to the derived localization.
For step 8 use lem-weil-pbc-site-derived-tensor-descent on flat-term K-flat complexes;
step 5 identifies the resolving subcategories. Localize the step-4 total tensor maps in
both variables. The descent node's extension and uniqueness clause gives the natural
comparison on all derived objects. Its inverse is the localized inverse total map.
Associativity, unit and symmetry diagrams hold on resolving representatives by steps 3--4,
and hence on all derived objects by successive localization. Finally step 6 permits
arbitrary K-flat representatives: their total tensor functors invert quasi-isomorphisms,
so comparison with flat-term resolutions gives the same square recorded above. -/
theorem derived_comparison : Nonempty (DerivedComparison J B) := by
  sorry

end CategoryTheory.ConstantScalarRestriction

