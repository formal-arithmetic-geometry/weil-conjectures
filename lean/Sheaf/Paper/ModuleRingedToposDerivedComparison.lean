/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SectionDerivedRealization
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Algebra.Homology.KFlatModuleObject
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ProjectionMateExact

import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Sheaf.Paper.RingedTopoiTensorComparisonData
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.SheafTensor

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Module-object and ringed-topos derived comparison

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).

## Main definitions and statements

- `ordinary_exact_flat_kflat`, `ordinary_monoidal`: the ordinary equivalence clauses.
- `derivedPullComparison`, `derivedPushComparison`, `derived_homEquiv`: derived operations.
- `tensorPullComparison`, `delta_comparison`, `mu_comparison`: specified tensor maps.
- `composition_comparison`, `projection_comparison`: composition and the proper mate.
- `open_homEquiv`, `openProjection_comparison`: open adjunction and its unit mate.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Additivity, exactness, flatness and the two recorded K-flat definitions agree.
Source: Stacks 00YV, 03EK and 0G7E
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: use internal_section_tensor_comparison on the pulled-back coefficient ring.
It preserves kernels and cokernels on the unchanged abelian sheaf, hence is exact
and additive. The normalized tensor isomorphism conjugates the fixed-factor tensor
functors, giving flatness in both directions. Termwise it identifies the signed
total tensors and preserves and reflects acyclicity. Signed symmetry exchanges
P tensor N with N tensor P, relating IsKFlatModuleObject to the independent
coefficient sheaf definition. The quasi-inverse supplies every target acyclic test. -/
theorem ordinary_exact_flat_kflat (X : Scheme.{u}) :
    (equivalence Λ X).functor.Additive ∧
    exactFunctor _ _ (equivalence Λ X).functor ∧
    (∀ M : internalModules Λ X,
      exactFunctor _ _ (tensorRight M) ↔
        SheafOfModules.IsFlatOnSite ((equivalence Λ X).functor.obj M)) ∧
    (∀ P : CochainComplex (internalModules Λ X) ℤ,
      IsKFlatModuleObject X (CommMon.mk (condensedRingObj Λ X)) P ↔
        CochainComplex.IsKFlatIndependentCoefficients
          (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  sorry

/-- The chosen ordinary tensor maps obey all symmetric-monoidal coherence diagrams.
Source: Stacks 03EK (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: these are exactly the maps chosen from internal_section_tensor_comparison,
whose proof checks the naturality, associator, unitors and symmetry on local pure
tensors. The regular-unit comparison fixes local scalars, so the unit diagrams
are the scalar action laws. Local generation extends each equality to the sheaf. -/
theorem ordinary_monoidal (X : Scheme.{u}) :
    (∀ (M M' N N' : internalModules Λ X) (f : M ⟶ M') (g : N ⟶ N'),
      (equivalence Λ X).functor.map (f ⊗ₘ g) ≫
          (ordinaryTensorComparison Λ X M' N').hom =
        (ordinaryTensorComparison Λ X M N).hom ≫
          ((equivalence Λ X).functor.map f ⊗ₘ (equivalence Λ X).functor.map g)) ∧
    (∀ M N P : internalModules Λ X,
      (ordinaryTensorComparison Λ X (M ⊗ N) P).hom ≫
          (ordinaryTensorComparison Λ X M N).hom ▷ (equivalence Λ X).functor.obj P ≫
          (α_ _ _ _).hom =
        (equivalence Λ X).functor.map (α_ M N P).hom ≫
          (ordinaryTensorComparison Λ X M (N ⊗ P)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryTensorComparison Λ X N P).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X (𝟙_ _) M).hom ≫
          (ordinaryUnitComparison Λ X).hom ▷ (equivalence Λ X).functor.obj M ≫
          (λ_ _).hom = (equivalence Λ X).functor.map (λ_ M).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X M (𝟙_ _)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryUnitComparison Λ X).hom ≫
          (ρ_ _).hom = (equivalence Λ X).functor.map (ρ_ M).hom) ∧
    (∀ M N : internalModules Λ X,
      (ordinaryTensorComparison Λ X M N).hom ≫ (β_ _ _).hom =
        (equivalence Λ X).functor.map (β_ M N).hom ≫
          (ordinaryTensorComparison Λ X N M).hom) := by
  sorry

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- The specified internal derived tensor map is invertible.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: resolve both factors by flat-term K-flat complexes. The ordinary pullback
mate is invertible on every pair of modules, so its signed total is invertible.
Pullback preserves flat modules and acyclic complexes, hence these resolutions
compute all three derived tensors and their specified comparison. Localization
and naturality give invertibility on arbitrary unbounded derived objects. -/
@[instance] theorem internalDelta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    IsIso (((internalDelta Λ f).app M).app N) := by
  sorry

/-- The actual module-object proper projection arrow, the adjoint of counit after delta.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    ((CondensedRing.derivedTensor Λ Y).obj ((internalDerivedPushforward Λ f).obj K)).obj L ⟶
      (internalDerivedPushforward Λ f).obj
        (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
    (((internalDelta Λ f).app ((internalDerivedPushforward Λ f).obj K)).app L ≫
      (((CondensedRing.derivedTensor Λ X).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app K)).app
          ((internalDerivedPullback Λ f).obj L)))

/-- The precise ringed projection mate alpha, in the dependency's uncurried interface.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (modules Λ X)) (L : DerivedCategory (modules Λ Y)) :
    (tensor Λ Y).obj ((derivedPushforward Λ f).obj K, L) ⟶
      (derivedPushforward Λ f).obj ((tensor Λ X).obj (K, (derivedPullback Λ f).obj L)) :=
  derivedProjectionFormulaMate (derivedPullback Λ f) (derivedPushforward Λ f)
    (derivedAdjunction Λ f) (tensor Λ Y) (tensor Λ X) (tensorPullComparison Λ f) K L

/-- Equality of the specified derived Hom bijections; thus both units and counits agree.
Source: Stacks 07A6 and Derived Categories 09T5
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: derive the two equal ordinary Hom bijections on K-flat and K-injective
resolutions. The comparisons in derivedPullComparison and derivedPushComparison
are the canonical resolution comparisons, so uniqueness of derived adjunctions
gives this equality on all objects. Applying it to identities gives the unit
and counit statements. -/
theorem derived_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (internalModules Λ Y)) (N : DerivedCategory (internalModules Λ X))
    (q : (internalDerivedPullback Λ f).obj M ⟶ N) :
    (derivedAdjunction Λ f).homEquiv _ _
        ((derivedPullComparison Λ f).inv.app M ≫ (derivedEquivalence Λ X).functor.map q) =
      (derivedEquivalence Λ Y).functor.map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _ q) ≫
          (derivedPushComparison Λ f).hom.app N := by
  sorry

/-- Equality of the actual oplax tensor natural transformations under comparison.
Inverting this equation identifies the actual lax maps as well.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the normalized underived maps both send s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n). Apply this equality to flat-term K-flat
representatives and totalize with the same signs. The representative square in
tensorPullComparison_existsUnique and uniqueness of two-variable derived tensor
in lem-weil-pbc-site-derived-tensor-descent give the equation on every pair. -/
theorem delta_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedPullback Λ f).obj M,
            (internalDerivedPullback Λ f).obj N) ≫
        (tensor Λ X).map (Prod.mkHom
          ((derivedPullComparison Λ f).hom.app M) ((derivedPullComparison Λ f).hom.app N)) =
      (derivedPullComparison Λ f).hom.app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
        (tensorPullComparison Λ f).hom.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) := by
  sorry

/-- The actual lax tensor map is the inverse of the localized strong oplax map.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalMu {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    ((CondensedRing.derivedTensor Λ X).obj ((internalDerivedPullback Λ f).obj M)).obj
        ((internalDerivedPullback Λ f).obj N) ⟶
      (internalDerivedPullback Λ f).obj (((CondensedRing.derivedTensor Λ Y).obj M).obj N) :=
  inv (((internalDelta Λ f).app M).app N)

/-- Equality for the actual lax map mu and the inverse canonical ringed tensor map.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: invert the square in delta_comparison. Both transformations are strong,
so their lax maps are precisely the inverses of their specified oplax maps.
The inverse of the tensor of comparison isomorphisms is the tensor of their
inverses; functors preserve inverses. This gives the displayed equation. -/
theorem mu_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (tensor Λ X).map (Prod.mkHom ((derivedPullComparison Λ f).inv.app M)
        ((derivedPullComparison Λ f).inv.app N)) ≫
        (tensorComparison Λ X).inv.app
          ((internalDerivedPullback Λ f).obj M,
            (internalDerivedPullback Λ f).obj N) ≫
        (derivedEquivalence Λ X).functor.map (internalMu Λ f M N) =
      (tensorPullComparison Λ f).inv.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).inv.app (M, N)) ≫
        (derivedPullComparison Λ f).inv.app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) := by
  sorry

/-- The module-object proper projection is the precise ringed projection mate alpha.
This statement makes no invertibility assertion about the projection arrow.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: derived_homEquiv identifies the specified Hom bijection and counit, and
delta_comparison identifies its tensor arrow. Their composite therefore has the
same adjoint transpose, which is exactly derivedProjectionFormulaMate used in
ringedProjectionMateExact. Naturality and unit normalization follow from the same
identifications and the adjunction triangle identities. -/
theorem projection_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ Y).functor.map (internalProjection Λ f K L) ≫
        (derivedPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensorComparison Λ X).hom.app
          (K, (internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ X).functor.obj K))
          ((derivedPullComparison Λ f).hom.app L))) =
      (tensorComparison Λ Y).hom.app
          ((internalDerivedPushforward Λ f).obj K, L) ≫
        (tensor Λ Y).map (Prod.mkHom ((derivedPushComparison Λ f).hom.app K)
          (𝟙 ((derivedEquivalence Λ Y).functor.obj L))) ≫
        projection Λ f ((derivedEquivalence Λ X).functor.obj K)
          ((derivedEquivalence Λ Y).functor.obj L) := by
  sorry

/-- Equality of the specified open Hom bijections, hence of their units and counits.
Source: Stacks 03DI and 03DJ
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the comparison inserts the section equivalence unit into the same linearized
extension-by-zero functor. The sheaf open adjunction is unchanged on underlying maps.
The ordinary adjunction triangles give the Hom equality, and applying localization
preserves that equality since both functors are exact. Evaluate at identities for
units and counits. -/
theorem open_homEquiv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (internalModules Λ U)) (N : DerivedCategory (internalModules Λ X))
    (q : (internalDerivedExtension Λ j).obj M ⟶ N) :
    (derivedOpenAdjunction Λ j).homEquiv _ _
        ((derivedExtensionComparison Λ j).inv.app M ≫
          (derivedEquivalence Λ X).functor.map q) =
      (derivedEquivalence Λ U).functor.map ((internalOpenAdjunction Λ j).homEquiv _ _ q) ≫
        (derivedPullComparison Λ j).hom.app N := by
  sorry

/-- The actual internal adjoint-of-unit open projection arrow, using inverse delta.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalOpenProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (internalModules Λ U)) (L : DerivedCategory (internalModules Λ X)) :
    (internalDerivedExtension Λ j).obj
        (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)) ⟶
      ((CondensedRing.derivedTensor Λ X).obj ((internalDerivedExtension Λ j).obj K)).obj L :=
  ((internalOpenAdjunction Λ j).homEquiv _ _).symm
    ((((CondensedRing.derivedTensor Λ U).map
        ((internalOpenAdjunction Λ j).unit.app K)).app ((internalDerivedPullback Λ j).obj L)) ≫
      inv (((internalDelta Λ j).app
        ((internalDerivedExtension Λ j).obj K)).app L))

/-- The ringed adjoint-of-unit open projection arrow, using inverse canonical delta.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def openProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (modules Λ U)) (L : DerivedCategory (modules Λ X)) :
    (derivedExtension Λ j).obj ((tensor Λ U).obj (K, (derivedPullback Λ j).obj L)) ⟶
      (tensor Λ X).obj ((derivedExtension Λ j).obj K, L) :=
  ((derivedOpenAdjunction Λ j).homEquiv _ _).symm
    ((tensor Λ U).map (Prod.mkHom ((derivedOpenAdjunction Λ j).unit.app K)
        (𝟙 ((derivedPullback Λ j).obj L))) ≫
      (tensorPullComparison Λ j).inv.app ((derivedExtension Λ j).obj K, L))

/-- Equality of the actual adjoint-of-unit open projection morphisms.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: open_homEquiv identifies the specified unit, and delta_comparison identifies
its inverse, the actual lax map mu. Naturality of the tensor and extension
comparisons identifies their composite. Taking the specified open adjoint transpose
gives precisely the displayed equality, without choosing another projection map. -/
theorem openProjection_comparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (internalModules Λ U)) (L : DerivedCategory (internalModules Λ X)) :
    (derivedEquivalence Λ X).functor.map (internalOpenProjection Λ j K L) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedExtension Λ j).obj K, L) ≫
        (tensor Λ X).map (Prod.mkHom ((derivedExtensionComparison Λ j).hom.app K)
          (𝟙 ((derivedEquivalence Λ X).functor.obj L))) =
      (derivedExtensionComparison Λ j).hom.app
          (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensorComparison Λ U).hom.app
          (K, (internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensor Λ U).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ U).functor.obj K))
          ((derivedPullComparison Λ j).hom.app L))) ≫
        openProjection Λ j ((derivedEquivalence Λ U).functor.obj K)
          ((derivedEquivalence Λ X).functor.obj L) := by
  sorry

/-- Pullback composition is identified with the canonical ringed pasting comparison.
Source: Stacks 03D7 and 07A6
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the internal composition comparison is the localization of inverse-image
pasting followed by the compatible coefficient isomorphisms alpha. Under E this is
the same scalar-extension pasting map for ringed modules. Its Hom adjunction
characterization and K-flat normalization determine it uniquely. Essential
surjectivity of D(E_Z) extends the equation to all ringed derived objects. -/
theorem composition_comparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ M : DerivedCategory (internalModules Λ Z),
        (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
            (derivedPullbackComposition Λ f g).hom.app ((derivedEquivalence Λ Z).functor.obj M) =
          (derivedEquivalence Λ X).functor.map
              ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
            (derivedPullComparison Λ f).hom.app
              ((internalDerivedPullback Λ g).obj M) ≫
            (derivedPullback Λ f).map ((derivedPullComparison Λ g).hom.app M) := by
  sorry

/-- The specified derived tensor transformation comparison in the paper's field setting.
Together with ordinary_exact_flat_kflat, ordinary_monoidal, tensor_representatives,
derived_homEquiv, composition_comparison, projection_comparison, open_homEquiv and
openProjection_comparison, this states every clause of the comparison lemma.
Source: Stacks 00YV, 03EK, 03D7, 03DJ, 07A4, 07A6 and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: construct the sectionwise equivalence and its normalized ordinary tensor
maps, and identify signed total complexes and the two K-flat tests. Localize on
K-flat and K-injective representatives, identifying the specified adjunction Hom
bijections and composition pasting. The ordinary pure-tensor formula identifies
actual delta, and its inverse identifies actual mu. Transpose counit after delta
for the proper projection map. For an open immersion, localize the exact extension
by zero and transpose unit followed by mu. These are precisely the equalities
stated in the named clauses above; see their proof plans for the individual steps. -/
theorem module_ringed_topos_derived_comparison
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y.left)) :
    (derivedEquivalence Λ X.left).functor.map (((internalDelta Λ f.left).app M).app N) ≫
        (tensorComparison Λ X.left).hom.app
          ((internalDerivedPullback Λ f.left).obj M,
            (internalDerivedPullback Λ f.left).obj N) ≫
        (tensor Λ X.left).map (Prod.mkHom
          ((derivedPullComparison Λ f.left).hom.app M)
          ((derivedPullComparison Λ f.left).hom.app N)) =
      (derivedPullComparison Λ f.left).hom.app
          (((CondensedRing.derivedTensor Λ Y.left).obj M).obj N) ≫
        (derivedPullback Λ f.left).map ((tensorComparison Λ Y.left).hom.app (M, N)) ≫
        (tensorPullComparison Λ f.left).hom.app
          ((derivedEquivalence Λ Y.left).functor.obj M,
            (derivedEquivalence Λ Y.left).functor.obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
