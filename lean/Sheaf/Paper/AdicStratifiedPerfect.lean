/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.Paper.AdicLisseModule
public import Sheaf.Paper.CompletedConstantSheafReduction
public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ConstantModuleSectionProperties
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Paper.TorsionLimitSheafCompleteness
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.AdicResidueLissePerfectLift
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Adic constructibility and stratified perfect models

Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11
(blueprint: lem-sfb-adic-stratified-perfect).

The coefficients are arbitrary complete Noetherian local rings. No finiteness of their
residue fields or perfectness of their quotient modules over the original ring is assumed.

## Main definitions

* `IsSfbAdicConstructible`: completeness and bounded constructible etale residue origin.
* `IsSfbStratifiedPerfect`: finite strata with pro-etale locally perfect coefficient models.
* `SfbAdicConstructibleCategory`: the full ambient subcategory of these objects.

## Main statements

* `adic_stratified_perfect`: equivalence, boundedness and triangulated closure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Read modules over the constant ring sheaf as fixed-scalar module-valued sheaves,
by restricting along the constant section map, retaining the underlying additive sheaf.
Source: Stacks Tag 093I; Bhatt--Scholze, Definition 6.3.1
(blueprint: lem-sfb-adic-stratified-perfect). -/
def sfbFixedScalarRestriction (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    proEtaleRingModules X (adicLisseConstantRing X k) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k) where
  obj M :=
    { obj :=
        { obj := fun U ↦
            ((PresheafOfModules.restrictScalars (adicLisseConstantUnit X k)).obj M.val).obj U
          map := fun f ↦
            ((PresheafOfModules.restrictScalars (adicLisseConstantUnit X k)).obj M.val).map f
          map_id := fun _ ↦ by ext x; simp; rfl
          map_comp := fun _ _ ↦ by ext x; simp; rfl }
      property := Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}) M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun U ↦ (ModuleCat.restrictScalars ((adicLisseConstantUnit X k).app U).hom).map
        (f.val.app U)
      naturality := fun {_ _} g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }

/-- This scalar restriction is additive, since it keeps the underlying additive maps.
Source: Stacks Tag 093I (blueprint: lem-sfb-adic-stratified-perfect). -/
instance sfbFixedScalarRestriction_additive (X : Scheme.{u}) (k : Type (u + 1))
    [CommRing k] : (sfbFixedScalarRestriction X k).Additive where
  map_add := by intros; ext U x; rfl

/-- Tensor a complex of etale module sheaves termwise with a degree-zero module sheaf.
In the application the coefficient ring is a residue field. Every module sheaf is flat,
by the exact conservative geometric stalk functors, so this computes the derived tensor
for every representative complex, including unbounded representatives.
Source: Bhatt--Scholze, Remark 6.3.2 (blueprint: lem-sfb-adic-stratified-perfect). -/
def sfbEtaleTensorDegreeZero (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ)
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) :
    CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ :=
  letI := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} k)
  ((MonoidalCategory.tensorRight N).mapHomologicalComplex (.up ℤ)).obj C

/-- The residue reduction, read in fixed-scalar sheaves using the canonical constant
sections. The projection is to exponent one, written `0+1`, so the coefficient is A/I.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-sfb-adic-stratified-perfect). -/
def sfbResidueComplex (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ :=
  ((sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))).mapHomologicalComplex (.up ℤ)).obj
    (DerivedCategory.Q.objPreimage
      ((completedAdicDerivedChange X (limit.π (adicLisseRingSystem X I) (op 0))).obj K))

/-- Transport a commutative coefficient sheaf to the equivalent small model of the same
site; only the morphism universe is enlarged.
Source: Stacks Tags 00YY and 099F (blueprint: lem-sfb-adic-stratified-perfect). -/
abbrev sfbModelRings (X : Scheme.{u}) :=
  (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)

/-- Local derived completeness, using the recorded predicate on the equivalent small
site and the kernel of the actual residue projection. In the Noetherian case this kernel
is exactly the ideal generated by the constant sections in I. Transport a localization
representative termwise, so no choice of a new derived functor is involved.
Source: Stacks Tags 093M and 099F (blueprint: lem-sfb-adic-stratified-perfect). -/
def IsSfbAdicComplete (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  let F := proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  letI : F.Additive := ⟨by intros; ext U x; rfl⟩
  ConstantCompletion.IsComplete
    ((sfbModelRings X).map (limit.π (adicLisseRingSystem X I) (op 0)))
    (ConstantCompletion.Q _ |>.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)))

/-- Condition (a), using the recorded global constructibility predicate. On a Noetherian
scheme this is exactly the affine-local notion as well. Module finiteness means finite
 generation, hence finite presentation over the residue field, never finite underlying sets.
The last clause explicitly tests every degree-zero module sheaf for finite Tor amplitude.
Source: Bhatt--Scholze, Definitions 6.3.1 and 6.5.1, Remark 6.3.2
(blueprint: lem-sfb-adic-stratified-perfect). -/
def IsSfbAdicConstructible (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  IsSfbAdicComplete X I K ∧
    ∃ C : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) ∧
      (∀ q : ℤ, IsConstructibleSheaf (C.homology q)) ∧
      Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
        DerivedCategory.Q.obj
          (((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex (.up ℤ)).obj C)) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))))
          (q : ℤ), (q < a ∨ b < q) →
            IsZero ((sfbEtaleTensorDegreeZero X (A ⧸ I ^ (0 + 1)) C N).homology q)

/-- The termwise completed realization of an actual coefficient complex. The constant
module functor and scalar extension are the existing sheafification/tensor constructions.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-sfb-adic-stratified-perfect). -/
def sfbCompletedModel (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)) :=
  DerivedCategory.Q.obj
    (((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
      (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P))

/-- Restrict to a stratum, retaining the true inverse-image coefficient ring, and then to
one object of its pro-etale site. For immersions the coefficient identification with the
completion on the stratum is the canonical limit comparison, as in the recorded immersion
limit-preservation lemma.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-sfb-adic-stratified-perfect). -/
def sfbLocalRestriction {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :=
  let R' := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  ringedSiteDerivedRestrictionOfUniverses
    ((adicLisseForget S).obj ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) U
    ((proEtaleRingDerivedPullback i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj K)

/-- Condition (b): finite constructible locally closed strata, pro-etale covering sieves,
and bounded finite-projective coefficient complexes realizing K there.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-sfb-adic-stratified-perfect). -/
def IsSfbStratifiedPerfect (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  ∃ s : Stratification X,
    (∀ α : Fin s.n, Topology.IsConstructible (s.stratum α)) ∧
    ∀ α : Fin s.n, ∃ V : Sieve (⊤_ (s.domain α).ProEt),
      V ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt) ∧
        ∀ (U : (s.domain α).ProEt) (f : U ⟶ ⊤_ (s.domain α).ProEt), V f →
          ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
            DerivedCategory.IsPerfectRingComplex (DerivedCategory.Q.obj P) ∧
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
            Nonempty (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
              sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U
                (sfbCompletedModel X I P))

/-- The specified complexes form the full ambient subcategory, with every ambient morphism.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-sfb-adic-stratified-perfect). -/
abbrev SfbAdicConstructibleCategory (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) := ObjectProperty.FullSubcategory (IsSfbAdicConstructible X I)

/-- Adic constructibility is equivalent to stratified perfect local models; these objects
are bounded and form a full triangulated subcategory.
Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11
(blueprint: lem-sfb-adic-stratified-perfect).

Proof, following the six steps of the node:
1. Restrict completed coefficients and the Koszul completion unit to immersions and slice
sites. Immersion inverse image and slice restriction preserve limits. Exact countable
products and the strict-tower Roos triangle compute the unit. Finite-stratum detection
therefore detects its zero cone, so completeness restricts and is detected on these covers.
2. For bounded etale residue complexes, geometric stalks commute with derived tensor.
Tensor of vector spaces over the residue field is exact; exact conservative stalks give
finite Tor amplitude in the same interval, without finite-coefficient assumptions.
3. Refine the finitely many cohomology stratifications by fibre-product immersions. Each
stratum is Noetherian. Comparison-pullback identifies its residue reduction, and the local
perfect-lifting lemma gives the required pro-etale perfect coefficient models.
4. Conversely finite projective terms are idempotent summands of finite completed free
modules, hence limits of power-torsion quotient sheaves. Torsion-limit completeness and the
constant/completed equivalence give local completeness; step 1 detects it globally.
Quasi-compact strata admit finitely many quasi-compact pieces of trivializing covers;
the finitely many perfect models give global cohomological bounds, also for empty X.
5. Completed reduction identifies each model with the constant complex P tensor_A A/I.
Its cohomology is locally constant finite dimensional. The constructible comparison theorem
for arbitrary discrete Noetherian coefficients descends it to a bounded etale complex.
Affine-local and global constructibility agree on Noetherian X: refine affine strata by
successive differences of a finite affine cover. Step 2 gives its finite Tor amplitude.
6. Completion units are natural maps of exact functors, so complete objects form a full
triangulated subcategory. Residue reduction is triangulated. Constructible cohomology is
closed under kernels, cokernels and extensions by the weak Serre lemma; the long exact
sequence of an ambient triangle gives two-out-of-three and boundedness. Zero, isomorphisms
and shifts preserve both conditions. No dimension or residue-invertibility bound is used.

Proof dependencies by step:
1. lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-proetale-weakly-etale-
localization, lem-weil-pbc-constant-completion-equivalence, lem-weil-proetale-countable-products-
exact, lem-weil-derived-countable-products-core, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-weil-pbc-noetherian-stratum-detection.
2. prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative, lem-weil-
pbc-ringed-topoi-derived-tensor-pullback.
3. lem-weil-pbc-constructible-stratification-intersection, lem-weil-pbc-comparison-pullback, lem-
sfb-adic-residue-lisse-perfect-lift.
4. lem-weil-pbc-torsion-limit-sheaf-completeness, lem-weil-pbc-constant-completion-equivalence,
def-weil-pbc-proetale-site, lem-weil-pbc-noetherian-stratum-detection.
5. lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-pbc-noetherian-stratum-detection, sk-
thm-pe-constructible-comparison, lem-weil-pbc-constant-module-section-properties, def-pe-etale-
constructible-module, lem-sc-affine-noetherian-underlying-space, def-weil-constructible-subset.
6. lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-pur-derived-change-of-rings, sk-thm-pe-constructible-comparison, lem-sf-derived-homology-long-
exact, lem-sfb-discrete-noetherian-constructible-serre. -/
theorem adic_stratified_perfect (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (_hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A] :
    (∀ K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)),
      IsSfbAdicConstructible X I K ↔ IsSfbStratifiedPerfect X I K) ∧
    (∀ K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)),
      IsSfbAdicConstructible X I K → ∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    IsSfbAdicConstructible X I (0 : DerivedCategory
      (proEtaleRingModules X (adicLisseCompletedRing X I))) ∧
    (∀ (K L : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))),
      Nonempty (K ≅ L) → IsSfbAdicConstructible X I K → IsSfbAdicConstructible X I L) ∧
    (∀ (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) (n : ℤ),
      IsSfbAdicConstructible X I K → IsSfbAdicConstructible X I (K⟦n⟧)) ∧
    ∀ T : Triangle (DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))),
      T ∈ distTriang _ →
        (IsSfbAdicConstructible X I T.obj₁ ∧ IsSfbAdicConstructible X I T.obj₂ →
          IsSfbAdicConstructible X I T.obj₃) ∧
        (IsSfbAdicConstructible X I T.obj₂ ∧ IsSfbAdicConstructible X I T.obj₃ →
          IsSfbAdicConstructible X I T.obj₁) ∧
        (IsSfbAdicConstructible X I T.obj₃ ∧ IsSfbAdicConstructible X I T.obj₁ →
          IsSfbAdicConstructible X I T.obj₂) := by
  sorry

end AlgebraicGeometry.Scheme
