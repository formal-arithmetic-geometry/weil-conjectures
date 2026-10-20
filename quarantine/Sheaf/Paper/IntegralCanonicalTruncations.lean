/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.AdicTorFlatCohomology
import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteReductionReconstructionCompleted
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.LevelwiseAdicTruncations
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
/-! # Integral canonical truncations and their conditional tower computation

Source: blueprint, smooth base change, order 1430; Stacks Tags 0118 and 08J5
(blueprint: thm-weil-pbc-integral-truncations).
The Roos-limit formulation retains the actual quotient transitions and makes no
choice of an unspecified derived-limit object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable [hNoeth : IsNoetherian T] [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
include hNoeth hDim hInv

/-- The ambient standard t-structure on completed coefficients.
Source: blueprint order 1430 (blueprint: thm-weil-pbc-integral-truncations). -/
abbrev pbcAmbientTStructure :=
  DerivedCategory.TStructure.t (C := pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))

/-- The canonical ambient truncations remain in the integral full subcategory.
Source: blueprint order 1430, canonical-truncation clause
(blueprint: thm-weil-pbc-integral-truncations).
Proof: stalkwise invertibility of l implies invertibility of its global section.
Apply the standard-truncation clause of integralStratifiedPerfectClosure to K.property,
using the supplied finite-dimensional bound. This uses ambient truncation closure and
does not require commutation with coefficient reduction. -/
theorem pbcIntegralCanonicalTruncations_mem
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (m : ℤ) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        (((pbcAmbientTStructure T l E).truncLE m).obj K.obj) ∧
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        (((pbcAmbientTStructure T l E).truncGE m).obj K.obj) := by
  have hl : IsUnit (l : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro t ht
    simpa using (hInv.out t)
  exact (integralStratifiedPerfectClosure T l E hDim.out hl).2.2.1 K.obj K.property m

/-- Restriction of the actual ambient lower truncation, with all ambient maps.
Source: blueprint order 1430 (blueprint: thm-weil-pbc-integral-truncations). -/
def pbcIntegralTruncLE (m : ℤ) :
    PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) ⥤
      PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
      (pbcAmbientTStructure T l E).truncLE m)
    (fun K ↦ (pbcIntegralCanonicalTruncations_mem T l E K m).1)

/-- Restriction of the actual ambient upper truncation, with all ambient maps.
Source: blueprint order 1430 (blueprint: thm-weil-pbc-integral-truncations). -/
def pbcIntegralTruncGE (m : ℤ) :
    PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) ⥤
      PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
      (pbcAmbientTStructure T l E).truncGE m)
    (fun K ↦ (pbcIntegralCanonicalTruncations_mem T l E K m).2)

/-- Cohomology, additivity and the distinguished canonical truncation triangle.
The maps are the actual counit and unit, so the identifications are canonical.
Source: blueprint order 1430, clauses (ii) and (iii)
(blueprint: thm-weil-pbc-integral-truncations).
Proof: the integral functors are lifts of the ambient canonical functors, hence inherit
additivity. Standard derived truncation gives the cohomology isomorphisms in the
surviving degrees and vanishing in the removed degrees. Its natural triangle is
distinguished. Membership of both end terms is pbcIntegralCanonicalTruncations_mem,
so it is also the inherited integral triangle. Naturality of the three canonical
transformations gives functoriality of this triangle. -/
theorem pbc_integral_truncation_properties (m : ℤ) :
    (pbcIntegralTruncLE T l E m).Additive ∧
    (pbcIntegralTruncGE T l E (m + 1)).Additive ∧
    ∀ K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
      (∀ i : ℤ, i ≤ m → IsIso ((DerivedCategory.homologyFunctor _ i).map
        (((pbcAmbientTStructure T l E).truncLEι m).app K.obj))) ∧
      (∀ i : ℤ, m < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((pbcAmbientTStructure T l E).truncLE m).obj K.obj))) ∧
      (∀ i : ℤ, m + 1 ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        (((pbcAmbientTStructure T l E).truncGEπ (m + 1)).app K.obj))) ∧
      (∀ i : ℤ, i ≤ m → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((pbcAmbientTStructure T l E).truncGE (m + 1)).obj K.obj))) ∧
      ((pbcAmbientTStructure T l E).triangleLTGE (m + 1)).obj K.obj ∈
        distTriang (PbcCompletedDerived T (pbcIntegralDatum l E)) := by
  have hLE : (pbcIntegralTruncLE T l E m).Additive := by
    constructor
    intro X Y f g
    apply ObjectProperty.hom_ext
    change ((pbcAmbientTStructure T l E).truncLE m).map (f.hom + g.hom) = _
    exact Functor.map_add _
  have hGE : (pbcIntegralTruncGE T l E (m + 1)).Additive := by
    constructor
    intro X Y f g
    apply ObjectProperty.hom_ext
    change ((pbcAmbientTStructure T l E).truncGE (m + 1)).map (f.hom + g.hom) = _
    exact Functor.map_add _
  refine ⟨hLE, hGE, fun K ↦ ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi
    exact DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K.obj (m + 1) i
      (by omega)
  · intro i hi
    exact DerivedCategory.isZero_of_isLE _ m i hi
  · intro i hi
    exact DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K.obj (m + 1) i hi
  · intro i hi
    exact DerivedCategory.isZero_of_isGE _ (m + 1) i (by omega)
  · exact (pbcAmbientTStructure T l E).triangleLTGE_distinguished (m + 1) K.obj

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The normalized reduction diagram, including the canonical semilinear transitions.
Source: blueprint order 1430 (blueprint: thm-weil-pbc-integral-truncations). -/
def pbcCanonicalReductionDiagram (K : PbcCompletedDerived T d) :
    ℕᵒᵖ ⥤ PbcCompletedDerived T d :=
  Functor.ofOpSequence
    (X := fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
      ((pbcCompletedReduction T d n).obj K))
    (fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
      (pbcReductionTransition (pbcAdicProjection T d (n + 1))
        (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
        (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
        (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
        (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
          ((pbcCompletedReduction T d n).obj K))

/-- The higher-Tor vanishing formulation of the source's compatibility condition,
required above every cutoff. The single cohomology module is placed in degree zero.
Source: order 1430 and the Tor formulation of order 1429
(blueprint: thm-weil-pbc-integral-truncations). -/
def PbcTruncationTorCompatible (K : PbcCompletedDerived T d) : Prop :=
  ∀ (n : ℕ) (q p : ℤ), p < 0 →
    IsZero ((DerivedCategory.homologyFunctor _ p).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K)))))

omit hNoeth hDim hInv in
/-- Flat cohomology is sufficient for the compatibility used in the theorem.
The single complex in degree zero expresses flatness by K-flatness and uses the
actual completed ring, rather than the underlying constant coefficient ring.
Source: blueprint order 1430, the sufficient condition from order 1429
(blueprint: thm-weil-pbc-integral-truncations).
Proof: flatness of ambient cohomology identifies the cohomology of each quotient
reduction with the ordinary quotient of that cohomology sheaf, by the tensor spectral
sequence. That quotient is flat over the quotient ring. Consequently all its higher
Tor modules for the next quotient vanish, which is precisely the displayed predicate.
The same condition may be checked on the common local models: flatness is local and
inverse image is exact; the strata cover all stalks and coefficient change is the
specified restriction. -/
theorem pbc_flat_cohomology_torCompatible (K : PbcCompletedDerived T d)
    (_hflat : ∀ i : ℤ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion T d)
      ((CochainComplex.singleFunctor _ 0).obj
        ((DerivedCategory.homologyFunctor _ i).obj K))) :
    PbcTruncationTorCompatible T d K := by
  sorry

/-- On the integral constructible category, the all-level compatibility condition
is equivalent to flat cohomology of the local models, as stipulated in the source.
Flatness is expressed by K-flatness of each actual cohomology module in degree zero.
Source: blueprint order 1430, hypothesis paragraph
(blueprint: thm-weil-pbc-integral-truncations).
Proof: flat cohomology implies compatibility by pbc_flat_cohomology_torCompatible.
Conversely, apply the compatibility condition to the finite local models at all
positive quotient levels. The local flatness criterion over the artinian principal
quotient rings makes their cohomology flat over those quotients. The bounded finite
models and intrinsic completeness identify their cohomology with the inverse limits
of these quotient modules. Compatible quotient-flat finite modules have torsion-free
limits over the complete DVR: an element killed by the uniformizer vanishes at each
fixed quotient after lifting to arbitrarily higher levels. Hence the limit is flat.
The same argument on each stratum proves flatness of the local model cohomology;
the canonical local identifications transport this to the ambient cohomology sheaves. -/
theorem pbc_torCompatible_iff_flat_cohomology
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) :
    PbcTruncationTorCompatible T (pbcIntegralDatum l E) K.obj ↔
      ∀ i : ℤ, CochainComplex.IsKFlatIndependentCoefficients
        (R := pbcAdicCompletion T (pbcIntegralDatum l E))
        ((CochainComplex.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ i).obj K.obj)) := by
  sorry

omit hNoeth hDim hInv in
/-- Exact countable products for modules over the actual completed coefficient sheaf.
Source: order 1430; Bhatt--Scholze 4.2.8
(blueprint: thm-weil-pbc-integral-truncations).
Proof: apply countableProducts_exact to pbcAdicCompletion. Its product-of-epimorphisms
clause, together with sectionwise kernels, is precisely CountableAB4Star. -/
theorem pbcCompletedCountableAB4Star : CountableAB4Star
    (pbcModules T (pbcAdicCompletion T d)) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : HasCountableProducts (pbcModules T (pbcAdicCompletion T d)) :=
    (ProEt.countableProducts_exact.{u, u, 0} T (pbcAdicCompletion T d)).1
  have : (lim (J := Discrete ℕ)
      (C := pbcModules T (pbcAdicCompletion T d))).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{u, u, 0} T
          (pbcAdicCompletion T d)).2.2 ℕ (fun n ↦ F.obj ⟨n⟩)
            (fun n ↦ G.obj ⟨n⟩) (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have : HasFiniteBiproducts (pbcModules T (pbcAdicCompletion T d)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have := hasExactLimitsOfShape_of_preservesEpi
    (pbcModules T (pbcAdicCompletion T d)) (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

/-- Countable products in the ambient derived category, fixed by their limit property.
Source: order 1430, Tag 07KC (blueprint: thm-weil-pbc-integral-truncations). -/
instance pbcCompletedDerivedCountableProducts : HasCountableProducts
    (PbcCompletedDerived T d) :=
  letI := pbcCompletedCountableAB4Star T d
  (derivedCategory_countableProducts_core.{0}
    (pbcModules T (pbcAdicCompletion T d))).choose

/-- Under exactly the higher-Tor compatibility condition at all levels, canonical
integral truncations are the derived limits of the levelwise truncated reduction tower.
Their quotient reductions are canonically the quotient-coefficient truncations: the
comparison isomorphisms are normalized by the truncation counit and unit.
Source: blueprint order 1430 (blueprint: thm-weil-pbc-integral-truncations).
Proof: the levelwise truncation result uses the Tor hypothesis in the tensor truncation
triangle to remove its higher-Tor obstruction. It gives normalized adic towers with
uniformly bounded constructible models and compatible etale origins. Reconstruction
identifies their Roos limits with complete objects and identifies their finite reductions
with those towers. The cohomology formulas and the derived-limit truncation triangle
identify these limits with the ambient canonical truncations, by their adjunctions.
Uniqueness with the counit and unit proves naturality in K and compatibility with all
quotient normalizations, including equal indices. The resulting triangle is the
canonical ambient truncation triangle; its end objects belong to the full category
by pbcIntegralCanonicalTruncations_mem. No assertion of reduction compatibility without
the Tor condition is made. -/
theorem pbc_integral_truncations
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
    (_hTor : PbcTruncationTorCompatible T (pbcIntegralDatum l E) K.obj) (m : ℤ) :
    IsDerivedLimit
      (K := fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).obj
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
      (fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).map
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
          (homOfLE (Nat.le_succ n)).op))
      (((pbcAmbientTStructure T l E).truncLE m).obj K.obj) ∧
    IsDerivedLimit
      (K := fun n ↦ ((pbcAmbientTStructure T l E).truncGE (m + 1)).obj
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
      (fun n ↦ ((pbcAmbientTStructure T l E).truncGE (m + 1)).map
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
          (homOfLE (Nat.le_succ n)).op))
      (((pbcAmbientTStructure T l E).truncGE (m + 1)).obj K.obj) ∧
    ∀ n : ℕ,
      (∃ e : (pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
          (((pbcAmbientTStructure T l E).truncLE m).obj K.obj) ≅
          (DerivedCategory.TStructure.t.truncLE m).obj
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj),
        e.hom ≫ (DerivedCategory.TStructure.t.truncLEι m).app
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj) =
          (pbcCompletedReduction T (pbcIntegralDatum l E) n).map
            (((pbcAmbientTStructure T l E).truncLEι m).app K.obj)) ∧
      (∃ e : (pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
          (((pbcAmbientTStructure T l E).truncGE (m + 1)).obj K.obj) ≅
          (DerivedCategory.TStructure.t.truncGE (m + 1)).obj
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj),
        (pbcCompletedReduction T (pbcIntegralDatum l E) n).map
            (((pbcAmbientTStructure T l E).truncGEπ (m + 1)).app K.obj) ≫ e.hom =
          (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj)) := by
  sorry

end AlgebraicGeometry.Scheme
