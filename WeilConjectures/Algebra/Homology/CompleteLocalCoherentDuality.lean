/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingHomExtensionDefsSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.CohenPowerSeriesPresentation
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.CoherentRHomFiniteInjectiveDimension
import WeilConjectures.Algebra.Homology.DerivedEvaluationFiniteInjective
import WeilConjectures.RingTheory.RegularLocalBoundedInjectiveResolution

/-! # Coherent duality over a complete Noetherian local ring

Source: Stacks Project, dualizing.tex, Tags 0BFR(2) and 0A7C
(blueprint: lem-trf-complete-local-coherent-duality).

The ordinary module category is the existing one-object bottom-topology ringed site.
The canonical biduality arrow uses the existing evaluation-normalized adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

/-- The contravariant functor RHom(-, Omega), using the recorded internal Hom.
Source: Stacks Project, Tag 0A7C (blueprint: lem-trf-complete-local-coherent-duality). -/
def completeLocalDualFunctor (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)]
    (Ω : DerivedCategory (RingSiteModules R)) :
    (DerivedCategory (RingSiteModules R))ᵒᵖ ⥤ DerivedCategory (RingSiteModules R) :=
  Prod.sectL (DerivedCategory (RingSiteModules R))ᵒᵖ Ω ⋙
    SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)

/-- Canonical biduality: transpose of evaluation after the Koszul interchange.
The adjunction is fixed on ordinary K-flat/K-injective representatives, so this is
an actual canonical map, not a chosen morphism or chosen objectwise isomorphism.
Source: Stacks Project, Tags 0A7C and 0A67
(blueprint: lem-trf-complete-local-coherent-duality). -/
def completeLocalBidual (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)]
    (Ω K : DerivedCategory (RingSiteModules R)) :
    K ⟶ (completeLocalDualFunctor R Ω).obj
      (op ((completeLocalDualFunctor R Ω).obj (op K))) :=
  (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
    ((completeLocalDualFunctor R Ω).obj (op K))).homEquiv K Ω
      ((β_ K ((completeLocalDualFunctor R Ω).obj (op K))).hom ≫
        (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R) K).counit.app Ω)

/-- Existence of coherent duality, including unbounded coherent complexes and canonical,
natural biduality. The two one-sided boundedness equivalences express the exchange
of D+ and D-; the last implication states preservation of Db.
Source: Stacks Project, Tag 0BFR, lemma-ubiquity-dualizing, case (2), and Tag 0A7C,
lemma-dualizing (blueprint: lem-trf-complete-local-coherent-duality).

Proof:
1. Cohen power-series presentation gives a surjective local map A to R with A complete,
Noetherian and regular local. The regular-local bounded-injective-resolution lemma
(lem-trf-regular-local-bounded-injective-resolution) gives a bounded injective model of A[0].
2. Evaluation at 1 identifies Hom(A[0],I) with I. Bounded injective complexes are K-injective
(lem-weil-pbc-bounded-below-injectives-kinjective), so scalar action on A[0] is an isomorphism.
The finite-map transfer lemma (lem-trf-finite-map-dualizing-transfer) applied to A to R
constructs Omega = RHom_A(R,A[0]), with bounded injective R-model J, finite cohomology,
and scalar-action isomorphism R[0] to RHom_R(Omega,Omega).
3. For every unbounded coherent K, lem-trf-coherent-rhom-finite-injective-dimension gives
finite cohomology of RHom_R(K,Omega). Thus the contravariant functor preserves coherence.
4. Each bounded-above good truncation of K is pseudo-coherent by the Noetherian
pseudo-coherent cohomology criterion. Apply lem-trf-derived-evaluation-finite-injective
with L=M=Omega. Both have bounded injective models; RHom(Omega,Omega) is R[0], of Tor
amplitude [0,0]. The resulting composite K = R[0] tensor K to D(D(K)) is an isomorphism.
5. Its transpose is evaluation: scalar 1 acts as the identity of Omega. Hence this
composite is exactly completeLocalBidual. Naturality of evaluation and scalar action
proves the displayed naturality equation, including the contravariant map twice.
6. These natural bidual isomorphisms supply mutually inverse functors between the
coherent category and its opposite, giving the stated equivalence compatible with RHom.
7. If J has terms only in [a,b], compute RHom(K,Omega) by Hom(P,J). Good truncation
makes P zero above c when K is bounded above by c. Its Hom complex then vanishes below
a-c. Good truncation makes P zero below c when K is bounded below by c; its Hom complex
vanishes above b-c. This uses def-pur-hom-complex and K-injectivity of J.
8. These bounds exchange D+ and D- and preserve Db. Apply the same bounds to D(K)
and use canonical biduality to get the reverse boundedness implications. Consequently
the restrictions remain mutually inverse, including on Db. -/
theorem complete_local_coherent_duality
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [HasDerivedCategory.{u} (RingSiteModules R)] :
    ∃ Ω : DerivedCategory (RingSiteModules R),
      (∀ i : ℤ, Module.Finite R
        (((homologyFunctor (RingSiteModules R) i).obj Ω).val.obj (op ⟨PUnit.unit⟩))) ∧
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (RingSiteModules R) i).obj Ω)) ∧
      (∃ e :
        (ObjectProperty.FullSubcategory (fun K : DerivedCategory (RingSiteModules R) ↦
          ∀ i : ℤ, Module.Finite R
            (((homologyFunctor (RingSiteModules R) i).obj K).val.obj
              (op ⟨PUnit.unit⟩))))ᵒᵖ ≌
        ObjectProperty.FullSubcategory (fun K : DerivedCategory (RingSiteModules R) ↦
          ∀ i : ℤ, Module.Finite R
            (((homologyFunctor (RingSiteModules R) i).obj K).val.obj
              (op ⟨PUnit.unit⟩))),
        Nonempty (e.functor ⋙ ObjectProperty.ι
          (fun K : DerivedCategory (RingSiteModules R) ↦ ∀ i : ℤ, Module.Finite R
            (((homologyFunctor (RingSiteModules R) i).obj K).val.obj (op ⟨PUnit.unit⟩))) ≅
          (ObjectProperty.ι
            (fun K : DerivedCategory (RingSiteModules R) ↦ ∀ i : ℤ, Module.Finite R
              (((homologyFunctor (RingSiteModules R) i).obj K).val.obj
                (op ⟨PUnit.unit⟩)))).op ⋙ completeLocalDualFunctor R Ω)) ∧
      (∀ K : DerivedCategory (RingSiteModules R),
        (∀ i : ℤ, Module.Finite R
          (((homologyFunctor (RingSiteModules R) i).obj K).val.obj (op ⟨PUnit.unit⟩))) →
        IsIso (completeLocalBidual R Ω K) ∧
        ((∃ a : ℤ, ∀ i : ℤ, i < a →
          IsZero ((homologyFunctor (RingSiteModules R) i).obj K)) ↔
          ∃ b : ℤ, ∀ i : ℤ, b < i →
            IsZero ((homologyFunctor (RingSiteModules R) i).obj
              ((completeLocalDualFunctor R Ω).obj (op K)))) ∧
        ((∃ b : ℤ, ∀ i : ℤ, b < i →
          IsZero ((homologyFunctor (RingSiteModules R) i).obj K)) ↔
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero ((homologyFunctor (RingSiteModules R) i).obj
              ((completeLocalDualFunctor R Ω).obj (op K)))) ∧
        ((∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
          IsZero ((homologyFunctor (RingSiteModules R) i).obj K)) →
          ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
            IsZero ((homologyFunctor (RingSiteModules R) i).obj
              ((completeLocalDualFunctor R Ω).obj (op K))))) ∧
      (∀ (K L : DerivedCategory (RingSiteModules R)) (f : K ⟶ L),
        (∀ i : ℤ, Module.Finite R
          (((homologyFunctor (RingSiteModules R) i).obj K).val.obj (op ⟨PUnit.unit⟩))) →
        (∀ i : ℤ, Module.Finite R
          (((homologyFunctor (RingSiteModules R) i).obj L).val.obj (op ⟨PUnit.unit⟩))) →
        f ≫ completeLocalBidual R Ω L = completeLocalBidual R Ω K ≫
          (completeLocalDualFunctor R Ω).map
            ((completeLocalDualFunctor R Ω).map f.op).op) := by
  sorry

end DerivedCategory
