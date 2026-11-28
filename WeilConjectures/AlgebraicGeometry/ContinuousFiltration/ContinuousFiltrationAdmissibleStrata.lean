/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousModuleEncodingUniverses
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelOpenClosedBasic
public import WeilConjectures.AlgebraicGeometry.LatticePullbackProof.ContinuousCoefficientPullbackIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Reduced.ReducedSourceFactors
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedLocalizationSequence
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousModuleOpenRestriction
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.AlgebraicGeometry.Open.LocallyClosedExtensionConstantModelConstructible

/-! # Continuous coefficient filtrations with admissible strata

## Implementation details

* The compatible norm on a finite extension is its unique extended p-adic norm.
* The continuous coefficient ring is the lattice presentation `ULift C(|U|, E)`, canonically
  the localization of the completed integral coefficients.
* Open pieces (`piece`, `counit`) use the actual slice restriction and extension-by-zero counit.

## References

* Bhatt--Scholze, Definitions 6.8.1, 6.8.3, 6.8.6 and 6.8.10, Lemmas 6.8.2 and 6.8.13,
  Proposition 6.8.14(2), Remark 6.8.15.
* Stacks Project, Tags 09BN, 03D6 and 03DI.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace Topology.FiniteLocallyClosedStratification

variable {X : Type*} [TopologicalSpace X]

open TopologicalSpace

/-- A nonempty closed subset of a Noetherian space meets some open set in a nonempty subset
of a single stratum. -/
theorem exists_isOpen_inter_subset_stratum [NoetherianSpace X]
    (s : FiniteLocallyClosedStratification X) (Z : Closeds X) (hZ : (Z : Set X).Nonempty) :
    ∃ (O : Set X) (a : Fin s.n), IsOpen O ∧ (O ∩ Z).Nonempty ∧ O ∩ Z ⊆ s.stratum a := by
  classical
  obtain ⟨S, hS, hZS⟩ := NoetherianSpace.exists_finset_irreducible Z
  have hZS' : (Z : Set X) = ⋃ C ∈ S, (C : Set X) := by
    rw [hZS, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    rfl
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [hZS'] at hZ
  obtain ⟨C, hCS, hCmax⟩ := S.exists_maximal hSne
  have hC : IsIrreducible (C : Set X) := hS ⟨C, hCS⟩
  have hcov : (C : Set X) ⊆ ⋃₀ ↑(Finset.univ.image
      fun a : Fin s.n ↦ closure ((C : Set X) ∩ s.stratum a)) := by
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (s.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ a)),
      subset_closure ⟨hx, ha⟩⟩
  obtain ⟨_, hmem, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hC _
    (by simp [isClosed_closure]) hcov
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hmem
  obtain ⟨U, K, hU, hK, hUK⟩ := s.isLocallyClosed_stratum a
  have hCK : (C : Set X) ⊆ K :=
    hsub.trans (closure_minimal (Set.inter_subset_right.trans (hUK ▸ Set.inter_subset_right)) hK)
  let D : Set X := ⋃ D ∈ S.erase C, (D : Set X)
  have hD : IsClosed D := isClosed_biUnion_finset fun D _ ↦ D.isClosed
  have hCU : ((C : Set X) ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hC.nonempty
    obtain ⟨y, hyC, hy⟩ := mem_closure_iff.mp (hsub hx) _ isOpen_univ trivial
    exact ⟨y, hy.1, (hUK ▸ hy.2).1⟩
  have hCD : ((C : Set X) ∩ Dᶜ).Nonempty := by
    rw [Set.inter_compl_nonempty_iff]
    intro h
    obtain ⟨_, hmem, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hC
      ((S.erase C).image fun D : Closeds X ↦ (D : Set X))
      (by simp only [Finset.mem_image]; rintro _ ⟨D, -, rfl⟩; exact D.isClosed)
      (by simpa [D, Set.sUnion_image, and_comm] using h)
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨hne, hD'S⟩ := Finset.mem_erase.mp hD'
    exact hne (le_antisymm (hCmax hD'S hsub) hsub)
  refine ⟨U ∩ Dᶜ, a, hU.inter hD.isOpen_compl, ?_, ?_⟩
  · obtain ⟨x, hxC, hxU, hxD⟩ := hC.2 U Dᶜ hU hD.isOpen_compl hCU hCD
    refine ⟨x, ⟨hxU, hxD⟩, ?_⟩
    rw [hZS']
    exact Set.mem_iUnion₂.mpr ⟨C, hCS, hxC⟩
  · rintro x ⟨⟨hxU, hxD⟩, hxZ⟩
    rw [hZS'] at hxZ
    obtain ⟨C', hC'S, hxC'⟩ := Set.mem_iUnion₂.mp hxZ
    by_cases hC' : C' = C
    · subst hC'
      rw [hUK]
      exact ⟨hxU, hCK hxC'⟩
    · exact absurd (Set.mem_iUnion₂.mpr ⟨C', Finset.mem_erase.mpr ⟨hC', hC'S⟩, hxC'⟩) hxD

/-- In a Noetherian space every open `W` starts a finite increasing chain of opens ending in
the whole space whose successive differences each lie in a single stratum. -/
theorem exists_opens_chain_of_le [NoetherianSpace X]
    (s : FiniteLocallyClosedStratification X) (W : Opens X) :
    ∃ (m : ℕ) (V : Fin (m + 1) → Opens X), Monotone V ∧ V 0 = W ∧ V (Fin.last m) = ⊤ ∧
      ∀ k : Fin m, ∃ a : Fin s.n,
        ∀ x ∈ V k.succ, x ∉ V k.castSucc → x ∈ s.stratum a := by
  induction W using WellFoundedGT.induction with
  | _ W ih =>
  by_cases hW : W = ⊤
  · exact ⟨0, fun _ ↦ W, monotone_const, rfl, hW, fun k ↦ k.elim0⟩
  have hZ : ((W.compl : Closeds X) : Set X).Nonempty := by
    rw [Opens.compl, Closeds.coe_mk, Set.nonempty_compl]
    exact fun h ↦ hW (SetLike.coe_injective h)
  obtain ⟨O, a, hO, hOZ, hOs⟩ := s.exists_isOpen_inter_subset_stratum _ hZ
  let W' : Opens X := W ⊔ ⟨O, hO⟩
  have hlt : W < W' := by
    refine lt_of_le_of_ne le_sup_left fun h ↦ ?_
    obtain ⟨x, hxO, hxW⟩ := hOZ
    exact hxW (h ▸ (Or.inr hxO : x ∈ (W : Set X) ∪ O))
  obtain ⟨m, V, hV, hV0, hVl, hVs⟩ := ih W' hlt
  refine ⟨m + 1, Fin.cons W V, ?_, rfl, ?_, ?_⟩
  · rw [Fin.monotone_iff_le_succ]
    intro i
    induction i using Fin.cases with
    | zero => simpa [hV0] using hlt.le
    | succ i => simpa using hV i.castSucc_le_succ
  · rw [← Fin.succ_last, Fin.cons_succ, hVl]
  · intro k
    induction k using Fin.cases with
    | zero =>
      refine ⟨a, fun x hx hxW ↦ hOs ⟨?_, hxW⟩⟩
      simp only [Fin.succ_zero_eq_one, Fin.cons_one, Fin.castSucc_zero, Fin.cons_zero,
        hV0] at hx hxW
      exact (hx.elim (fun h ↦ absurd h hxW) id :)
    | succ k =>
      obtain ⟨b, hb⟩ := hVs k
      exact ⟨b, fun x hx hxW ↦ hb x (by simpa using hx) (by simpa using hxW)⟩

end Topology.FiniteLocallyClosedStratification

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

/-- Given adjunctions `l ⊣ r`, `L ⊣ R` and `K ⊣ T` with `R ⋙ r ≅ T`, the counit of `K ⊣ T`
factors through that of `L ⊣ R`, with cokernel `R ⋙ H ⋙ L` when `cokernel a.counit ≅ H`. -/
theorem exists_counit_factor_cokernel_of_adjunctions
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D]
    {L : D ⥤ C} {R : C ⥤ D} {l : E ⥤ D} {r : D ⥤ E}
    {K : E ⥤ C} {T : C ⥤ E} (a : l ⊣ r) (b : L ⊣ R) (c : K ⊣ T)
    [L.Additive] [PreservesFiniteColimits L]
    (eR : R ⋙ r ≅ T) (H : D ⥤ D) (eQ : cokernel a.counit ≅ H) :
    ∃ d : T ⋙ K ⟶ R ⋙ L,
      d ≫ b.counit = c.counit ∧ Nonempty (cokernel d ≅ R ⋙ H ⋙ L) := by
  let ab := (a.comp b).ofNatIsoRight eR
  let eL := ab.leftAdjointUniq c
  let e : T ⋙ K ≅ R ⋙ r ⋙ l ⋙ L :=
    isoWhiskerLeft T eL.symm ≪≫ isoWhiskerRight eR.symm (l ⋙ L)
  let A := (whiskeringLeft C D D).obj R
  let B := (whiskeringRight C D C).obj L
  let f := B.map (A.map a.counit)
  let d := e.hom ≫ f
  refine ⟨d, ?_, ?_⟩
  · ext M
    have hc := ab.leftAdjointUniq_hom_app_counit c M
    apply (cancel_epi (eL.hom.app (T.obj M))).1
    dsimp only [d, e, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [hc]
    simp [ab, Adjunction.ofNatIsoRight_counit, Adjunction.comp_counit_app, f, A, B]
  · refine ⟨cokernel.mapIso d f e (Iso.refl _) (by simp [d]) ≪≫
      (PreservesCokernel.iso B (A.map a.counit)).symm ≪≫
      B.mapIso (PreservesCokernel.iso A a.counit).symm ≪≫
      isoWhiskerRight (isoWhiskerLeft R eQ) L⟩

/-- Objectwise variant of `exists_counit_factor_cokernel_of_adjunctions`, where the restricted
categories are only identified through an equivalence `G`. -/
theorem exists_counit_factor_cokernel_of_adjunctions_of_equivalence
    {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
    [Abelian C] [Abelian D]
    {L : D ⥤ C} {R : C ⥤ D} {l : E ⥤ D} {r : D ⥤ E}
    {K : E' ⥤ C} {T : C ⥤ E'} (a : l ⊣ r) (b : L ⊣ R) (c : K ⊣ T) (G : E' ≌ E)
    [L.Additive] [PreservesFiniteColimits L]
    (eR : R ⋙ r ≅ T ⋙ G.functor) (H : D ⥤ D) (eQ : cokernel a.counit ≅ H) (M : C) :
    ∃ d : K.obj (T.obj M) ⟶ L.obj (R.obj M),
      d ≫ b.counit.app M = c.counit.app M ∧
        Nonempty (cokernel d ≅ L.obj (H.obj (R.obj M))) := by
  let c' := G.symm.toAdjunction.comp c
  obtain ⟨d, hd, ⟨ed⟩⟩ := exists_counit_factor_cokernel_of_adjunctions a b c' eR H eQ
  refine ⟨K.map (G.unit.app (T.obj M)) ≫ d.app M, ?_, ?_⟩
  · rw [Category.assoc, ← NatTrans.comp_app, hd]
    simp [c', Adjunction.comp_counit_app]
  · let ev := (evaluation C C).obj M
    refine ⟨?_⟩
    exact cokernelEpiComp _ _ ≪≫ (PreservesCokernel.iso ev d).symm ≪≫ ed.app M


/-- In an abelian category, a natural transformation from the cokernel of `f` that composes
with the projection to a pointwise exact epimorphic `g` is an isomorphism. -/
theorem nonempty_cokernel_iso_of_exact {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {P Q H : C ⥤ D} (f : P ⟶ Q) (g : Q ⟶ H) (w : f ≫ g = 0)
    (hg : ∀ M, Epi (g.app M))
    (hex : ∀ M, (ShortComplex.mk (f.app M) (g.app M) (by rw [← NatTrans.comp_app, w]; rfl)).Exact) :
    Nonempty (cokernel f ≅ H) := by
  let φ : cokernel f ⟶ H := cokernel.desc f g w
  have : ∀ M, IsIso (φ.app M) := by
    intro M
    let ev := (evaluation C D).obj M
    have := hg M
    let hc := (hex M).gIsCokernel
    let ψ := cokernelComparison f ev ≫ φ.app M
    have hψ : cokernel.π (f.app M) ≫ ψ = g.app M := by
      rw [← Category.assoc]
      refine (congrArg (· ≫ φ.app M) (π_comp_cokernelComparison f ev)).trans ?_
      dsimp only [ev, evaluation_obj_map]
      rw [← NatTrans.comp_app, cokernel.π_desc]
    have hiso : IsIso ψ := by
      have hm := (hex M).mono_cokernelDesc
      have : ψ = cokernel.desc (f.app M) (g.app M) (by rw [← NatTrans.comp_app, w]; rfl) := by
        apply (cancel_epi (cokernel.π (f.app M))).1
        rw [hψ, cokernel.π_desc]
      have : Epi ψ := epi_of_epi_fac hψ
      have : Mono ψ := by
        rw [‹ψ = _›]
        exact hm
      exact isIso_of_mono_of_epi ψ
    have : φ.app M = (PreservesCokernel.iso ev f).hom ≫ ψ := by
      dsimp only [ψ]
      rw [← Category.assoc, ← PreservesCokernel.iso_inv, Iso.hom_inv_id, Category.id_comp]
    rw [this]
    infer_instance
  have : IsIso φ := NatIso.isIso_of_isIso_app φ
  exact ⟨asIso φ⟩


end CategoryTheory


namespace AlgebraicGeometry.ProEtale
namespace ContinuousFiltration

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E]

/-- The tensor-formula continuous module inverse image, with the canonical coefficient map. -/
def pull {Y X : Scheme.{u}} (f : Y ⟶ X) :
    SheafOfModules.{u + 1} (latticeModuleRing X E) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing Y E) :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  letI := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso f E
  Scheme.proEtaleRingModulePullback f (latticeCoefficientSheaf X E)
    (latticeCoefficientSheaf Y E) (asIso (continuousCoefficientInverseImageMap f E))

/-- The open-support piece `v_!v^*`, in the canonical slice presentation of the open site. -/
def piece {X : Scheme.{u}} (V : X.Opens) :=
  SheafOfModules.overFunctor.{u + 1} (latticeModuleRing X E) (Scheme.ProEt.mk V.ι) ⋙
    Scheme.proEtaleRingedExtensionByZero (Scheme.ProEt.mk V.ι) (latticeCoefficientSheaf X E)

/-- The actual extension-by-zero/restriction counit, without any chosen map into F. -/
def counit {X : Scheme.{u}} (V : X.Opens)
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :
    (piece E V).obj F ⟶ F := by
  classical
  refine (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (latticeModuleRing X E).obj)).symm ?_
  refine
    { app := fun _ => ModuleCat.ofHom
        (DirectSum.toModule _ _ _ (fun _ => LinearMap.id))
      naturality := ?_ }
  intro W W' f
  ext x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of φ x =>
    change (DirectSum.toModule _ _ _ (fun _ => LinearMap.id))
      (SheafOfModules.extensionByZeroPresheafRestrictAdd
        (latticeModuleRing X E) (Scheme.ProEt.mk V.ι)
        ((SheafOfModules.overFunctor _ _).obj F) f (DirectSum.of _ φ x)) =
      F.val.map f ((DirectSum.toModule _ _ _ (fun _ => LinearMap.id))
        (DirectSum.of _ φ x))
    dsimp only [SheafOfModules.extensionByZeroPresheafRestrictAdd]
    erw [DirectSum.toAddMonoid_of, DirectSum.toModule_lof, DirectSum.toModule_lof]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Ordinary continuous closed direct image followed by continuous open extension by zero,
with the stratum object exactly the successive restriction of F. -/
def stratumPiece {X : Scheme.{u}} (V : X.Opens) {S : Scheme.{u}}
    (t : S ⟶ V.toScheme) (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :=
  (continuousModuleExtensionByZero (Scheme.ProEt.mk V.ι) E).obj
    ((continuousModuleDirectImage t E).obj
      ((pull l E t).obj ((pull l E V.ι).obj F)))

/-- A morphism of module sheaves which is bijective on all sections is an isomorphism. -/
theorem _root_.SheafOfModules.isIso_of_bijective_app {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (f : M ⟶ N)
    (hf : ∀ W : Cᵒᵖ, Function.Bijective (f.val.app W)) : IsIso f := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro W
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (hf W)

/-- A module sheaf all of whose sections are subsingletons is zero. -/
theorem _root_.SheafOfModules.isZero_of_subsingleton {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} R) (h : ∀ W : Cᵒᵖ, Subsingleton (M.val.obj W)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext W x
  exact Subsingleton.elim _ _

/-- The counit is the counit of the extension-by-zero/restriction adjunction. -/
private theorem counit_eq_extensionSheafAdjunction_counit {X : Scheme.{u}} (V : X.Opens)
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :
    counit E V F = (SheafOfModules.extensionSheafAdjunction (latticeModuleRing X E)
      (Scheme.ProEt.mk V.ι)).counit.app F := by
  rfl

/-- The open-support counit `v_!v^*F ⟶ F` is a monomorphism. -/
theorem counit_mono {X : Scheme.{u}} (V : X.Opens) [QuasiCompact V.ι]
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :
    Mono (counit E V F) := by
  rw [counit_eq_extensionSheafAdjunction_counit]
  have hU : Set.range (Scheme.ProEt.mk V.ι).hom = (Set.range V.closedComplement)ᶜ := by
    rw [Scheme.Opens.range_closedComplement, compl_compl]
    exact V.range_ι
  have : QuasiCompact (Scheme.ProEt.mk V.ι).hom := inferInstanceAs (QuasiCompact V.ι)
  have : IsOpenImmersion (Scheme.ProEt.mk V.ι).hom := inferInstanceAs (IsOpenImmersion V.ι)
  obtain ⟨-, -, ai, -⟩ := Scheme.proEtale_ringed_open_closed V.closedComplement
    (Scheme.ProEt.mk V.ι) hU (latticeCoefficientSheaf X E)
  exact (Scheme.proEtale_ringed_localization_sequence V.closedComplement
    (Scheme.ProEt.mk V.ι) hU (latticeCoefficientSheaf X E) ai
    (SheafOfModules.extensionSheafAdjunction _ _) F).1

/-- The open-support piece of the empty open is zero. -/
theorem isZero_piece_bot {X : Scheme.{u}} (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :
    IsZero ((piece E (⊥ : X.Opens)).obj F) := by
  let adj := SheafOfModules.extensionSheafAdjunction (latticeModuleRing X E)
    (Scheme.ProEt.mk (⊥ : X.Opens).ι)
  have : (Scheme.proEtaleRingedExtensionByZero (Scheme.ProEt.mk (⊥ : X.Opens).ι)
      (latticeCoefficientSheaf X E)).IsLeftAdjoint := adj.isLeftAdjoint
  refine Functor.map_isZero (Scheme.proEtaleRingedExtensionByZero
    (Scheme.ProEt.mk (⊥ : X.Opens).ι) (latticeCoefficientSheaf X E))
    (SheafOfModules.isZero_of_subsingleton ((SheafOfModules.overFunctor _ _).obj F) fun W ↦ ?_)
  have : IsEmpty W.unop.left.left := ⟨fun x ↦ Set.notMem_empty _ (W.unop.hom.left x).2⟩
  exact Scheme.module_empty_sections _ F W.unop.left

/-- The open-support counit of the whole scheme is an isomorphism. -/
theorem isIso_counit_top {X : Scheme.{u}}
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :
    IsIso (counit E (⊤ : X.Opens) F) := by
  rw [counit_eq_extensionSheafAdjunction_counit]
  have : IsOpenImmersion (Scheme.ProEt.mk (⊤ : X.Opens).ι).hom :=
    inferInstanceAs (IsOpenImmersion (⊤ : X.Opens).ι)
  refine SheafOfModules.isIso_of_bijective_app _ fun W ↦ ?_
  exact SheafOfModules.counit_bijective_on_open _ _ _ F W.unop
    (MorphismProperty.Over.homMk (W.unop.hom ≫ X.topIso.inv) (by simp))

/-- The slice transport of continuous-coefficient modules is an equivalence. -/
noncomputable def openSliceEquivalence {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing U.left T) ≌
      SheafOfModules.{u + 1} ((latticeModuleRing X T).over U) := by
  letI := Scheme.ProEt.sliceDense X U
  letI : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  exact SheafOfModules.pushforwardPushforwardEquivalence (Scheme.ProEt.sliceEquiv X U)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
    (by ext V : 2; exact ((latticeModuleRing U.left T).obj.map_id V).trans rfl)
    (by ext V : 2; exact (((latticeModuleRing X T).over U).obj.map_id V).trans (by simp))


set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars along a ring isomorphism agrees with the pushforward of the
scalar equivalence. -/
private noncomputable def restrictScalarsIsoScalarEquivalence {X : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (c : A ≅ B) :
    SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom) ≅
      (Scheme.proEtaleScalarEquivalence X ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)).functor :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl))) (by
      intro M N a
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      rfl)

/-- The tensor inverse image followed by the continuous direct image along `t` is the
module inverse image followed by the ringed direct image. -/
private noncomputable def pullCompDirectImageIso {Y S : Scheme.{u}} (t : S ⟶ Y) :
    pull l E t ⋙ continuousModuleDirectImage t E ≅
      Scheme.proEtaleModuleInverseImage t (latticeCoefficientSheaf Y E) ⋙
        Scheme.proEtaleRingedDirectImage t (latticeCoefficientSheaf Y E) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : IsIso (continuousCoefficientInverseImageMap t E) :=
    LatticePullbackProof.continuousCoefficientInverseImageMap_isIso t E
  let c := asIso (continuousCoefficientInverseImageMap t E)
  let A := latticeCoefficientSheaf Y E
  let e := Scheme.proEtaleScalarEquivalence S ((sheafCompose (Scheme.ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  let adj := (Scheme.proEtaleRingExtensionAdjunction t A (latticeCoefficientSheaf S E)
    c).ofNatIsoRight
    (restrictScalarsIsoScalarEquivalence c)
  let q := adj.leftAdjointUniq e.symm.toAdjunction
  let p : pull l E t ≅ Scheme.proEtaleModuleInverseImage t A ⋙ e.inverse :=
    Functor.isoWhiskerLeft (Scheme.proEtaleModuleInverseImage t A) q
  let D := Scheme.proEtaleRingedDirectImage t A
  let rs := SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)
  let r : continuousModuleDirectImage t E ≅ rs ⋙ D := Iso.refl _
  exact Functor.isoWhiskerRight p _ ≪≫ Functor.isoWhiskerLeft _ r ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft e.inverse (restrictScalarsIsoScalarEquivalence c) ≪≫
          e.counitIso) D ≪≫ Functor.leftUnitor D)


/-- For an open `U` with closed complement `t`, the cokernel of the extension-by-zero counit
is the continuous direct image of the continuous inverse image along `t`. -/
private theorem nonempty_cokernel_counit_iso {Y S : Scheme.{u}} (U : Y.ProEt)
    [IsOpenImmersion U.hom]
    [QuasiCompact U.hom] (t : S ⟶ Y) [IsClosedImmersion t]
    (hU : Set.range U.hom = (Set.range t)ᶜ) :
    Nonempty (cokernel (SheafOfModules.extensionSheafAdjunction (latticeModuleRing Y E) U).counit ≅
      pull l E t ⋙ continuousModuleDirectImage t E) := by
  let A := latticeCoefficientSheaf Y E
  let aj := SheafOfModules.extensionSheafAdjunction (latticeModuleRing Y E) U
  obtain ⟨-, -, ai, -⟩ := Scheme.proEtale_ringed_open_closed t U hU A
  have hs := Scheme.proEtale_ringed_localization_sequence t U hU A ai aj
  have w : aj.counit ≫ ai.unit = 0 := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    rw [NatTrans.comp_app, NatTrans.app_zero]
    exact (hs M).2.2.toIsComplex.zero 0
  obtain ⟨e⟩ := nonempty_cokernel_iso_of_exact aj.counit ai.unit w (fun M ↦ (hs M).2.1)
    (fun M ↦ (hs M).2.2.exact 0)
  exact ⟨e ≪≫ (pullCompDirectImageIso l E t).symm⟩



/-- The adjoint of the canonical inverse-image coefficient map is the canonical direct-image
coefficient map. -/
theorem proEtaleRingDirectImageMap_continuous {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [IsIso (continuousCoefficientInverseImageMap f T)] :
    Scheme.proEtaleRingDirectImageMap f (latticeCoefficientSheaf Y T)
      (latticeCoefficientSheaf X T) (asIso (continuousCoefficientInverseImageMap f T)) =
        continuousCoefficientDirectImageMap f T := by
  rw [Scheme.proEtaleRingDirectImageMap, asIso_hom, continuousCoefficientInverseImageMap,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem nonempty_continuousRestriction_iso_pull {X : Scheme.{u}} (U : X.ProEt) :
    Nonempty (continuousRestriction U E ≅ pull l E U.hom) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : IsIso (continuousCoefficientInverseImageMap U.hom E) :=
    LatticePullbackProof.continuousCoefficientInverseImageMap_isIso U.hom E
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap U.prop
  let P := Scheme.proEtaleBaseChange U.hom
  let : P.IsContinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology U.left) :=
    Scheme.proEtaleBaseChange_isContinuous U.hom
  let a : G ⊣ P := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let φ : latticeModuleRing U.left E ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X)).obj (latticeModuleRing X E) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let ψ : latticeModuleRing X E ⟶ (P.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology U.left)).obj
        (latticeModuleRing U.left E) :=
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (continuousCoefficientDirectImageMap U.hom E)
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) (latticeModuleRing X E).obj =
      ψ.hom ≫ P.op.whiskerLeft φ.hom := by
    ext V s
    apply ULift.ext
    ext x
    rfl
  have H₂ : φ.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) (latticeModuleRing U.left E).obj =
        𝟙 (latticeModuleRing U.left E).obj := by
    ext W s
    apply ULift.ext
    ext x
    have h : (a.unit.app W.unop).left ≫ pullback.fst _ _ = 𝟙 _ := by
      simp only [a]
      exact pullback.lift_fst _ _ _
    exact congrArg (fun g ↦ s.down (g x)) h
  let d := SheafOfModules.pushforwardPushforwardAdj a φ ψ H₁ H₂
  let adj := Scheme.proEtaleRingModuleAdjunction U.hom (latticeCoefficientSheaf X E)
    (latticeCoefficientSheaf U.left E) (asIso (continuousCoefficientInverseImageMap U.hom E))
  have hψ : SheafOfModules.pushforward.{u + 1} ψ ≅ Scheme.proEtaleRingModuleDirectImage U.hom
      (latticeCoefficientSheaf X E) (latticeCoefficientSheaf U.left E)
        (asIso (continuousCoefficientInverseImageMap U.hom E)) :=
    SheafOfModules.pushforwardCongr (by
      exact congrArg (fun m ↦ (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map m)
          (proEtaleRingDirectImageMap_continuous U.hom E).symm)
  exact ⟨d.leftAdjointUniq (adj.ofNatIsoRight hψ.symm)⟩


set_option backward.isDefEq.respectTransparency false in
/-- Restricting from `X` to `T` and then to `W ≤ T` is restricting from `X` to `W`. -/
private noncomputable def continuousRestrictionCompIso {X : Scheme.{u}} {W T : X.Opens}
    (h : W ≤ T) :
    continuousRestriction (Scheme.ProEt.mk T.ι) E ⋙
        continuousRestriction (Scheme.ProEt.mk (X.homOfLE h)) E ≅
      continuousRestriction (Scheme.ProEt.mk W.ι) E := by
  let GT : T.toScheme.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ (Scheme.ProEt.mk T.ι).prop
  let G' : W.toScheme.ProEt ⥤ T.toScheme.ProEt :=
    MorphismProperty.Over.map ⊤ (Scheme.ProEt.mk (X.homOfLE h)).prop
  let GW : W.toScheme.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ (Scheme.ProEt.mk W.ι).prop
  let : GT.IsContinuous (Scheme.ProEt.topology T.toScheme) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (Scheme.ProEt.mk T.ι).prop
  let : G'.IsContinuous (Scheme.ProEt.topology W.toScheme) (Scheme.ProEt.topology T.toScheme) :=
    Scheme.ProEt.isContinuous_overMap (Scheme.ProEt.mk (X.homOfLE h)).prop
  let : GW.IsContinuous (Scheme.ProEt.topology W.toScheme) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (Scheme.ProEt.mk W.ι).prop
  let : (G' ⋙ GT).IsContinuous (Scheme.ProEt.topology W.toScheme) (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology T.toScheme) _
  let e : G' ⋙ GT ≅ GW := NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      simp [GT, G', GW, Scheme.homOfLE_ι])) (by
        intro V V' f
        apply MorphismProperty.Over.Hom.ext
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
  let φ : latticeModuleRing W.toScheme E ⟶ (GW.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology W.toScheme) (Scheme.ProEt.topology X)).obj
        (latticeModuleRing X E) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let φ₁ : latticeModuleRing W.toScheme E ⟶ (G'.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology W.toScheme) (Scheme.ProEt.topology T.toScheme)).obj
        (latticeModuleRing T.toScheme E) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let ψ₁ : latticeModuleRing T.toScheme E ⟶ (GT.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology T.toScheme) (Scheme.ProEt.topology X)).obj
        (latticeModuleRing X E) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  refine SheafOfModules.pushforwardComp φ₁ ψ₁ ≪≫ ?_
  refine SheafOfModules.pushforwardCongr ?_ ≪≫ (SheafOfModules.pushforwardCongr₂ φ e
    (by ext V s; rfl)).symm
  ext V s
  rfl



/-- For nested opens `W ≤ T` with `t` a closed immersion onto `T \ W`, the counit of `W`
factors through that of `T`, and the cokernel of the factorization is the stratum piece. -/
theorem exists_counit_factor_cokernel {X : Scheme.{u}} (W T : X.Opens) (hWT : W ≤ T)
    [QuasiCompact W.ι] [QuasiCompact T.ι] {S : Scheme.{u}} (t : S ⟶ T.toScheme)
    [IsClosedImmersion t] (ht : Set.range t = {x | T.ι x ∉ W})
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :
    ∃ d : (piece E W).obj F ⟶ (piece E T).obj F,
      d ≫ counit E T F = counit E W F ∧
        Nonempty (cokernel d ≅ stratumPiece l E T t F) := by
  let R := latticeModuleRing X E
  let UT := Scheme.ProEt.mk T.ι
  let UW := Scheme.ProEt.mk W.ι
  let U' : T.toScheme.ProEt := Scheme.ProEt.mk (X.homOfLE hWT)
  have : IsOpenImmersion U'.hom := inferInstanceAs (IsOpenImmersion (X.homOfLE hWT))
  have : QuasiCompact U'.hom := by
    have : QuasiCompact (X.homOfLE hWT ≫ T.ι) := by
      rw [X.homOfLE_ι hWT]
      infer_instance
    exact QuasiCompact.of_comp (X.homOfLE hWT) T.ι
  have hU' : Set.range (X.homOfLE hWT) = (Set.range t)ᶜ := by
    rw [ht]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
    constructor
    · rintro ⟨w, rfl⟩
      rw [← Scheme.Hom.comp_apply, X.homOfLE_ι hWT]
      exact w.property
    · intro hx
      refine ⟨⟨x.val, hx⟩, T.ι.isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, X.homOfLE_ι hWT]
      rfl
  let ΦT := openSliceEquivalence UT E
  let ΦW := openSliceEquivalence UW E
  let Φ' := openSliceEquivalence U' E
  let ajT := SheafOfModules.extensionSheafAdjunction R UT
  let ajW := SheafOfModules.extensionSheafAdjunction R UW
  let b := ΦT.toAdjunction.comp ajT
  let a := SheafOfModules.extensionSheafAdjunction (latticeModuleRing T.toScheme E) U'
  let G := ΦW.symm.trans Φ'
  let OT := SheafOfModules.overFunctor R UT
  let OW := SheafOfModules.overFunctor R UW
  let O' := SheafOfModules.overFunctor (latticeModuleRing T.toScheme E) U'
  let ρT := continuousRestriction UT E
  let ρW := continuousRestriction UW E
  let ρ' := continuousRestriction U' E
  let eT : OT ⋙ ΦT.inverse ≅ ρT :=
    Functor.isoWhiskerRight (restrictionToSlice UT E).symm ΦT.inverse ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft ρT ΦT.unitIso.symm ≪≫ Functor.rightUnitor _
  let eW : OW ⋙ ΦW.inverse ≅ ρW :=
    Functor.isoWhiskerRight (restrictionToSlice UW E).symm ΦW.inverse ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft ρW ΦW.unitIso.symm ≪≫ Functor.rightUnitor _
  let eR : (OT ⋙ ΦT.inverse) ⋙ O' ≅ OW ⋙ G.functor :=
    Functor.isoWhiskerRight eT O' ≪≫ Functor.isoWhiskerLeft ρT (restrictionToSlice U' E).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (continuousRestrictionCompIso E hWT) Φ'.functor ≪≫
      Functor.isoWhiskerRight eW.symm Φ'.functor ≪≫ Functor.associator _ _ _
  obtain ⟨eQ⟩ := nonempty_cokernel_counit_iso l E U' t hU'
  let L := ΦT.functor ⋙ (SheafOfModules.extensionByZeroPresheaf R UT ⋙
    PresheafOfModules.sheafification (𝟙 R.obj))
  have : PreservesColimitsOfSize.{0, 0} L := b.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  have : L.Additive := L.additive_of_preservesBinaryBiproducts
  obtain ⟨d, hd, ⟨ed⟩⟩ := exists_counit_factor_cokernel_of_adjunctions_of_equivalence a b ajW G eR
    (pull l E t ⋙ continuousModuleDirectImage t E) eQ F
  obtain ⟨eΩ⟩ := nonempty_continuousRestriction_iso_pull l E UT
  let LT := Scheme.proEtaleRingedExtensionByZero UT (latticeCoefficientSheaf X E)
  refine ⟨d ≫ LT.map (ΦT.counitIso.hom.app (OT.obj F)), ?_, ⟨?_⟩⟩
  · rw [Category.assoc]
    exact hd
  · exact cokernelCompIsIso _ _ ≪≫ ed ≪≫ LT.mapIso (ΦT.functor.mapIso
      ((pull l E t ⋙ continuousModuleDirectImage t E).mapIso (eT.app F ≪≫ eΩ.app F)))

end ContinuousFiltration

/-- A morphism from a reduced scheme whose range lies in the range of an immersion factors
through it. -/
theorem exists_factor_immersion_of_isReduced {Y Z X : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) (i : Z ⟶ X) [IsImmersion i]
    (h : Set.range f ⊆ Set.range i) : ∃ g : Y ⟶ Z, g ≫ i = f := by
  let f' : Y ⟶ i.coborderRange.toScheme :=
    IsOpenImmersion.lift i.coborderRange.ι f (h.trans (by simpa using! subset_coborder))
  have hf' : f' ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  have h' : Set.range f' ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := h (Set.mem_range_self y)
    refine ⟨z, ?_⟩
    apply i.coborderRange.ι.isOpenEmbedding.injective
    change (i.liftCoborder ≫ i.coborderRange.ι) z = (f' ≫ i.coborderRange.ι) y
    rw [i.liftCoborder_ι, hf']
    exact hz
  obtain ⟨g, hg⟩ :=
    (reduced_source_factors_through_closed_subscheme i.liftCoborder f').1.mpr h'
  refine ⟨g, ?_⟩
  rw [← i.liftCoborder_ι, ← Category.assoc, hg, hf']

/-- `l` stays invertible in the stalks after pulling back along any morphism. -/
theorem isUnit_natCast_stalk {Y X : Scheme.{u}} (f : Y ⟶ X) (l : ℕ)
    (hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) (y : Y) :
    IsUnit (l : Y.presheaf.stalk y) := by
  simpa using (hl (f y)).map (f.stalkMap y).hom

/-- An immersion into a Noetherian scheme has Noetherian source. -/
theorem isNoetherian_of_isImmersion {Y X : Scheme.{u}} (f : Y ⟶ X) [IsImmersion f]
    [IsNoetherian X] : IsNoetherian Y := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : TopologicalSpace.NoetherianSpace Y := f.isEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

/-- A morphism out of a topologically Noetherian scheme is quasi-compact. -/
theorem quasiCompact_of_noetherianSpace {Y X : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y]
    (f : Y ⟶ X) : QuasiCompact f :=
  ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.ContinuousRingUniverse

open Opposite MonoidalCategory MonObj

attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sectionwise precomposition with the base-change projection, as a map of abelian sheaves
of continuous functions into the direct image. -/
noncomputable def directImageMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type u) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousCoefficientRingSheaf X O) ⟶
    (ProEtale.lowerStar Ab.{u + 1} f).obj
      ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousCoefficientRingSheaf Y O)) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ULift.up
            (s.down.comp (pullback.fst U.unop.hom f).base.hom)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro U V g
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       change (s.down.comp g.unop.left.base.hom).comp
         (pullback.fst V.unop.hom f).base.hom =
           (s.down.comp (pullback.fst U.unop.hom f).base.hom).comp
             ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left.base.hom
       have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
           pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ g.unop.left := by
         exact pullback.lift_fst _ _ _
       ext x
       exact congrArg (fun h : pullback V.unop.hom f ⟶ U.unop.left ↦ s.down (h x)) h.symm }⟩

/-- Sections of `directImageMap` are precomposed with the base-change projection. -/
theorem directImageMap_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type u) [TopologicalSpace O] [Ring O] [IsTopologicalRing O]
    (U : X.ProEt) (s : ULift.{u + 1} C(U.left, O)) :
    ((directImageMap f O).hom.app (op U)) s =
      ULift.up (s.down.comp (pullback.fst U.hom f).base.hom) := rfl

/-- The universe continuous coefficient comparison commutes with scheme direct image. -/
theorem comparison_lowerStar_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type u) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    condensedPushforwardHom (Profinite.continuousMapRingObjOfUniverse O) f ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (comparison Y O) =
    comparison X O ≫ directImageMap f O := by
  let adjX := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  let CY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf Y O)
  have hleft := CondensedRing.chartMate_homEquiv f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)
    (pointUpperStar.obj (Profinite.continuousMapRingObjOfUniverse O)) CY (comparison Y O)
  rw [← condensedPullbackHom_eq (Profinite.continuousMapRingObjOfUniverse O) f] at hleft
  apply (adjX.homEquiv _ _).injective
  conv_rhs => rw [adjX.homEquiv_naturality_right]
  have hchart : adjX.homEquiv _ _ (comparison X O) =
      comparisonAdjoint X O := by
    rw [comparison]; exact Equiv.apply_symm_apply _ _
  rw [hchart]
  simp only [adjX, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [← unitAlgHom_comp_map_condensedPullbackHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  have hchartY :
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))).homEquiv _ _
          (comparison Y O) = comparisonAdjoint Y O := by
    rw [comparison]; exact Equiv.apply_symm_apply _ _
  simp only [Adjunction.comp_homEquiv] at hchartY
  erw [hchartY]
  ext S s
  apply ULift.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change ((((lowerStarFactor Ab.{u + 1} (comp_toSpecZ f)).inv.app CY).hom.app
    (op (profiniteToProEt.obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection Y S.unop)))).down =
    (((directImageMap f O).hom.app
      (op ((profiniteToProEtOf X).obj S.unop)))
        (ULift.up (s.down.comp (profiniteTestProjection X S.unop)))).down
  rw [lowerStarFactor_inv_app_hom_app, directImageMap_app]
  change (s.down.comp (profiniteTestProjection Y S.unop)).comp
      (((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left.base.hom) =
    (s.down.comp (profiniteTestProjection X S.unop)).comp
      (pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f).base.hom
  have hp :
      ((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Y) =
      pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ X) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    dsimp only [pullback.map]
    erw [Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    rfl
  have hp' := congrArg (fun g ↦ g.base.hom) hp
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
  simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
  rw [hp']

end AlgebraicGeometry.ProEtale.ContinuousRingUniverse

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Opposite MonoidalCategory MonObj
open ContinuousRingUniverse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-- Evaluating a right whiskering followed by a map on a pure tensor. -/
theorem whiskerRight_comp_apply {A A' B C : Ab.{u + 1}} (d : A ⟶ A')
    (g : A' ⊗ B ⟶ C) (a : A) (b : B) :
    (d ▷ B ≫ g) (a ⊗ₜ[ℤ] b) = g (d a ⊗ₜ[ℤ] b) := by
  rw [ConcreteCategory.comp_apply, AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]

variable {Y Z : Scheme.{u}} (i : Z ⟶ Y) (T : Type u) [CommRing T] [TopologicalSpace T]
  [IsTopologicalRing T] [TotallyDisconnectedSpace T]

/-- The universe section-action encoding intertwines the condensed direct image with the
sectionwise ringed direct image, for any coefficient identification whose adjoint ring map is
precomposition with the base-change projection. -/
noncomputable def lowerStarEncodingIso
    (c : (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf Y T) ≅ latticeCoefficientSheaf Z T)
    (hc : Scheme.proEtaleRingDirectImageMap i _ _ c = continuousCoefficientDirectImageMap i T) :
    lowerStar (Profinite.continuousCoefficientRingObj T) i ⋙
        (continuousLatticeModuleEquivalenceUniverse Y T).functor ≅
      (continuousLatticeModuleEquivalenceUniverse Z T).functor ⋙
        Scheme.proEtaleRingModuleDirectImage i _ _ c := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro r
      ext m
      let Λ := Profinite.continuousCoefficientRingObj T
      let AY := (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf Y T)
      let AZ := (sheafCompose (Scheme.ProEt.topology Z)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf Z T)
      let φY : condensedRingObj Λ Y ⟶ AY := ContinuousRingUniverse.comparison Y T
      let φZ : condensedRingObj Λ Z ⟶ AZ := ContinuousRingUniverse.comparison Z T
      have : IsIso φY := ContinuousRingUniverse.comparison_isIso Y T
      have : IsIso φZ := ContinuousRingUniverse.comparison_isIso Z T
      let P := ProEtale.lowerStar Ab.{u + 1} i
      let U' := op ((Scheme.proEtaleBaseChange i).obj U.unop)
      let D := ContinuousRingUniverse.directImageMap i T
      conv_rhs =>
        change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          AY (P.obj M.X)).app U ≫ ((inv φY ▷ P.obj M.X ≫
            condensedPushforwardHom Λ i ▷ P.obj M.X ≫
            Functor.LaxMonoidal.μ P (condensedRingObj Λ Z) M.X ≫
              P.map (Mod.act M.X)).hom.app U)) (r ⊗ₜ[ℤ] m)
      conv_lhs =>
        change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          AZ M.X).app U' ≫ ((inv φZ ▷ M.X ≫ Mod.act M.X).hom.app U'))
          (((Scheme.proEtaleRingDirectImageMap i _ _ c).hom.app U).hom r ⊗ₜ[ℤ] m)
      rw [hc]
      have hA : condensedPushforwardHom Λ i ≫ P.map φZ = φY ≫ D :=
        ContinuousRingUniverse.comparison_lowerStar_naturality i T
      have hcY : inv φY ≫ condensedPushforwardHom Λ i = D ≫ P.map (inv φZ) := by
        rw [IsIso.inv_comp_eq, ← reassoc_of% hA, ← P.map_comp, IsIso.hom_inv_id, P.map_id,
          Category.comp_id]
      have key : (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          AY (P.obj M.X)).app U ≫ ((inv φY ▷ P.obj M.X ≫
            condensedPushforwardHom Λ i ▷ P.obj M.X ≫
            Functor.LaxMonoidal.μ P (condensedRingObj Λ Z) M.X ≫
              P.map (Mod.act M.X)).hom.app U) =
          (D.hom.app U ▷ (P.obj M.X).obj.obj U) ≫
          (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
            AZ M.X).app U' ≫ ((inv φZ ▷ M.X ≫ Mod.act M.X).hom.app U') := by
        rw [← MonoidalCategory.comp_whiskerRight_assoc, hcY,
          MonoidalCategory.comp_whiskerRight_assoc,
          Functor.LaxMonoidal.μ_natural_left_assoc, ← P.map_comp]
        have h1 := congr_app (Functor.LaxMonoidal.μ_natural_left
          (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) D (P.obj M.X)) U
        have h2 := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i) Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z) AZ M.X U
        simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h1 ⊢
        have h1' : (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
            AY (P.obj M.X)).app U ≫ (D ▷ P.obj M.X).hom.app U =
            (D.hom.app U ▷ (P.obj M.X).obj.obj U) ≫
              (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
                (P.obj AZ) (P.obj M.X)).app U := h1.symm
        have h2' : (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
                (P.obj AZ) (P.obj M.X)).app U ≫
              (Functor.LaxMonoidal.μ P AZ M.X).hom.app U =
            (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
              AZ M.X).app U' := h2
        rw [reassoc_of% h1', reassoc_of% h2']
        rfl
      have key2 := ConcreteCategory.congr_hom key (r ⊗ₜ[ℤ] m)
      exact (key2.trans (whiskerRight_comp_apply _ _ _ _)).symm
    · intro U V f
      ext
      rfl
  · intro M N f
    ext U m
    rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- An iso `L ⋙ eY.functor ≅ eZ.functor ⋙ G` through equivalences gives an iso
`G ⋙ eY.inverse ≅ eZ.inverse ⋙ L`. -/
noncomputable def isoInverseOfFunctorIso {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D] (eY : A ≌ B) (eZ : C ≌ D) (L : C ⥤ A) (G : D ⥤ B)
    (K : L ⋙ eY.functor ≅ eZ.functor ⋙ G) :
    G ⋙ eY.inverse ≅ eZ.inverse ⋙ L :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight eZ.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft eZ.inverse
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight K.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L eY.unitIso.symm ≪≫
          Functor.rightUnitor L)

namespace CondensedRing

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The universe section-action encoding identifies the regular module with the unit. -/
def continuousRingUniverseRegularIso (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    (continuousLatticeModuleEquivalenceUniverse X T).functor.obj
        (Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) ≅
      SheafOfModules.unit (latticeModuleRing X T) := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let J := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ by
      exact @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} T
  let φ := ContinuousRingUniverse.comparison X T
  letI := ContinuousRingUniverse.comparison_isIso X T
  let F := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J A
  let G := ringModuleEquivalenceOfIso X (reconstructedRingIso X R).symm
  let H := ringModuleEquivalenceOfIso X (continuousSectionRingIso X T)
  exact H.functor.mapIso (G.functor.mapIso (F.functor.mapIso
    (Mod.regularIsoOfIsIso φ) ≪≫ sectionModuleRegularIso X A) ≪≫
      ringModuleUnitIso X (reconstructedRingIso X R).symm) ≪≫
    ringModuleUnitIso X (continuousSectionRingIso X T)

/-- The universe section-action encoding identifies finite free modules with free sheaves. -/
def continuousRingUniverseFreeIso (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (n : ℕ) :
    (continuousLatticeModuleEquivalenceUniverse X T).functor.obj
        (Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj T) X) n) ≅
      SheafOfModules.free (R := latticeModuleRing X T) (ULift.{u + 1} (Fin n)) := by
  let F := (continuousLatticeModuleEquivalenceUniverse X T).functor
  letI : PreservesBiproduct (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X)) F :=
    preservesBiproduct_of_preservesCoproduct F
  exact F.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ continuousRingUniverseRegularIso X T) ≪≫
    biproduct.isoCoproduct _ ≪≫
      (Sigma.reindex Equiv.ulift (fun _ : Fin n ↦
        SheafOfModules.unit (latticeModuleRing X T))).symm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]

/-- The section-action encoding retains the underlying abelian sheaf. -/
def continuousFieldModuleEquivalenceUniverseToSheafIso (T : Scheme.{u}) :
    (continuousFieldModuleEquivalenceUniverse l E T).functor ⋙
        SheafOfModules.toSheaf (latticeModuleRing T E) ≅
      Mod.forget (condensedRingObj (Profinite.continuousCoefficientRingObj E) T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The section-action encoding sends the finite free module of rank `n` to the free module
sheaf on `n` generators. -/
theorem nonempty_continuousFieldModuleEquivalenceUniverse_finiteFree_iso
    (T : Scheme.{u}) (n : ℕ) :
    Nonempty ((continuousFieldModuleEquivalenceUniverse l E T).functor.obj
        (Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) T) n) ≅
      SheafOfModules.free (R := latticeModuleRing T E) (ULift.{u + 1} (Fin n))) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  exact ⟨continuousRingUniverseFreeIso T E n⟩

/-- The section-action encoding intertwines condensed inverse image along any morphism with
the continuous tensor inverse image. -/
theorem nonempty_upperStar_comp_continuousFieldModuleEquivalenceUniverse_iso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) :
    Nonempty (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E) i ⋙
        (continuousFieldModuleEquivalenceUniverse l E Z).functor ≅
      (continuousFieldModuleEquivalenceUniverse l E Y).functor ⋙
        ContinuousFiltration.pull l E i) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso i E
  let c := asIso (continuousCoefficientInverseImageMap i E)
  let EY := continuousLatticeModuleEquivalenceUniverse Y E
  let EZ := continuousLatticeModuleEquivalenceUniverse Z E
  let adj1 := (upperStarLowerStarAdjunction (Profinite.continuousCoefficientRingObj E) i).comp
    EZ.toAdjunction
  let adj2 : EY.functor ⋙ ContinuousFiltration.pull l E i ⊣
      Scheme.proEtaleRingModuleDirectImage i _ _ c ⋙ EY.inverse :=
    EY.toAdjunction.comp (Scheme.proEtaleRingModuleAdjunction i _ _ c)
  let K := lowerStarEncodingIso i E c
    (ContinuousFiltration.proEtaleRingDirectImageMap_continuous i E)
  exact ⟨(conjugateIsoEquiv adj2 adj1).symm (isoInverseOfFunctorIso EY EZ _ _ K)⟩

end CondensedRing

namespace CondensedRing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]

/-- The slice transport of continuous-coefficient modules preserves the unit module. -/
def openSliceUnitIso {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.unit ((latticeModuleRing X T).over U) ≅
      (ContinuousFiltration.openSliceEquivalence U T).functor.obj
        (SheafOfModules.unit (latticeModuleRing U.left T)) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun Z ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext m
    rfl
  · intro Z Z' a
    ext
    rfl

/-- Transport of "isomorphic to a free object of some finite rank" along an equivalence which
sends the finite free objects to the free ones. -/
theorem exists_iso_free_iff_of_equivalence {A B : Type*} [Category* A] [Category* B]
    (G : A ≌ B) (FA : ℕ → A) (FB : ℕ → B) (hF : ∀ n, G.functor.obj (FA n) ≅ FB n)
    {M : B} {Q : A} (em : M ≅ G.functor.obj Q) :
    (∃ n : ℕ, Nonempty (M ≅ FB n)) ↔ ∃ n : ℕ, Nonempty (Q ≅ FA n) := by
  constructor
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨G.fullyFaithfulFunctor.preimageIso (em.symm ≪≫ en ≪≫ (hF n).symm)⟩⟩
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨em ≪≫ G.functor.mapIso en ≪≫ hF n⟩⟩


/-- The restriction of the section-action encoding to a pro-etale slice is the slice transport of
the encoding of the condensed inverse image. -/
theorem nonempty_over_continuousFieldModuleEquivalenceUniverse_iso (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (W : X.ProEt) :
    Nonempty (((continuousFieldModuleEquivalenceUniverse l E X).functor.obj P).over W ≅
      ((continuousFieldModuleEquivalenceUniverse l E W.left).trans
        (ContinuousFiltration.openSliceEquivalence W E)).functor.obj
          ((upperStar (Profinite.continuousCoefficientRingObj E) W.hom).obj P)) := by
  obtain ⟨e4⟩ := nonempty_upperStar_comp_continuousFieldModuleEquivalenceUniverse_iso l E W.hom
  obtain ⟨eΩ⟩ := ContinuousFiltration.nonempty_continuousRestriction_iso_pull l E W
  exact ⟨((restrictionToSlice W E).app _).symm ≪≫
    (ContinuousFiltration.openSliceEquivalence W E).functor.mapIso
      (eΩ.app _ ≪≫ (e4.app P).symm)⟩

/-- Freeness of a module object over the condensed coefficients of `W` is equivalent to
freeness of its raw abelian inverse image over the pulled-back coefficients. -/
theorem continuousField_isFree_upperStar_iff_isFree_mapMod
    {X W : Scheme.{u}} (f : W ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) :
    Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) W)
      ((upperStar (Profinite.continuousCoefficientRingObj E) f).obj P) ↔
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj P) := by
  let φ := condensedPullbackHom (X := W) (Y := X) (Profinite.continuousCoefficientRingObj E) f
  let Qraw := ((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj P
  let ec := (Mod.extendScalarsIsoComapInv φ).app Qraw
  let E' := Mod.comapEquivalenceOfIsIso (inv φ)
  have : E'.functor.Additive := Functor.additive_of_preserves_binary_products E'.functor
  let ef (n : ℕ) : E'.functor.obj (Mod.finiteFree _ n) ≅ Mod.finiteFree _ n :=
    E'.functor.mapBiproduct (fun _ : Fin n ↦ Mod.regular _) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.regularIsoOfIsIso φ)
  exact exists_iso_free_iff_of_equivalence E' _ _ ef ec
/-- Finite freeness of the section-action encoding on a pro-etale slice is detected by the raw
internal inverse image. -/
theorem continuousFieldUniverse_slice_free_iff (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (W : X.ProEt) :
    (∃ n : ℕ, Nonempty (((continuousFieldModuleEquivalenceUniverse l E X).functor.obj P).over W ≅
      SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} W.hom).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
      (((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod _).obj P) := by
  let Λ := Profinite.continuousCoefficientRingObj E
  let EW := continuousFieldModuleEquivalenceUniverse l E W.left
  let Φ := ContinuousFiltration.openSliceEquivalence W E
  let hF (n : ℕ) : (EW.trans Φ).functor.obj (Mod.finiteFree (condensedRingObj Λ W.left) n) ≅
      SheafOfModules.free (ULift.{u + 1} (Fin n)) :=
    Φ.functor.mapIso (nonempty_continuousFieldModuleEquivalenceUniverse_finiteFree_iso l E
      W.left n).some ≪≫
      (SheafOfModules.mapFreeIso Φ.functor _ (openSliceUnitIso W E)).symm
  exact (exists_iso_free_iff_of_equivalence (EW.trans Φ) _ _ hF
    (nonempty_over_continuousFieldModuleEquivalenceUniverse_iso l E X P W).some).trans
    (continuousField_isFree_upperStar_iff_isFree_mapMod E W.hom P)

/-- The section-action encoding preserves and reflects local finite freeness. -/
theorem isLocallyFree_iff_continuousFieldModuleEquivalenceUniverse (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) :
    IsLocallyFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) P ↔
      ((continuousFieldModuleEquivalenceUniverse l E X).functor.obj P).IsFiniteLocallyFree := by
  classical
  let R := latticeModuleRing X E
  let M := (continuousFieldModuleEquivalenceUniverse l E X).functor.obj P
  constructor
  · rintro ⟨C, hC⟩
    let (s : C.I₀) : WeaklyEtale (C.f s) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
    let U (s : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f s)
    have hU : (Scheme.ProEt.topology X).CoversTop U := by
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal _
        (Scheme.ProEt.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) X)]
      let a (s : C.I₀) : U s ⟶ Scheme.ProEt.mk (𝟙 X) :=
        MorphismProperty.Over.homMk (C.f s) (by
          change C.f s ≫ 𝟙 X = C.f s
          exact Category.comp_id _)
      apply Scheme.ProEt.mem_topology_iff.mpr
      refine ⟨Presieve.ofArrows U a, ?_, ?_⟩
      · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
        exact C.mem₀
      · intro W f hf
        obtain ⟨s⟩ := hf
        exact ⟨s, ⟨𝟙 _⟩⟩
    have hfree (s : C.I₀) : ∃ n : ℕ, Nonempty (M.over (U s) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) :=
      (continuousFieldUniverse_slice_free_iff l E X P (U s)).mpr (hC s)
    choose n hn using hfree
    have hU' : (Scheme.ProEt.topology X).CoversTop
        (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) := by
      intro V
      apply (Scheme.ProEt.topology X).superset_covering _ (hU V)
      rintro W f ⟨s, ⟨a⟩⟩
      exact ⟨ULift.up s, ⟨a⟩⟩
    exact SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free (M := M)
      (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) hU'
      (fun s ↦ ULift.{u + 1} (Fin (n s.down))) (fun s ↦ hn s.down)
  · intro hM
    let : M.IsFiniteLocallyFree := hM
    obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
    let : q.IsLocallyFreeData := hq
    have hfree (i : q.I) : ∃ n : ℕ, Nonempty (M.over (q.X i) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let : (q.generators i).IsFiniteType := hf.isFiniteType i
      obtain ⟨n, ⟨en⟩⟩ := Finite.exists_equiv_fin (q.generators i).I
      exact ⟨n, ⟨(asIso (q.generators i).π).symm ≪≫
        SheafOfModules.freeFunctor.mapIso (en.trans Equiv.ulift.symm).toIso⟩⟩
    let V : X.ProEt := Scheme.ProEt.mk (𝟙 X)
    obtain ⟨S, hS, hle⟩ := Scheme.ProEt.mem_topology_iff.mp (q.coversTop V)
    obtain ⟨C, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hS
    have hw (i : C.I₀) : (C.f i).left = (C.X i).hom := by
      have h := MorphismProperty.Over.w (C.f i)
      change (C.f i).left ≫ 𝟙 X = (C.X i).hom at h
      exact (Category.comp_id _).symm.trans h
    let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
      { I₀ := C.I₀
        X := fun i ↦ (C.X i).left
        f := fun i ↦ (C.X i).hom
        mem₀ := by
          have hm := Scheme.ProEt.mem_precoverage_iff.mp C.mem₀
          rw [Presieve.map_ofArrows] at hm
          change (Presieve.ofArrows (fun i ↦ (C.X i).left)
            (fun i ↦ (C.f i).left)) ∈ Scheme.proetalePrecoverage X at hm
          simpa only [hw] using hm }
    let : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage (@WeaklyEtale)))
    let D' := D.restrictIndexOfSmall.{u}
    refine ⟨D', fun s ↦ ?_⟩
    let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} D s
    obtain ⟨i, ⟨a⟩⟩ := hle _ _ (.mk j)
    obtain ⟨n, ⟨en⟩⟩ := hfree i
    have en' : Nonempty (M.over (C.X j) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let F := SheafOfModules.overMap R a
      let e : F.obj (SheafOfModules.unit (R.over (q.X i))) ≅
          SheafOfModules.unit (R.over (C.X j)) := SheafOfModules.overMapUnitIso a
      exact ⟨((SheafOfModules.overFunctorMap R a).app M).symm ≪≫ F.mapIso en ≪≫
        (SheafOfModules.mapFreeIso F _ e.symm).symm⟩
    exact (continuousFieldUniverse_slice_free_iff l E X P (C.X j)).mp ⟨n, en'⟩

/-- The encoding of the condensed inverse image of the decoded module `F` is finite locally free
whenever the continuous inverse image of `F` is. -/
theorem isFiniteLocallyFree_encoding_upperStar_of_pull {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (hF : ((ContinuousFiltration.pull l E i).obj F).IsFiniteLocallyFree) :
    ((continuousFieldModuleEquivalenceUniverse l E Z).functor.obj
      ((upperStar (Profinite.continuousCoefficientRingObj E) i).obj
        ((continuousFieldModuleEquivalenceUniverse l E X).inverse.obj F))).IsFiniteLocallyFree := by
  obtain ⟨e⟩ := nonempty_upperStar_comp_continuousFieldModuleEquivalenceUniverse_iso l E i
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (h := hF)
    ((ContinuousFiltration.pull l E i).mapIso
      ((continuousFieldModuleEquivalenceUniverse l E X).counitIso.app F).symm ≪≫
        (e.app ((continuousFieldModuleEquivalenceUniverse l E X).inverse.obj F)).symm)

/-- A module object whose encoding is finite locally free has finite constant local models. -/
theorem hasFiniteConstantLocalModel_of_isFiniteLocallyFree {Z : Scheme.{u}}
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) Z))
    (hN : ((continuousFieldModuleEquivalenceUniverse l E Z).functor.obj N).IsFiniteLocallyFree) :
    HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj E) Z N :=
  IsLocallyFree.hasFiniteConstantLocalModel _
    ((isLocallyFree_iff_continuousFieldModuleEquivalenceUniverse l E Z N).mpr hN)

/-- Finite local freeness of encodings is preserved by condensed inverse image. -/
theorem isFiniteLocallyFree_encoding_upperStar {Z W : Scheme.{u}} (g : W ⟶ Z)
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) Z))
    (hN : ((continuousFieldModuleEquivalenceUniverse l E Z).functor.obj N).IsFiniteLocallyFree) :
    ((continuousFieldModuleEquivalenceUniverse l E W).functor.obj
      ((upperStar (Profinite.continuousCoefficientRingObj E) g).obj N)).IsFiniteLocallyFree :=
  (isLocallyFree_iff_continuousFieldModuleEquivalenceUniverse l E W _).mp
    (IsLocallyFree.upperStar _ g
      ((isLocallyFree_iff_continuousFieldModuleEquivalenceUniverse l E Z N).mpr hN))

/-- A decoded continuous module whose continuous inverse images to the strata of a
stratification are finite locally free is finitely constant stratified. -/
theorem isFiniteConstantStratified_continuousFieldModuleEquivalenceUniverse_inverse
    (X : Scheme.{u}) (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (S : Scheme.Stratification X)
    (hS : ∀ a : Fin S.n,
      ((ContinuousFiltration.pull l E (S.immersion a)).obj F).IsFiniteLocallyFree) :
    IsFiniteConstantStratified (Profinite.continuousCoefficientRingObj E) X
      ((continuousFieldModuleEquivalenceUniverse l E X).inverse.obj F) :=
  ⟨S, fun a ↦ hasFiniteConstantLocalModel_of_isFiniteLocallyFree l E _
    (isFiniteLocallyFree_encoding_upperStar_of_pull l E (S.immersion a) F (hS a))⟩

/-- A continuous module which is finite locally free on the strata of a finite locally closed
stratification has a constructible condensed encoding. -/
theorem isConstantModelConstructible_continuousFieldModuleEquivalenceUniverse_inverse
    (X : Scheme.{u}) [IsNoetherian X]
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (s : X.FiniteLocallyClosedStratification)
    (hs : ∀ a : Fin s.n,
      ((ContinuousFiltration.pull l E (s.immersion a)).obj F).IsFiniteLocallyFree) :
    IsConstantModelConstructible (Profinite.continuousCoefficientRingObj E) X
      ((continuousFieldModuleEquivalenceUniverse l E X).inverse.obj F) := by
  rw [IsConstantModelConstructible,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨inferInstance, inferInstance⟩)]
  exact isFiniteConstantStratified_continuousFieldModuleEquivalenceUniverse_inverse l E X F
    (Scheme.Stratification.ofNoetherianSpace s.n s.stratum s.isLocallyClosed_stratum
      s.iUnion_stratum_eq_univ s.pairwise_disjoint_stratum s.domain s.immersion s.isImmersion
      s.range_immersion) hs

/-- Finite local freeness of encodings is invariant under replacing the composite of condensed
inverse images by another factorization of the same morphism. -/
theorem isFiniteLocallyFree_encoding_upperStar_upperStar {A B C X : Scheme.{u}}
    (f₁ : A ⟶ B) (f₂ : B ⟶ X) (g₁ : A ⟶ C) (g₂ : C ⟶ X) (h : f₁ ≫ f₂ = g₁ ≫ g₂)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hM : ((continuousFieldModuleEquivalenceUniverse l E A).functor.obj
      ((upperStar (Profinite.continuousCoefficientRingObj E) g₁).obj
        ((upperStar (Profinite.continuousCoefficientRingObj E) g₂).obj M))).IsFiniteLocallyFree) :
    ((continuousFieldModuleEquivalenceUniverse l E A).functor.obj
      ((upperStar (Profinite.continuousCoefficientRingObj E) f₁).obj
        ((upperStar (Profinite.continuousCoefficientRingObj E) f₂).obj M))).IsFiniteLocallyFree :=
  SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (h := hM)
    ((continuousFieldModuleEquivalenceUniverse l E A).functor.mapIso
      ((upperStarComp _ g₁ g₂).symm.app M ≪≫ (upperStarCongr _ h.symm).app M ≪≫
        (upperStarComp _ f₁ f₂).app M))

/-- The encoding of a composite condensed inverse image of a decoded module is the composite
continuous inverse image. -/
theorem isFiniteLocallyFree_pull_pull_of_encoding {A B X : Scheme.{u}}
    (f₁ : A ⟶ B) (f₂ : B ⟶ X) (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (hM : ((continuousFieldModuleEquivalenceUniverse l E A).functor.obj
      ((upperStar (Profinite.continuousCoefficientRingObj E) f₁).obj
        ((upperStar (Profinite.continuousCoefficientRingObj E) f₂).obj
          ((continuousFieldModuleEquivalenceUniverse l E X).inverse.obj F)))).IsFiniteLocallyFree) :
    ((ContinuousFiltration.pull l E f₁).obj
      ((ContinuousFiltration.pull l E f₂).obj F)).IsFiniteLocallyFree := by
  obtain ⟨ef₁⟩ := nonempty_upperStar_comp_continuousFieldModuleEquivalenceUniverse_iso l E f₁
  obtain ⟨ef₂⟩ := nonempty_upperStar_comp_continuousFieldModuleEquivalenceUniverse_iso l E f₂
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (h := hM)
    (ef₁.app _ ≪≫ (ContinuousFiltration.pull l E f₁).mapIso (ef₂.app _ ≪≫
      (ContinuousFiltration.pull l E f₂).mapIso
        ((continuousFieldModuleEquivalenceUniverse l E X).counitIso.app F)))

/-- Finite local freeness of continuous inverse images is transported along a commutative
square: if `g₂^*F` is finite locally free, so is `f₁^*f₂^*F` whenever `f₁ ≫ f₂ = g₁ ≫ g₂`. -/
theorem isFiniteLocallyFree_pull_pull {A B C X : Scheme.{u}}
    (f₁ : A ⟶ B) (f₂ : B ⟶ X) (g₁ : A ⟶ C) (g₂ : C ⟶ X) (h : f₁ ≫ f₂ = g₁ ≫ g₂)
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (hF : ((ContinuousFiltration.pull l E g₂).obj F).IsFiniteLocallyFree) :
    ((ContinuousFiltration.pull l E f₁).obj
      ((ContinuousFiltration.pull l E f₂).obj F)).IsFiniteLocallyFree :=
  isFiniteLocallyFree_pull_pull_of_encoding l E f₁ f₂ F
    (isFiniteLocallyFree_encoding_upperStar_upperStar l E f₁ f₂ g₁ g₂ h _
      (isFiniteLocallyFree_encoding_upperStar l E g₁ _
        (isFiniteLocallyFree_encoding_upperStar_of_pull l E g₂ F hF)))

end CondensedRing

/-- A continuous module which is finite locally free on the strata of a finite locally closed
stratification admits a finite open filtration whose successive strata are reduced closed
subschemes on which it is finite locally free, with the extension-by-zero pieces forming a
chain of subobjects whose quotients are the stratum pieces. -/
theorem exists_continuousFiltration_of_stratification
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (s : X.FiniteLocallyClosedStratification)
    (hs : ∀ a : Fin s.n,
      ((ContinuousFiltration.pull l E (s.immersion a)).obj F).IsFiniteLocallyFree) :
    ∃ (m : ℕ) (V : Fin (m + 1) → X.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last m) = ⊤ ∧
      ∃ (S : Fin m → Scheme.{u}) (t : ∀ k : Fin m, S k ⟶ (V k.succ).toScheme),
        (∀ k : Fin m, IsClosedImmersion (t k) ∧ IsReduced (S k) ∧
          Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        (∀ k : Fin (m + 1), IsNoetherian (V k).toScheme ∧
          topologicalKrullDim (V k).toScheme ≤ topologicalKrullDim X ∧
          (∀ x : (V k).toScheme, IsUnit (l : (V k).toScheme.presheaf.stalk x)) ∧
          QuasiCompact (V k).ι ∧ QuasiSeparated (V k).ι) ∧
        (∀ k : Fin m, IsNoetherian (S k) ∧
          topologicalKrullDim (S k) ≤ topologicalKrullDim X ∧
          (∀ x : S k, IsUnit (l : (S k).presheaf.stalk x)) ∧
          QuasiCompact ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          QuasiSeparated ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          ((ContinuousFiltration.pull l E (t k)).obj
            ((ContinuousFiltration.pull l E (V k.succ).ι).obj F)).IsFiniteLocallyFree) ∧
        (∀ k : Fin (m + 1), Mono (ContinuousFiltration.counit E (V k) F)) ∧
        IsZero ((ContinuousFiltration.piece E (V 0)).obj F) ∧
        IsIso (ContinuousFiltration.counit E (V (Fin.last m)) F) ∧
        ∃ d : ∀ k : Fin m,
          (ContinuousFiltration.piece E (V k.castSucc)).obj F ⟶
            (ContinuousFiltration.piece E (V k.succ)).obj F,
          (∀ k : Fin m, d k ≫ ContinuousFiltration.counit E (V k.succ) F =
            ContinuousFiltration.counit E (V k.castSucc) F) ∧
          (∀ k : Fin m, Mono (d k)) ∧
          (∀ k : Fin m, Nonempty
            (cokernel (d k) ≅ ContinuousFiltration.stratumPiece l E (V k.succ) (t k) F)) := by
  classical
  obtain ⟨m, V, hV, hV0, hVl, hstep⟩ : ∃ (m : ℕ) (V : Fin (m + 1) → X.Opens), Monotone V ∧
      V 0 = ⊥ ∧ V (Fin.last m) = ⊤ ∧ ∀ k : Fin m, ∃ a : Fin s.n,
        ∀ x ∈ V k.succ, x ∉ V k.castSucc → x ∈ s.stratum a :=
    s.toFiniteLocallyClosedStratification.exists_opens_chain_of_le ⊥
  let Z (k : Fin m) : TopologicalSpace.Closeds (V k.succ).toScheme :=
    ⟨{x | (V k.succ).ι x ∉ V k.castSucc},
      ((V k.castSucc).isOpen.preimage (V k.succ).ι.continuous).isClosed_compl⟩
  let S (k : Fin m) := (Scheme.IdealSheafData.vanishingIdeal (Z k)).subscheme
  let t (k : Fin m) : S k ⟶ (V k.succ).toScheme :=
    (Scheme.IdealSheafData.vanishingIdeal (Z k)).subschemeι
  have ht (k : Fin m) : IsClosedImmersion (t k) ∧ IsReduced (S k) ∧
      Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc} := by
    obtain ⟨-, -, hci, hred, -, hrange, -⟩ :=
      Scheme.IdealSheafData.reduced_induced_closed_subscheme _ (Z k)
    exact ⟨hci, hred, hrange⟩
  have hVn (k : Fin (m + 1)) : IsNoetherian (V k).toScheme :=
    isNoetherian_of_isImmersion (V k).ι
  have hVqc (k : Fin (m + 1)) : QuasiCompact (V k).ι := quasiCompact_of_noetherianSpace _
  have hSn (k : Fin m) : IsNoetherian (S k) := by
    have := (ht k).1
    have := hVn k.succ
    exact isNoetherian_of_isImmersion (t k)
  refine ⟨m, V, hV, hV0, hVl, S, t, ht, fun k ↦ ⟨hVn k,
    (V k).ι.isEmbedding.isInducing.topologicalKrullDim_le,
    isUnit_natCast_stalk (V k).ι l hl, hVqc k, inferInstance⟩, fun k ↦ ?_, ?_⟩
  · have := (ht k).1
    have := (ht k).2.1
    have := hVn k.succ
    have := hSn k
    have := isNoetherian_of_isImmersion ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι
    refine ⟨hSn k, (t k ≫ (V k.succ).ι).isEmbedding.isInducing.topologicalKrullDim_le,
      isUnit_natCast_stalk (t k ≫ (V k.succ).ι) l hl,
      quasiCompact_of_noetherianSpace _, inferInstance, ?_⟩
    obtain ⟨a, ha⟩ := hstep k
    have := s.isImmersion a
    obtain ⟨g, hg⟩ := exists_factor_immersion_of_isReduced (t k ≫ (V k.succ).ι)
      (s.immersion a) (by
        rintro _ ⟨y, rfl⟩
        rw [s.range_immersion, Scheme.Hom.comp_apply]
        have hy : t k y ∈ Set.range (t k) := ⟨y, rfl⟩
        rw [(ht k).2.2] at hy
        exact ha _ (t k y).2 hy)
    exact CondensedRing.isFiniteLocallyFree_pull_pull l E (t k) (V k.succ).ι g
      (s.immersion a) hg.symm F (hs a)
  · have hfac (k : Fin m) := ContinuousFiltration.exists_counit_factor_cokernel l E
      (V k.castSucc) (V k.succ) (hV k.castSucc_le_succ) (t k) (ht k).2.2 F
    choose d hd hq using hfac
    have hmono (k : Fin (m + 1)) : Mono (ContinuousFiltration.counit E (V k) F) :=
      ContinuousFiltration.counit_mono E (V k) F
    refine ⟨hmono, hV0 ▸ ContinuousFiltration.isZero_piece_bot E F,
      hVl ▸ ContinuousFiltration.isIso_counit_top E F, d, hd, fun k ↦ ?_, hq⟩
    have : Mono (d k ≫ ContinuousFiltration.counit E (V k.succ) F) := by
      rw [hd k]
      exact hmono _
    exact mono_of_mono _ (ContinuousFiltration.counit E (V k.succ) F)

/-- A rational constructible continuous module has an admissible finite open filtration.
The canonical section-action equivalence retains the underlying abelian sheaves, identifies
finite free scalar models, and intertwines locally closed restriction. -/
theorem exists_continuousFiltration_admissibleStrata
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (hF : ∃ s : X.FiniteLocallyClosedStratification, ∀ a : Fin s.n,
      ((ContinuousFiltration.pull l E (s.immersion a)).obj F).IsFiniteLocallyFree) :
    IsConstantModelConstructible (Profinite.continuousCoefficientRingObj E) X
      ((CondensedRing.continuousFieldModuleEquivalenceUniverse l E X).inverse.obj F) ∧
    (∀ T : Scheme.{u}, Nonempty
      ((CondensedRing.continuousFieldModuleEquivalenceUniverse l E T).functor ⋙
          SheafOfModules.toSheaf (latticeModuleRing T E) ≅
        Mod.forget (condensedRingObj (Profinite.continuousCoefficientRingObj E) T))) ∧
    (∀ (T : Scheme.{u}) (n : ℕ), Nonempty
      ((CondensedRing.continuousFieldModuleEquivalenceUniverse l E T).functor.obj
          (Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) T) n) ≅
        SheafOfModules.free (R := latticeModuleRing T E) (ULift.{u + 1} (Fin n)))) ∧
    (∀ (Y Z : Scheme.{u}) (i : Z ⟶ Y) [IsImmersion i], Nonempty
      (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E) i ⋙
          (CondensedRing.continuousFieldModuleEquivalenceUniverse l E Z).functor ≅
        (CondensedRing.continuousFieldModuleEquivalenceUniverse l E Y).functor ⋙
          ContinuousFiltration.pull l E i)) ∧
    ∃ (m : ℕ) (V : Fin (m + 1) → X.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last m) = ⊤ ∧
      ∃ (S : Fin m → Scheme.{u}) (t : ∀ k : Fin m, S k ⟶ (V k.succ).toScheme),
        (∀ k : Fin m, IsClosedImmersion (t k) ∧ IsReduced (S k) ∧
          Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        (∀ k : Fin (m + 1), IsNoetherian (V k).toScheme ∧
          topologicalKrullDim (V k).toScheme ≤ topologicalKrullDim X ∧
          (∀ x : (V k).toScheme, IsUnit (l : (V k).toScheme.presheaf.stalk x)) ∧
          QuasiCompact (V k).ι ∧ QuasiSeparated (V k).ι) ∧
        (∀ k : Fin m, IsNoetherian (S k) ∧
          topologicalKrullDim (S k) ≤ topologicalKrullDim X ∧
          (∀ x : S k, IsUnit (l : (S k).presheaf.stalk x)) ∧
          QuasiCompact ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          QuasiSeparated ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          ((ContinuousFiltration.pull l E (t k)).obj
            ((ContinuousFiltration.pull l E (V k.succ).ι).obj F)).IsFiniteLocallyFree) ∧
        (∀ k : Fin (m + 1), Mono (ContinuousFiltration.counit E (V k) F)) ∧
        IsZero ((ContinuousFiltration.piece E (V 0)).obj F) ∧
        IsIso (ContinuousFiltration.counit E (V (Fin.last m)) F) ∧
        ∃ d : ∀ k : Fin m,
          (ContinuousFiltration.piece E (V k.castSucc)).obj F ⟶
            (ContinuousFiltration.piece E (V k.succ)).obj F,
          (∀ k : Fin m, d k ≫ ContinuousFiltration.counit E (V k.succ) F =
            ContinuousFiltration.counit E (V k.castSucc) F) ∧
          (∀ k : Fin m, Mono (d k)) ∧
          (∀ k : Fin m, Nonempty
            (cokernel (d k) ≅ ContinuousFiltration.stratumPiece l E (V k.succ) (t k) F)) := by
  obtain ⟨s, hs⟩ := hF
  exact ⟨CondensedRing.isConstantModelConstructible_continuousFieldModuleEquivalenceUniverse_inverse
      l E X F s hs,
    fun T ↦ ⟨CondensedRing.continuousFieldModuleEquivalenceUniverseToSheafIso l E T⟩,
    CondensedRing.nonempty_continuousFieldModuleEquivalenceUniverse_finiteFree_iso l E,
    fun _ _ i _ ↦ CondensedRing.nonempty_upperStar_comp_continuousFieldModuleEquivalenceUniverse_iso
      l E i,
    exists_continuousFiltration_of_stratification l E X _hl F s hs⟩

end AlgebraicGeometry.ProEtale
