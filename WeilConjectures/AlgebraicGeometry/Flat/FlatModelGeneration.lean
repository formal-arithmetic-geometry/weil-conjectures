/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.Topology.Stratification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.ExtensionByZero
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import all WeilConjectures.AlgebraicGeometry.Open.OpenClosedFlatness
import WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedExtensionComparison
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.Algebra.Module.Projective
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.ConstructibleSheaf.Monoidal
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import all WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Point.Over
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Ordered strata, sheaf filtrations, and thick generation over finite rings

The six statements give the three clauses separately on the etale and pro-etale sites.
`Dctf` is expanded using constructible cohomology, finite cohomological bounds, and the
recorded Tor-amplitude predicates. In particular no etale-origin condition is imposed.
The auxiliary definitions spell out its parts: ordered tails, finite projective
lisse restrictions, the canonical locally closed extension, and a finite sheaf filtration.
All their data are explicit. The pro-etale site retains object universe u+1 and Hom universe u.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Closed tails and relative openness for an ordered finite stratification. -/
def FlatModelOrderedStratification {X : Scheme.{u}} (str : Stratification X) :
    Prop :=
  ∀ k : Fin str.n,
    IsClosed (⋃ k' : Fin str.n, if k ≤ k' then str.stratum k' else ∅) ∧
    IsOpen {x : (⋃ k' : Fin str.n, if k ≤ k' then str.stratum k' else ∅) |
      (x : X) ∈ str.stratum k}

/-- A finite extension filtration has zero first term, final term isomorphic to F,
and exactly one specified quotient per stratum, in the prescribed order. -/
def FlatModelExtensionFiltration {C : Type v} [Category.{w} C] [Abelian C]
    {m : ℕ} (G : Fin m → C) (F : C) : Prop :=
  ∃ M : Fin (m + 1) → C,
    IsZero (M 0) ∧ Nonempty (M (Fin.last m) ≅ F) ∧
    ∀ k : Fin m,
      ∃ (f : M k.castSucc ⟶ M k.succ) (g : M k.succ ⟶ G k)
        (h : f ≫ g = 0), (ShortComplex.mk f g h).ShortExact

/-- Local constancy and finite projective geometric stalks on the small etale site. -/
def FlatModelEtaleLisseProjective {S : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) : Prop :=
  IsLocallyConstantSheaf L ∧
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S),
      Finite ((((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj L) : Type (u + 1)) ∧
      Module.Projective A (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj L)

/-- The ordinary locally closed extension a_! = g_* j_!, with j = a.toImage and
closed g = a.imageι. Its quasi-compactness follows from the embedding into Noetherian X. -/
def flatModelEtaleExtension {S X : Scheme.{u}} [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] (a : S ⟶ X) (ha : IsImmersion a) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  exact Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) a.toImage ⋙
    Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι

private theorem flatModel_exists_ordered_refinement
    (X : Scheme.{u}) [IsNoetherian X] (S : Stratification X) :
    ∃ T : Stratification X, FlatModelOrderedStratification T ∧ T.Refines S := by
  classical
  obtain ⟨m, V, hV0, hVm, hstep⟩ := S.toStratification.exists_chain_opens (⊥ : X.Opens)
  have hmono : Monotone V := Fin.monotone_iff_le_succ.mpr fun r ↦ (hstep r).1
  let D : Fin m → Set X := fun r ↦ (V r.succ : Set X) \ V r.castSucc
  have hfind (x : X) (j : Fin (m + 1)) (hx : x ∈ V j) (h0 : x ∉ V 0) :
      ∃ r : Fin m, x ∈ D r ∧ r.succ ≤ j := by
    induction j using Fin.induction with
    | zero => exact (h0 hx).elim
    | succ j ih =>
      by_cases hj : x ∈ V j.castSucc
      · obtain ⟨r, hr, hjr⟩ := ih hj
        exact ⟨r, hr, hjr.trans (by
          simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
          omega)⟩
      · exact ⟨j, ⟨hx, hj⟩, le_rfl⟩
  have hcover : ⋃ r, D r = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨r, hr, -⟩ := hfind x (Fin.last m) (by simp [hVm]) (by simp [hV0])
    exact Set.mem_iUnion.mpr ⟨r, hr⟩
  have hdisjoint : Pairwise (Function.onFun Disjoint D) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    rintro x ⟨hxr, hnr⟩ ⟨hxs, hns⟩
    rcases lt_or_gt_of_ne hrs with h | h
    · exact hns (hmono (show r.succ ≤ s.castSucc by
          simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at *
          omega) hxr)
    · exact hnr (hmono (show s.succ ≤ r.castSucc by
          simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at *
          omega) hxs)
  have htail (k : Fin m) :
      (⋃ r : Fin m, if k ≤ r then D r else ∅) = (V k.castSucc : Set X)ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
      by_cases hkr : k ≤ r
      · rw [ite_eq_left hkr] at hr
        exact fun hk ↦ hr.2 (hmono (show k.castSucc ≤ r.castSucc by
          simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
          omega) hk)
      · simp [hkr] at hr
    · intro hx
      have hx0 : x ∉ V 0 := by simp [hV0]
      obtain ⟨r, hr, -⟩ := hfind x (Fin.last m) (by simp [hVm]) hx0
      have hkr : k ≤ r := by
        by_contra h
        exact hx (hmono (show r.succ ≤ k.castSucc by
          simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
          omega) hr.1)
      exact Set.mem_iUnion.mpr ⟨r, by simpa only [ite_eq_left hkr] using hr⟩
  have hclosed (k : Fin m) :
      IsClosed (⋃ r : Fin m, if k ≤ r then D r else ∅) := by
    rw [htail]
    exact (V k.castSucc).isOpen.isClosed_compl
  have hopen (k : Fin m) :
      IsOpen {x : (⋃ r : Fin m, if k ≤ r then D r else ∅) | (x : X) ∈ D k} := by
    have heq : {x : (⋃ r : Fin m, if k ≤ r then D r else ∅) | (x : X) ∈ D k} =
        Subtype.val ⁻¹' (V k.succ : Set X) := by
      ext x
      have hx : (x : X) ∉ V k.castSucc := by
        exact (Set.ext_iff.mp (htail k) x.val).mp x.property
      exact and_iff_left hx
    rw [heq]
    exact (V k.succ).isOpen.preimage continuous_subtype_val
  choose Z i hi hrange using fun k : Fin m ↦
    exists_isClosedImmersion_range_eq_compl (X.homOfLE (hstep k).1)
  let T : Stratification X := Stratification.ofNoetherianSpace m D
    (fun k ↦ (V k.succ).isOpen.isLocallyClosed.inter
      (V k.castSucc).isOpen.isClosed_compl.isLocallyClosed)
    hcover hdisjoint Z (fun k ↦ i k ≫ (Scheme.Opens.ι (V k.succ)))
    (fun k ↦ by have := hi k; infer_instance) (fun k ↦ by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        refine ⟨by simp, ?_⟩
        intro hx
        have hz : (i k) z ∈ Set.range (i k).base := ⟨z, rfl⟩
        rw [hrange] at hz
        exact hz ⟨⟨_, hx⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩
      · rintro ⟨hx, hnx⟩
        have hx' : (⟨x, hx⟩ : (V k.succ)) ∈ Set.range (i k).base := by
          rw [hrange]
          rintro ⟨y, hy⟩
          have heq := congrArg Subtype.val hy
          simp only [Scheme.homOfLE_apply] at heq
          exact hnx (heq ▸ y.property)
        obtain ⟨z, hz⟩ := hx'
        exact ⟨z, congrArg Subtype.val hz⟩)
  exact ⟨T, fun k ↦ ⟨hclosed k, hopen k⟩, fun k ↦ (hstep k).2⟩

private theorem flatModel_etale_lisse_flat
    {S : Scheme.{u}} (A : Type (u + 1)) [CommRing A] [Finite A]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : FlatModelEtaleLisseProjective A L) :
    IsFiniteLocallyConstantSheaf L ∧ ObjectProperty.flat L := by
  have hfin : IsFiniteSheaf L := ⟨fun Ω _ _ x ↦ by
    have := (hL.2 Ω x).1
    exact (ModuleCat.isFinitelyGenerated_iff _).mpr (Module.Finite.of_finite)⟩
  have : IsLocallyConstantSheaf L := hL.1
  have : IsFiniteSheaf L := hfin
  refine ⟨{}, (Etale.flat_iff_forall_flat_sheafFiber_obj L).mpr ?_⟩
  intro Ω _ _ x
  have := (hL.2 Ω x).2
  have hf := (ModuleCat.flat_iff_flat
    (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj L)).mpr
    (Module.Flat.of_projective (R := A))
  exact ObjectProperty.prop_of_iso _
    (((pointSmallEtale x).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} A)).app L).symm hf

private theorem flatModel_etale_extension_properties
    {S X : Scheme.{u}} [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [Finite A] (a : S ⟶ X) (ha : IsImmersion a)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : FlatModelEtaleLisseProjective A L) :
    ObjectProperty.flat ((flatModelEtaleExtension A a ha).obj L) ∧
      IsConstructibleEtaleModuleSheaf ((flatModelEtaleExtension A a ha).obj L) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  obtain ⟨hc, hf⟩ := flatModel_etale_lisse_flat A L hL
  have : IsConstructibleSheaf L := hc.isConstructibleSheaf
  let E := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) a.toImage).obj L
  have hE : ObjectProperty.flat E :=
    (openClosedFlatness_etale A a.toImage a.toImage.closedComplement
      a.toImage.range_closedComplement E).2.1 L hf
  have : IsConstructibleSheaf E :=
    IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact a.toImage L
  have hG : ObjectProperty.flat ((Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι).obj E) :=
    (openClosedFlatness_etale A (openComplementOfIsClosedImmersion a.imageι).ι a.imageι
      (by simp [openComplementOfIsClosedImmersion])
      ((Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι).obj E)).2.2 E hE
  refine ⟨hG, (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr ?_⟩
  exact IsConstructibleSheaf.lowerStar_of_isClosedImmersion_of_quasiCompact a.imageι E

private theorem flatModel_etale_ctf_iff
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (K : Etale.DerivedCategoryModule A X) :
    ((∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K)) ↔
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, ⟨a, b, -, hz⟩, ⟨c, d, -, ht⟩⟩
    exact ⟨⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
        (fun q hq ↦ hz q (.inl hq))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
        (fun q hq ↦ hz q (.inr hq))⟩⟩,
      fun q ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc q)⟩,
      c, d, Etale.torAmplitudeIn_of_hasTorAmplitudeIn A ht⟩
  · rintro ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, c, d, ht⟩
    refine ⟨fun q ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc q),
      ⟨min a b, max a b, min_le_max, fun q hq ↦ ?_⟩,
      ⟨min c d, max c d, min_le_max,
        Etale.hasTorAmplitudeIn_of_torAmplitudeIn
          (Etale.DerivedCategory.torAmplitudeIn.mono (min_le_left c d) (le_max_right c d) ht)⟩⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha q (hq.trans_le (min_le_left a b))
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb q ((le_max_right a b).trans_lt hq)

private theorem flatModel_etale_ordered_filtration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (str : Stratification X) (ho : FlatModelOrderedStratification str) :
    FlatModelExtensionFiltration
      (fun k : Fin str.n ↦
        (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) F := by
  classical
  let T (r : Fin (str.n + 1)) : Set X :=
    ⋃ k : Fin str.n, if r.val ≤ k.val then str.stratum k else ∅
  have hT (r : Fin (str.n + 1)) : IsClosed (T r) := by
    by_cases hr : r.val < str.n
    · exact (ho ⟨r.val, hr⟩).1
    · have he : T r = ∅ := by
        ext x
        simp only [T, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
        intro k
        simp only [ite_eq_right (by omega : ¬r.val ≤ k.val), Set.mem_empty_iff_false,
          not_false_eq_true]
      rw [he]
      exact isClosed_empty
  let U (r : Fin (str.n + 1)) : X.Opens := ⟨(T r)ᶜ, (hT r).isOpen_compl⟩
  have hU0 : U 0 = ⊥ := by
    apply TopologicalSpace.Opens.ext
    change (⋃ k : Fin str.n, if (0 : ℕ) ≤ k.val then str.stratum k else ∅)ᶜ = ∅
    simp only [Nat.zero_le, ite_true, str.iUnion_stratum_eq_univ, Set.compl_univ]
  have hUn : U (Fin.last str.n) = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext x
    simp [U, T, show ∀ k : Fin str.n, ¬str.n ≤ k.val from fun k ↦ by omega]
  have hmono : Monotone U := by
    intro r s hrs x hx hs
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hs
    by_cases hsk : s.val ≤ k.val
    · rw [ite_eq_left hsk] at hk
      exact hx (Set.mem_iUnion.mpr ⟨k, by
        rw [ite_eq_left (show r.val ≤ k.val from (Fin.le_def.mp hrs).trans hsk)]
        exact hk⟩)
    · simp [hsk] at hk
  have hdiff (k : Fin str.n) :
      (U k.succ : Set X) \ U k.castSucc = str.stratum k := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      have ht : x ∈ T k.castSucc := by
        change ¬x ∈ (T k.castSucc)ᶜ at hn
        exact not_not.mp hn
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
      change x ∈ if k.val ≤ j.val then str.stratum j else ∅ at hj
      by_cases hkj : k.val ≤ j.val
      · rw [ite_eq_left hkj] at hj
        have hjk : j = k := by
          apply Fin.ext
          by_contra h
          exact hx (Set.mem_iUnion.mpr ⟨j, by
            rw [ite_eq_left (show k.succ.val ≤ j.val by simp only [Fin.val_succ]; omega)]
            exact hj⟩)
        simpa [hjk] using hj
      · simp [hkj] at hj
    · intro hx
      refine ⟨?_, ?_⟩
      · intro ht
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
        change x ∈ if k.val + 1 ≤ j.val then str.stratum j else ∅ at hj
        by_cases hkj : k.val + 1 ≤ j.val
        · rw [ite_eq_left hkj] at hj
          exact (Set.disjoint_left.mp (str.pairwise_disjoint_stratum (by
            intro h; subst j; omega))) hx hj
        · simp [hkj] at hj
      · intro hn
        exact hn (Set.mem_iUnion.mpr ⟨k, by simp [hx]⟩)
  let M (r : Fin (str.n + 1)) :=
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (U r).ι).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) (U r).ι).obj F)
  refine ⟨M, ?_, ?_, ?_⟩
  · change IsZero ((Etale.openImmersionLowerShriek _ (U 0).ι).obj _)
    rw [hU0]
    have : IsEmpty (⊥ : X.Opens).toScheme :=
      ⟨fun x ↦ TopologicalSpace.Opens.mem_bot.mp x.2⟩
    exact Functor.map_isZero _ (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  · change Nonempty ((Etale.openImmersionLowerShriek _ (U (Fin.last str.n)).ι).obj _ ≅ F)
    rw [hUn]
    obtain ⟨Z, i, _, hi⟩ := exists_isClosedImmersion_range_eq_compl (⊤ : X.Opens).ι
    have hs := Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
      (⊤ : X.Opens).ι i F hi
    have : IsEmpty Z := ⟨fun z ↦ by
      have hz : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
      simp [hi, Scheme.Opens.range_ι] at hz⟩
    have hg : (Etale.openClosedShortComplex (ModuleCat.{u + 1} A) (⊤ : X.Opens).ι i
        (disjoint_range_of_range_eq_compl _ _ hi) F).g = 0 :=
      (Functor.map_isZero (Etale.lowerStar (ModuleCat.{u + 1} A) i)
        (Scheme.Etale.isZero_sheaf_of_isEmpty _)).eq_of_tgt _ _
    have : Epi ((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (⊤ : X.Opens).ι).counit.app F) := hs.exact.epi_f hg
    have : IsIso ((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (⊤ : X.Opens).ι).counit.app F) := isIso_of_mono_of_epi _
    exact ⟨asIso ((Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) (⊤ : X.Opens).ι).counit.app F)⟩
  · intro k
    let a := str.immersion k
    have : IsImmersion a := str.isImmersion k
    let W := U k.succ
    let V := U k.castSucc
    have hVW : V ≤ W := hmono (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
    have haW : Set.range a ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι, str.range_immersion]
      exact fun x hx ↦ ((Set.ext_iff.mp (hdiff k) x).mpr hx).1
    let i := IsOpenImmersion.lift W.ι a haW
    have hia : i ≫ W.ι = a := IsOpenImmersion.lift_fac _ _ _
    have : IsPreimmersion (i ≫ W.ι) := by rw [hia]; infer_instance
    have : IsPreimmersion i := .of_comp i W.ι
    have hir : Set.range i = W.ι ⁻¹' (str.stratum k) := by
      rw [← str.range_immersion k]
      change Set.range i = W.ι ⁻¹' Set.range a
      rw [← hia]
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z, rfl⟩
      · rintro ⟨z, hz⟩
        exact ⟨z, W.ι.isEmbedding.injective hz⟩
    have hir' : Set.range i = (Set.range (X.homOfLE hVW))ᶜ := by
      rw [hir]
      ext x
      have hxW : W.ι x ∈ (W : Set X) := by simp
      rw [← hdiff k]
      simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_compl_iff]
      constructor
      · rintro ⟨_, hx⟩ ⟨z, hz⟩
        apply hx
        have he := congrArg (fun y ↦ W.ι y) hz
        change W.ι x ∈ (V : Set X)
        rw [← he]
        simp [Scheme.homOfLE_apply]
      · intro hx
        refine ⟨hxW, fun hv ↦ hx ?_⟩
        exact ⟨⟨W.ι x, hv⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩
    have : IsClosedImmersion i := .of_isPreimmersion i (by
      rw [hir']
      exact (X.homOfLE hVW).isOpenEmbedding.isOpen_range.isClosed_compl)
    let E := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) W.ι
    let H := (Etale.upperStar (ModuleCat.{u + 1} A) W.ι).obj F
    let S := (Etale.openClosedShortComplex (ModuleCat.{u + 1} A) (X.homOfLE hVW) i
      (disjoint_range_of_range_eq_compl _ _ hir') H).map E
    have hs : S.ShortExact := (Etale.shortExact_openClosedShortComplex
      (ModuleCat.{u + 1} A) (X.homOfLE hVW) i H hir').map_of_exact E
    obtain ⟨α, _⟩ := Adjunction.exists_iso_counit_app
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) V.ι)
      ((Etale.openImmersionLowerShriekUpperStarAdjunction _ (X.homOfLE hVW)).comp
        (Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι))
      (Etale.upperStarComp _ (X.homOfLE hVW) W.ι V.ι (X.homOfLE_ι hVW).symm) F
    obtain ⟨hqa, he, _⟩ := (etale_locallyClosed_extension_comparison
      (A := A) X (𝟙 X) (𝟙 X)).2 a
    obtain ⟨e, _, _⟩ := he i W.ι hia
    let L := (Etale.upperStar (ModuleCat.{u + 1} A) a).obj F
    let β : S.X₃ ≅ (flatModelEtaleExtension A a (str.isImmersion k)).obj L :=
      E.mapIso ((Etale.lowerStar (ModuleCat.{u + 1} A) i).mapIso
        ((Etale.upperStarComp (ModuleCat.{u + 1} A) i W.ι a hia.symm).app F).symm) ≪≫
        (e.app L).symm
    let f : M k.castSucc ⟶ M k.succ := α.hom ≫ S.f
    let g := S.g ≫ β.hom
    have hfg : f ≫ g = 0 := by simp [f, g, Category.assoc]
    refine ⟨f, g, hfg, ?_⟩
    exact ShortComplex.shortExact_of_iso (S₁ := S)
      (ShortComplex.isoMk (S₁ := S) α.symm (Iso.refl _) β (by simp [f]) (by simp [g])) hs

private theorem flatModel_filtration_mem
    {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory.{w} C]
    {m : ℕ} {G : Fin m → C} {F : C}
    (hF : FlatModelExtensionFiltration G F)
    (P : ObjectProperty (_root_.DerivedCategory C))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hG : ∀ k, P ((_root_.DerivedCategory.singleFunctor C 0).obj (G k))) :
    P ((_root_.DerivedCategory.singleFunctor C 0).obj F) := by
  obtain ⟨M, h0, ⟨e⟩, hM⟩ := hF
  have h (k : Fin (m + 1)) : P ((_root_.DerivedCategory.singleFunctor C 0).obj (M k)) := by
    induction k using Fin.induction with
    | zero => exact P.prop_of_isZero (Functor.map_isZero _ h0)
    | succ k ih =>
      obtain ⟨f, g, hfg, hs⟩ := hM k
      let S := ShortComplex.mk f g hfg
      let B := HomologicalComplex.single C (ComplexShape.up ℤ) 0
      have hB := hs.map_of_exact B
      have h1 : P (_root_.DerivedCategory.Q.obj (B.obj (M k.castSucc))) :=
        P.prop_of_iso ((_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app _ ) ih
      have h3 : P (_root_.DerivedCategory.Q.obj (B.obj (G k))) :=
        P.prop_of_iso ((_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app _ ) (hG k)
      exact P.prop_of_iso ((_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app _).symm
        (P.ext_of_isTriangulatedClosed₂ (_root_.DerivedCategory.triangleOfSES hB)
          (_root_.DerivedCategory.triangleOfSES_distinguished hB) h1 h3)
  exact P.prop_of_iso ((_root_.DerivedCategory.singleFunctor C 0).mapIso e) (h (Fin.last m))

/-- Clause (1) on the etale site: an ordered finite stratification with projective stalks. -/
theorem etale_flatConstructible_orderedStratification
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hc : IsConstructibleEtaleModuleSheaf F) (_hf : ObjectProperty.flat F) :
    ∃ str : Stratification X,
      FlatModelOrderedStratification str ∧
      ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
        ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F) := by
  have hc := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp _hc
  obtain ⟨S, hS⟩ := hc.exists_stratification
  obtain ⟨T, hT, hTS⟩ := flatModel_exists_ordered_refinement X S
  refine ⟨T, hT, fun k ↦ ?_⟩
  let L := (Etale.upperStar (ModuleCat.{u + 1} A) (T.immersion k)).obj F
  have hL : IsFiniteLocallyConstantSheaf L :=
    hTS.isFiniteLocallyConstantSheaf_upperStar F hS k
  have hflat : ObjectProperty.flat L := Functor.PreservesFlat.flat_obj _hf
  refine ⟨hL.toIsLocallyConstantSheaf, fun Ω _ _ x ↦ ?_⟩
  let M := ((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj L
  have hfin := hL.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω x
  have : Module.Finite A M := (ModuleCat.isFinitelyGenerated_iff M).mp hfin
  have : Finite M := Module.finite_of_finite A
  have hM : ObjectProperty.flat M := ObjectProperty.prop_of_iso _
    (((pointSmallEtale x).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} A)).app L)
    ((pointSmallEtale x).ulift.flat_sheafFiber_obj hflat)
  have : Module.Flat A M := (ModuleCat.flat_iff_flat M).mp hM
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

/-- The extension by zero `a_{k!} a_k^* F` of the restriction of `F` to the `k`-th stratum
of a stratification. -/
abbrev flatModelStratumExtension {X : Scheme.{u}} [IsNoetherian X] (A : Type (u + 1))
    [CommRing A] (str : Stratification X) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (k : Fin str.n) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)

/-- Clause (2) on the etale site: the specified finite sheaf-extension filtration
and flat constructible degree-zero factors of finite Tor amplitude. -/
theorem etale_flatConstructible_extensionFiltration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (str : Stratification X) (ho : FlatModelOrderedStratification str)
    (hp : ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
      ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) :
    FlatModelExtensionFiltration (flatModelStratumExtension A str F) F ∧
    ∀ k : Fin str.n,
      ObjectProperty.flat (flatModelStratumExtension A str F k) ∧
      IsConstructibleEtaleModuleSheaf (flatModelStratumExtension A str F k) ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (flatModelStratumExtension A str F k)))) ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (flatModelStratumExtension A str F k)))) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (flatModelStratumExtension A str F k))) := by
  refine ⟨flatModel_etale_ordered_filtration X A F str ho, fun k ↦ ?_⟩
  let G := flatModelStratumExtension A str F k
  obtain ⟨hf, hc⟩ := flatModel_etale_extension_properties A (str.immersion k)
    (str.isImmersion k) _ (hp k)
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mp hc
  have hctf : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G) :=
    ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
      0, 0, Etale.torAmplitudeIn_singleFunctor_obj_of_flat A G hf⟩
  exact ⟨hf, hc, (flatModel_etale_ctf_iff X A _).mpr hctf⟩

/-- Clause (3) on the etale site: equality with the smallest replete full
subcategory closed under shifts, cones and direct summands. -/
theorem etale_flatConstructible_thickGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A] :
    (fun K : Etale.DerivedCategoryModule A X ↦
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K)) =
    ObjectProperty.triangEnvelope
      (fun K : Etale.DerivedCategoryModule A X ↦
        ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
          (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
          FlatModelEtaleLisseProjective A L ∧
          Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
            ((flatModelEtaleExtension A a ha).obj L))) := by
  let _ : Zero (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    CategoryTheory.Limits.HasZeroObject.zero' _
  let G : ObjectProperty (Etale.DerivedCategoryModule A X) := fun K ↦
    ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
      FlatModelEtaleLisseProjective A L ∧
      Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((flatModelEtaleExtension A a ha).obj L))
  have hnonempty : G.Nonempty := by
    let L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := 0
    have hL : FlatModelEtaleLisseProjective A L := by
      refine ⟨IsLocallyConstantSheaf.of_isZero (isZero_zero _), fun Ω _ _ x ↦ ?_⟩
      have hz := Functor.map_isZero ((pointSmallEtale x).sheafFiber
        (A := ModuleCat.{u + 1} A)) (isZero_zero _)
      have := ModuleCat.subsingleton_of_isZero hz
      exact ⟨inferInstance, inferInstance⟩
    exact ⟨_, X, 𝟙 X, inferInstance, L, hL, ⟨Iso.refl _⟩⟩
  let : G.Nonempty := hnonempty
  have hsingle (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (hc : IsConstructibleEtaleModuleSheaf F) (hf : ObjectProperty.flat F) :
      G.triangEnvelope ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    obtain ⟨str, ho, hp⟩ := etale_flatConstructible_orderedStratification X A F hc hf
    have hfil := (etale_flatConstructible_extensionFiltration X A F str ho hp).1
    refine flatModel_filtration_mem hfil G.triangEnvelope (fun k ↦ ?_)
    exact G.le_triangEnvelope _
      ⟨str.domain k, str.immersion k, str.isImmersion k, _, hp k, ⟨Iso.refl _⟩⟩
  apply le_antisymm
  · intro K hK
    obtain ⟨hc, hz, a, b, hab, ht⟩ := hK
    obtain ⟨P, hf, hpc, hpz, ⟨e⟩⟩ :=
      (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel A X a b hab K
        ⟨hc, hz⟩).mp ht
    have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff P a).mpr
      (fun q hq ↦ hpz q (.inl hq))
    have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).mpr
      (fun q hq ↦ hpz q (.inr hq))
    have hP := HomotopyCategory.mem_subcategory_of_strictly_bounded
      (G.triangEnvelope.inverseImage _root_.DerivedCategory.Qh) P a b (fun n _ _ ↦ ?_)
    · exact G.triangEnvelope.prop_of_iso e
        (G.triangEnvelope.prop_of_iso
          ((_root_.DerivedCategory.quotientCompQhIso _).app P) hP)
    exact hsingle (P.X n) (hpc n) (hf n)
  · intro K hK
    apply (flatModel_etale_ctf_iff X A K).mpr
    apply (ObjectProperty.triangEnvelope_le_iff (P := G)
      (Q := Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X)).mpr ?_ K hK
    rintro K ⟨S, a, ha, L, hL, ⟨e⟩⟩
    obtain ⟨hf, hc⟩ := flatModel_etale_extension_properties A a ha L hL
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
    exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).prop_of_iso
      e.symm ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
        0, 0, Etale.torAmplitudeIn_singleFunctor_obj_of_flat A _ hf⟩

end AlgebraicGeometry
