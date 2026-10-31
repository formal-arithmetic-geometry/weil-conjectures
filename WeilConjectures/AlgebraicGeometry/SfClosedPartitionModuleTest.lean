/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientModulePullbackComposition
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.NoetherianComplementaryStratifications

/-!
# Closed-side partitions and pro-etale module restrictions

Source: Stacks Project, Tags 02V0, 01OW, 01OZ, 04ZA and 03D8;
finite-stage paragraph of prop-sf-open-closed-triangle-all-stages
(blueprint: lem-sf-closed-partition-module-test).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Restrict the supplied closed-side identification using the canonical compositor.
The compositor is fixed by its direct-image mate on fibre-product sections, as stated
in proEtaleConstantRingModulePullbackComposition; its adjunction characterization
uniquely determines it. The second arrow is the image of the supplied isomorphism
under the actual module inverse-image functor. Both arrows are module-linear and
natural in the module and its supplied identification.
Source: Stacks Project, Tag 03D8
(blueprint: lem-sf-closed-partition-module-test). -/
def sfClosedPartitionRestrictionIso
    (A : Type u) [CommRing A] {X Z T : Scheme.{u}}
    (i : Z ⟶ X) (t : T ⟶ Z)
    (P : proEtaleRingModules X (proEtaleConstantRing X A))
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A))
    (h : proEtaleConstantModulePullback i A P ≅ N) :
    proEtaleConstantModulePullback (t ≫ i) A P ≅
      proEtaleConstantModulePullback t A N :=
  (proEtaleConstantRingModulePullbackComposition t i A).choose.app P ≪≫
    (proEtaleConstantRingPullback A t).mapIso h

private theorem constant_zero_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    IsZero (proEtaleConstantModuleSheaf Y A
      (0 : ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let R : Sheaf (ProEt.topology Y)
      RingCat.{u + 1} := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} A)))
  let α : ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)) ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⟶ R.obj :=
    Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallyInjective _ α := (proEtaleConstantRingUnit_locallyBijective Y A).1
  have : Presheaf.IsLocallySurjective _ α := (proEtaleConstantRingUnit_locallyBijective Y A).2
  let F := PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (R := R) α
  have : F.IsLeftAdjoint :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1} (R := R) α).isLeftAdjoint
  have hz : IsZero (proEtaleConstantModulePresheaf Y.ProEt A
      (0 : ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
    rw [IsZero.iff_id_eq_zero]
    ext W x
    change x = 0
    have : Subsingleton (0 : ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    exact @Subsingleton.elim (0 : ModuleCat.{u + 1} (ULift.{u + 1} A)) this x 0
  exact F.map_isZero hz

private theorem constant_zero_over_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (V : Y.ProEt) :
    IsZero (proEtaleConstantModuleSheafOver Y A V
      (0 : ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
  let R : Sheaf ((ProEt.topology Y).over V)
      RingCat.{u + 1} := ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} A)))).over V
  let α : ((Functor.const (Over V)ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)) ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⟶ R.obj :=
    Functor.whiskerLeft (Over.forget V).op
    (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have : Presheaf.IsLocallyInjective _ α := (proEtaleConstantRingUnit_over_locallyBijective Y A V).1
  have : Presheaf.IsLocallySurjective _ α :=
    (proEtaleConstantRingUnit_over_locallyBijective Y A V).2
  let F := PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1} (R := R) α
  have : F.IsLeftAdjoint :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1} (R := R) α).isLeftAdjoint
  have hz : IsZero (proEtaleConstantModulePresheaf (Over V) A
      (0 : ModuleCat.{u + 1} (ULift.{u + 1} A))) := by
    rw [IsZero.iff_id_eq_zero]
    ext W x
    change x = 0
    have : Subsingleton (0 : ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    exact @Subsingleton.elim (0 : ModuleCat.{u + 1} (ULift.{u + 1} A)) this x 0
  exact F.map_isZero hz

private theorem locallyConstant_of_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hG : IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} Y A G) :
    IsLocallyConstantProEtaleModuleSheaf Y A F := by
  obtain ⟨I, V, f, hf, h⟩ := hG
  refine ⟨I, V, f, hf, ?_⟩
  intro a
  obtain ⟨M, _, ⟨eM⟩⟩ := h a
  exact ⟨M, ⟨(SheafOfModules.overFunctor _ (V a)).mapIso e ≪≫ eM⟩⟩

private theorem locallyConstant_of_isZero {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {F : proEtaleRingModules Y (proEtaleConstantRing Y A)} (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheaf Y A F := by
  refine ⟨PUnit.{u + 2}, fun _ ↦ ProEt.mk (𝟙 Y), fun _ ↦ 𝟙 _, ?_, ?_⟩
  · simpa only [Presieve.ofArrows_pUnit] using
      (Precoverage.mem_coverings_of_isIso (J := ProEt.precoverage Y) (𝟙 (ProEt.mk (𝟙 Y))))
  · intro a
    refine ⟨0, ⟨?_⟩⟩
    apply IsZero.iso ?_ (constant_zero_over_isZero Y A _)
    rw [IsZero.iff_id_eq_zero]
    ext W x
    exact congrArg (fun k : F ⟶ F ↦ k.val.app (Opposite.op W.unop.left) x)
      ((IsZero.iff_id_eq_zero F).mp hF)

private theorem finite_stalk_of_isZero {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {F : proEtaleRingModules Y (proEtaleConstantRing Y A)} (hF : IsZero F)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) := by
  have hz := (geometricRingModuleStalkFunctor y (proEtaleConstantRing Y A)).map_isZero hF
  have : Subsingleton (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  infer_instance

set_option linter.unusedVariables false in
/-- Extend a finite closed-side stratification by the given complementary open,
and test finite constructibility of a module with the specified restrictions.
The dependent-pair equalities retain the exact domain schemes and composite maps.
There is no reducedness or nonemptiness condition on any stratum.

Source: Stacks Project, schemes.tex Tag 02V0; properties.tex Tags 01OW and 01OZ;
topology.tex Tag 04ZA; sites-modules.tex Tag 03D8; the finite-partition convention
of def-weil-proetale-constructible-sheaf
(blueprint: lem-sf-closed-partition-module-test).

Proof (the three reviewed DAG steps):
1. Apply lem-sfb-noetherian-complementary-stratifications to i, j and S. Its closed-side
   clause appends precisely U and j to the original composites. Every subset of X is
   compact; in particular every open and its intersections with compact opens are
   compact, giving retrocompactness, and j is quasi-compact. Locally closed strata
   are constructible in this Noetherian space.
2. Apply lem-pur-proetale-module-pullback-composition to each S.immersion and i.
   Its constant-section-normalized compositor followed by the inverse image of h
   is sfClosedPartitionRestrictionIso, so the old restrictions identify with those
   of N, naturally and linearly.
3. Transport the old local trivializations and finite geometric stalks through these
   isomorphisms. On U use the supplied zero restriction. The constant zero presheaf
   is already a sheaf, hence its sheafification is zero; the identity cover trivializes
   it and its pointed-neighbourhood module colimit is zero. Thus this very extended
   partition witnesses constructibility. It has S.n + 1 positive strata. If X is empty,
   a single empty stratum is valid. No scheme is replaced by a reduction. -/
theorem sf_closed_partition_module_test
    {X Z U : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hji : Set.range j = (Set.range i)ᶜ)
    (S : FiniteLocallyClosedStratification Z)
    (hS : ∀ μ : Fin S.n, Topology.IsConstructible (S.stratum μ)) :
    (∀ V : Set X, IsOpen V → IsRetrocompact V ∧ IsCompact V) ∧ QuasiCompact j ∧
    ∃ (R : Stratification X) (e : Fin (S.n + 1) ≃ Fin R.n),
      (∀ a : Fin (S.n + 1),
        (⟨R.domain (e a), R.immersion (e a)⟩ : Σ W : Scheme.{u}, W ⟶ X) =
          Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ W : Scheme.{u}, W ⟶ X)
            (fun μ : Fin S.n ↦
              (⟨S.domain μ, S.immersion μ ≫ i⟩ : Σ W : Scheme.{u}, W ⟶ X))
            (⟨U, j⟩ : Σ W : Scheme.{u}, W ⟶ X) a) ∧
      ∀ (A : Type u) [CommRing A] [Finite A]
        (P : proEtaleRingModules X (proEtaleConstantRing X A))
        (N : proEtaleRingModules Z (proEtaleConstantRing Z A))
        (h : proEtaleConstantModulePullback i A P ≅ N)
        (hzero : IsZero (proEtaleConstantModulePullback j A P)),
        (∀ μ : Fin S.n,
          Nonempty (proEtaleConstantModulePullback (S.immersion μ ≫ i) A P ≅
            proEtaleConstantModulePullback (S.immersion μ) A N)) ∧
        Nonempty (proEtaleConstantModulePullback j A P ≅
          proEtaleConstantModuleSheaf U A (0 : ModuleCat.{u + 1} (ULift.{u + 1} A))) ∧
        ((∀ μ : Fin S.n,
          IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} (S.domain μ) A
            (proEtaleConstantModulePullback (S.immersion μ) A N) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (y : Spec (.of Ω) ⟶ S.domain μ),
            Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain μ) A)
              (proEtaleConstantModulePullback (S.immersion μ) A N))) →
          (0 < R.n ∧ ∀ a : Fin R.n,
            IsLocallyConstantProEtaleModuleSheaf (R.domain a) A
              (proEtaleConstantModulePullback (R.immersion a) A P) ∧
            ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
              (y : Spec (.of Ω) ⟶ R.domain a),
              Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (R.domain a) A)
                (proEtaleConstantModulePullback (R.immersion a) A P))) ∧
          IsConstructibleProEtaleModuleSheaf X A P) := by
  classical
  obtain ⟨_, _, _, _, _, _, hcompact, hqc, _, hclosed⟩ :=
    noetherian_complementary_stratifications j i hji
  obtain ⟨R₀, e, he, hc⟩ := hclosed S
  let R : Stratification X :=
    { n := R₀.n
      stratum := R₀.stratum
      isLocallyClosed_stratum := R₀.isLocallyClosed_stratum
      isConstructible_stratum := hc
      iUnion_stratum_eq_univ := R₀.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := R₀.pairwise_disjoint_stratum
      domain := R₀.domain
      immersion := R₀.immersion
      isImmersion := R₀.isImmersion
      range_immersion := R₀.range_immersion }
  have hpos : 0 < R.n := by
    have hn := Fintype.card_congr e
    simp only [Fintype.card_fin] at hn
    change 0 < R₀.n
    omega
  refine ⟨fun V _ ↦ ⟨fun W _ _ ↦ hcompact (V ∩ W), hcompact V⟩,
    hqc, R, e, he, ?_⟩
  intro A _ _ P N h hzero
  have hiso (μ : Fin S.n) := sfClosedPartitionRestrictionIso A i (S.immersion μ) P N h
  refine ⟨fun μ ↦ ⟨hiso μ⟩, ⟨hzero.iso (constant_zero_isZero U A)⟩, ?_⟩
  intro hN
  have hR : ∀ a : Fin R.n,
      IsLocallyConstantProEtaleModuleSheaf (R.domain a) A
        (proEtaleConstantModulePullback (R.immersion a) A P) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ R.domain a),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (R.domain a) A)
          (proEtaleConstantModulePullback (R.immersion a) A P)) := by
    let Q : (Σ W : Scheme.{u}, W ⟶ X) → Prop := fun a ↦
      IsLocallyConstantProEtaleModuleSheaf a.1 A
        (proEtaleConstantModulePullback a.2 A P) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ a.1),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing a.1 A)
          (proEtaleConstantModulePullback a.2 A P))
    intro a
    change Q ⟨R.domain a, R.immersion a⟩
    have ha := he (e.symm a)
    have ha' := congrArg (fun b ↦
      (⟨R₀.domain b, R₀.immersion b⟩ : Σ W : Scheme.{u}, W ⟶ X))
      (e.apply_symm_apply a)
    have ha := ha'.symm.trans ha
    change Q ⟨R₀.domain a, R₀.immersion a⟩
    rw [ha]
    refine Fin.lastCases ?_ (fun μ ↦ ?_) (e.symm a)
    · simp only [Fin.snoc_last]
      change Q ⟨U, j⟩
      exact ⟨locallyConstant_of_isZero hzero, finite_stalk_of_isZero hzero⟩
    · simp only [Fin.snoc_castSucc]
      change Q ⟨S.domain μ, S.immersion μ ≫ i⟩
      refine ⟨locallyConstant_of_iso (hiso μ) (hN μ).1, ?_⟩
      intro Ω _ _ y
      have : Finite ((geometricRingModuleStalkFunctor y
          (proEtaleConstantRing (S.domain μ) A)).obj
            (proEtaleConstantModulePullback (S.immersion μ) A N)) := (hN μ).2 Ω y
      let eM := (geometricRingModuleStalkFunctor y
        (proEtaleConstantRing (S.domain μ) A)).mapIso (hiso μ)
      exact Finite.of_injective eM.hom (ConcreteCategory.bijective_of_isIso eM.hom).1
  exact ⟨⟨hpos, hR⟩, R, hpos, hR⟩

end AlgebraicGeometry.Scheme
