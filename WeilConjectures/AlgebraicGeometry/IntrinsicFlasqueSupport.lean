/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePairFlasque
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Supported sections and flasque objects

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/def-pur-flasque-support.md`,
node `def-pur-flasque-support` (blueprint: def-pur-flasque-support).
The canonical kernel and closed inverse image are imported from
`def-exc-proetale-sections-with-support`; this file records the intrinsic
flasqueness predicate and the remaining statement of the node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A module over the intrinsic constant coefficient sheaf is flasque for an open
complement when the canonical restriction unit is an epimorphism.
Source: Stacks Tag 03DA and blueprint `def-pur-flasque-support`
(blueprint: def-pur-flasque-support). -/
def sfIntrinsicIsFlasqueFor {U X : Scheme.{u}} (j : U ⟶ X)
    (A : Type u) [CommRing A] [Finite A]
    (I : proEtaleRingModules X (proEtaleConstantRing X A)) : Prop :=
  Epi ((sfConstantModuleAdjunction j A).unit.app I)

/-- The canonical comparison from supported sections to closed direct image.
Source: Stacks Tag 09AH and blueprint `def-pur-flasque-support`
(blueprint: def-pur-flasque-support). -/
noncomputable def sfIntrinsicSupportedComparison {Z U T : Scheme.{u}}
    (i : Z ⟶ T) (j : U ⟶ T) (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicSectionsWithSupport j A ⟶
      sfIntrinsicClosedUpperShriek i j A ⋙ sfConstantModuleDirectImage i A :=
  Functor.whiskerLeft (sfIntrinsicSectionsWithSupport j A)
    (sfConstantModuleAdjunction i A).unit

private noncomputable def supportKernelIso {T U : Scheme.{u}} (j : U ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    kernel (sfConstantModuleAdjunction j A).unit ≅
      sfIntrinsicSectionsWithSupport j A := by
  refine NatIso.ofComponents
    (fun X ↦ asIso (kernelComparison (sfConstantModuleAdjunction j A).unit
      ((CategoryTheory.evaluation _ _).obj X))) ?_
  intro X Y f
  apply (cancel_mono (kernel.ι ((sfConstantModuleAdjunction j A).unit.app Y))).mp
  simp only [Category.assoc]
  change (kernel (sfConstantModuleAdjunction j A).unit).map f ≫
    kernelComparison _ ((CategoryTheory.evaluation _ _).obj Y) ≫ kernel.ι _ =
      kernelComparison _ ((CategoryTheory.evaluation _ _).obj X) ≫
        kernel.map _ _ f
          ((sfConstantModuleDirectImage j A).map
            ((sfConstantModulePullback j A).map f))
          ((sfConstantModuleAdjunction j A).unit.naturality f).symm ≫ kernel.ι _
  rw [kernelComparison_comp_ι, kernel.lift_ι, ← Category.assoc,
    kernelComparison_comp_ι]
  exact (kernel.ι (sfConstantModuleAdjunction j A).unit).naturality f

private theorem support_leftExact {T U : Scheme.{u}} (j : U ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteLimits (sfIntrinsicSectionsWithSupport j A) := by
  let C := proEtaleRingModules T (proEtaleConstantRing T A)
  let := (sfConstantModuleAdjunction j A).rightAdjoint_preservesLimits
  let D := parallelPair (sfConstantModuleAdjunction j A).unit 0
  have hD : PreservesFiniteLimits D.flip :=
    preservesFiniteLimits_of_evaluation _ (fun p ↦ by
      cases p
      · change PreservesFiniteLimits (𝟭 C)
        infer_instance
      · change PreservesFiniteLimits
          (sfConstantModulePullback j A ⋙ sfConstantModuleDirectImage j A)
        infer_instance)
  have : PreservesFiniteLimits (kernel (sfConstantModuleAdjunction j A).unit) :=
    preservesFiniteLimits_of_natIso (limitIsoFlipCompLim D).symm
  exact preservesFiniteLimits_of_natIso (supportKernelIso j A)

private theorem support_restrict_zero {T U : Scheme.{u}} (j : U ⟶ T)
    (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
    IsZero ((sfConstantModulePullback j A).obj
      ((sfIntrinsicSectionsWithSupport j A).obj M)) := by
  let L := sfConstantModulePullback j A
  let adj := sfConstantModuleAdjunction j A
  have : Mono (L.map (adj.unit.app M)) := by
    constructor
    intro Y a b hab
    have he := congrArg (fun f ↦ f ≫ adj.counit.app (L.obj M)) hab
    have ht : L.map (adj.unit.app M) ≫ adj.counit.app (L.obj M) = 𝟙 _ :=
      adj.left_triangle_components M
    simpa only [Category.assoc, ht, Category.comp_id] using he
  exact (isZero_kernel_of_mono (L.map (adj.unit.app M))).of_iso
    (PreservesKernel.iso L (adj.unit.app M))

private noncomputable def unitKernelRightIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (r : R ≅ R') (M : C) :
    kernel (a.unit.app M) ≅ kernel (b.unit.app M) := by
  let b' := b.ofNatIsoRight r.symm
  let l := a.leftAdjointUniq b'
  refine kernel.mapIso (a.unit.app M) (b'.unit.app M)
      (Iso.refl _) (R.mapIso (l.app M)) ?_ ≪≫
    kernel.mapIso (b'.unit.app M) (b.unit.app M)
      (Iso.refl _) (r.app (L'.obj M)) ?_
  · change a.unit.app M ≫ R.map (l.hom.app M) = 𝟙 M ≫ b'.unit.app M
    simpa only [Category.id_comp] using a.unit_leftAdjointUniq_hom_app b' M
  · simp [b', Adjunction.ofNatIsoRight_unit]

private theorem unitIsIsoRightIso
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (r : R ≅ R') (M : C) :
    IsIso (a.unit.app M) ↔ IsIso (b.unit.app M) := by
  let b' := b.ofNatIsoRight r.symm
  let l := a.leftAdjointUniq b'
  have h : a.unit.app M ≫ R.map (l.hom.app M) ≫ r.hom.app (L'.obj M) =
      b.unit.app M := by
    rw [← Category.assoc, a.unit_leftAdjointUniq_hom_app b' M]
    simp [b', Adjunction.ofNatIsoRight_unit]
  rw [← h]
  simp only [isIso_comp_right_iff]

private noncomputable def transportedRightIso
    {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D']
    (E : C ≌ C') (F : D ≌ D') {R : D ⥤ C} {R' : D' ⥤ C'}
    (r : F.functor ⋙ R' ≅ R ⋙ E.functor) :
    F.inverse ⋙ R ⋙ E.functor ≅ R' :=
  Functor.isoWhiskerLeft F.inverse r.symm ≪≫ F.invFunIdAssoc R'

private noncomputable def transportedKernelIso
    {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] [Abelian C] [Abelian C']
    (E : C ≌ C') (F : D ≌ D') {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) (N : C') :
    kernel (((E.symm.toAdjunction.comp a).comp F.toAdjunction).unit.app N) ≅
      E.functor.obj (kernel (a.unit.app (E.inverse.obj N))) := by
  let a' := E.symm.toAdjunction.comp a
  let e : kernel (a'.unit.app N) ≅
      kernel ((a'.comp F.toAdjunction).unit.app N) :=
    kernel.mapIso _ _ (Iso.refl _)
      ((R ⋙ E.functor).mapIso (F.unitIso.app (L.obj (E.inverse.obj N))))
      (by simp [Adjunction.comp_unit_app])
  refine e.symm ≪≫ kernel.mapIso _ _ (E.counitIso.app N).symm (Iso.refl _) ?_ ≪≫
    (PreservesKernel.iso E.functor (a.unit.app (E.inverse.obj N))).symm
  simp [a', Adjunction.comp_unit_app]

private theorem transportedUnitIsIso
    {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D']
    (E : C ≌ C') (F : D ≌ D') {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) (N : C') :
    IsIso (((E.symm.toAdjunction.comp a).comp F.toAdjunction).unit.app N) ↔
      IsIso (a.unit.app (E.inverse.obj N)) := by
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  change IsIso ((E.counitIso.inv.app N ≫ E.functor.map
    (a.unit.app (E.inverse.obj N))) ≫ (R ⋙ E.functor).map
      (F.unitIso.hom.app (L.obj (E.inverse.obj N)))) ↔ _
  rw [isIso_comp_right_iff, isIso_comp_left_iff]
  exact isIso_iff_of_reflects_iso _ E.functor

private theorem unitIsIsoOfObjIso
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {M N : C} (e : M ≅ N)
    [IsIso (a.unit.app N)] : IsIso (a.unit.app M) := by
  have h : a.unit.app M ≫ (L ⋙ R).map e.hom = e.hom ≫ a.unit.app N :=
    a.unit.naturality e.hom |>.symm
  have : IsIso (a.unit.app M ≫ (L ⋙ R).map e.hom) := by rw [h]; infer_instance
  exact (isIso_comp_right_iff _ _).mp this

private theorem constantPush_eq {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModuleDirectImage f A = proEtaleConstantModuleDirectImage f A := by
  unfold sfConstantModuleDirectImage proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing T A)
      (proEtaleConstantRing Y A) (sfConstantCoefficientIso f A) =
        proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat).homEquiv _ _).apply_symm_apply _
  rw [h]

private noncomputable def constantPushIso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicModuleEquivalence Y A).functor ⋙ sfConstantModuleDirectImage f A ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
        (sfIntrinsicModuleEquivalence T A).functor :=
  Functor.isoWhiskerLeft _ (eqToIso (constantPush_eq f A)) ≪≫
    sfIntrinsicDirectImageComparison f A

/-- The supported-sections construction is additive and left exact, its canonical
closed comparison is invertible for a quasi-compact complement, pair-flasqueness
(epimorphy of the open adjunction unit) is vanishing of the sheaf cokernel, and without
quasi-compactness the comparison can fail: for nonzero finite coefficients there is an
affine pair with non-quasi-compact complement and a module whose comparison is not
invertible (it need not fail for every such pair, and never fails for `A = 0`).
Source: Stacks Tags 03DA and 09AH and blueprint `def-pur-flasque-support`
(blueprint: def-pur-flasque-support).

Proof plan: (1) use `lem-pur-proetale-open-unit-evaluation` to identify the
kernel sectionwise and use naturality for its action on morphisms.  (2) The kernel
restricts to zero on the open complement; apply
`lem-exc-proetale-closed-essential-image` and the coefficient comparison to obtain
the closed comparison isomorphism when the complement is quasi-compact.  (3) Kernels
are sectionwise and the canonical finite-coefficient inverse image is exact, giving
left exactness and additivity.  (4) In an abelian category epimorphisms are exactly
maps with zero cokernel, giving the flasque criterion.  (5)--(7) the infinite
clopen affine construction, the opposite-index refinement, and the finite-support
section argument from `lem-pur-module-sheaf-coproduct-local-support` and
`lem-weil-pbc-proetale-immersion-limit-preservation` exhibit failure without
quasi-compactness: `T' = Spec ∏ₙ k`, `Z' = Spec(∏ₙ k / ⊕ₙ k)`, `U' = ⊔ₙ Spec k`,
`M = coker(⊕ₙ Hₙ → ∏ₙ Hₙ)`; only `A ≠ 0` is used, to see `(1,1,…) ∉ ⊕ₙ Hₙ(T')`. -/
theorem sfIntrinsicFlasqueSupport (A : Type u) [CommRing A] [Finite A]
    {Z U T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    (sfIntrinsicSectionsWithSupport j A).Additive ∧
      PreservesFiniteLimits (sfIntrinsicSectionsWithSupport j A) ∧
      (sfIntrinsicClosedUpperShriek i j A).Additive ∧
      PreservesFiniteLimits (sfIntrinsicClosedUpperShriek i j A) ∧
      (∀ [QuasiCompact j], IsIso (sfIntrinsicSupportedComparison i j A)) ∧
      (∀ I : proEtaleRingModules T (proEtaleConstantRing T A),
        sfIntrinsicIsFlasqueFor j A I ↔
          IsZero (cokernel ((sfConstantModuleAdjunction j A).unit.app I))) ∧
      (Nontrivial A →
        ∃ (Z' U' T' : Scheme.{u}) (i' : Z' ⟶ T') (j' : U' ⟶ T'),
          IsClosedImmersion i' ∧ IsOpenImmersion j' ∧ IsAffine T' ∧
            IsCompl (Set.range i') (Set.range j') ∧ ¬ QuasiCompact j' ∧
            ∃ (M : proEtaleRingModules T' (proEtaleConstantRing T' A)),
              ¬ IsIso ((sfIntrinsicSupportedComparison i' j' A).app M)) := by
  have hG := support_leftExact j A
  let := hG
  have hH : PreservesFiniteLimits (sfIntrinsicClosedUpperShriek i j A) :=
    inferInstanceAs (PreservesFiniteLimits
      (sfIntrinsicSectionsWithSupport j A ⋙ sfConstantModulePullback i A))
  refine ⟨inferInstance, hG, inferInstance, hH, ?_, ?_, ?_⟩
  · intro hqc
    have hU : Set.range j = (Set.range i)ᶜ := hPair.compl_eq.symm
    have hi (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
        IsIso ((sfIntrinsicSupportedComparison i j A).app M) :=
      (proEtaleRingModule_closed_essImage_iff_and_unit_isIso i j hU
        (proEtaleConstantRing T A) (proEtaleConstantRing Z A)
        (proEtaleConstantRing U A) (sfConstantCoefficientIso i A)
        (sfConstantCoefficientIso j A)
        ((sfIntrinsicSectionsWithSupport j A).obj M)).2 (support_restrict_zero j A M)
    exact NatIso.isIso_of_isIso_app _
  · intro I
    exact Preadditive.epi_iff_isZero_cokernel _
  · intro hA
    let := hA
    let Λ := ULift.{u + 1, u} A
    obtain ⟨X, Z', U', s, v, ha, hs, hv, hp, hnqc, M, hM⟩ :=
      ProEtale.exists_finiteSupportedClosedComparison_not_isIso Λ
    let := ha
    let := hs
    let := hv
    let E := sfIntrinsicModuleEquivalence X A
    let F := sfIntrinsicModuleEquivalence U' A
    let G := sfIntrinsicModuleEquivalence Z' A
    let N := E.functor.obj M
    let aj := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v
    let ai := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s
    let bj := sfConstantModuleAdjunction v A
    let bi := sfConstantModuleAdjunction s A
    let tj := (E.symm.toAdjunction.comp aj).comp F.toAdjunction
    let ti := (E.symm.toAdjunction.comp ai).comp G.toAdjunction
    let rj := transportedRightIso E F (constantPushIso v A)
    let ri := transportedRightIso E G (constantPushIso s A)
    let k : (sfIntrinsicSectionsWithSupport v A).obj N ≅
        E.functor.obj ((ProEtale.finiteSupportedSections Λ v).obj M) :=
      (unitKernelRightIso tj bj rj N).symm ≪≫
        transportedKernelIso E F aj N ≪≫
        E.functor.mapIso
          ((PreservesKernel.iso ((CategoryTheory.evaluation _ _).obj
            (E.inverse.obj N)) aj.unit).symm ≪≫
            (ProEtale.finiteSupportedSections Λ v).mapIso (E.unitIso.app M).symm)
    refine ⟨Z', U', X, s, v, hs, hv, ha, hp, hnqc, N, ?_⟩
    intro h
    have hb : IsIso (bi.unit.app ((sfIntrinsicSectionsWithSupport v A).obj N)) := h
    have ht := (unitIsIsoRightIso ti bi ri _).2 hb
    have hf := (transportedUnitIsIso E G ai _).1 ht
    let e : E.inverse.obj ((sfIntrinsicSectionsWithSupport v A).obj N) ≅
        (ProEtale.finiteSupportedSections Λ v).obj M :=
      E.inverse.mapIso k ≪≫ (E.unitIso.app _).symm
    let := hf
    have hi := unitIsIsoOfObjIso ai e.symm
    exact hM hi

end AlgebraicGeometry.Scheme
