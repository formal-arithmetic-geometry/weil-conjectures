/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Topology.LocallyConstant.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic
import Sheaf.RingTheory.WeaklyEtaleField

import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-!
# Affine sections of functions modulo the constant pro-etale sheaf

Source: Stacks Project, Tag 0F6D, Example `example-functions-mod-locally-constant-functions`
(blueprint: lem-cbc-proetale-functions-quotient-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def proEtContinuousSheaf (X : Scheme.{u})
    (A : Type (u + 1)) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  ((ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous _ _
    proetaleTopology).obj
    ⟨continuousMapPresheafAb A,
      .of_le proetaleTopology_le_fpqcTopology
        (isSheaf_fpqcTopology_continuousMapPresheafAb A)⟩

private noncomputable def proEtFunctions (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} := by
  let : TopologicalSpace A := ⊤
  let : IsTopologicalAddGroup A :=
    { continuous_add := continuous_top
      continuous_neg := continuous_top }
  exact proEtContinuousSheaf X A

private noncomputable def proEtFunctionsEquiv (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] (V : X.ProEt) :
    (proEtFunctions X A).obj.obj (op V) ≃+ (V.left → A) := by
  let : TopologicalSpace A := ⊤
  let : IsTopologicalAddGroup A :=
    { continuous_add := continuous_top
      continuous_neg := continuous_top }
  change C(V.left, A) ≃+ (V.left → A)
  exact
    { toFun := fun f ↦ f.toFun
      invFun := fun f ↦ ⟨f, continuous_top⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }

private noncomputable def proEtLocallyConstant (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  exact proEtContinuousSheaf X A

private noncomputable def proEtConstToLocallyConstant (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A) ⟶
      (proEtLocallyConstant X A).obj := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  exact
    { app := fun _ ↦ AddCommGrpCat.ofHom
        { toFun := fun a ↦ ContinuousMap.const _ a
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

private theorem proEtConstToLocallyConstant_locallySurjective (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    Presheaf.IsLocallySurjective (ProEt.topology X)
      (proEtConstToLocallyConstant X A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  constructor
  intro U s₀
  let s : C(U.left, A) := s₀
  let j (x : U.left) := (U.left.fiberOpens s (s x)).ι
  apply ProEt.mem_topology_of_openImmersion _ j
  · intro x
    exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
  · intro x
    refine ⟨s x, ContinuousMap.ext fun y ↦ ?_⟩
    exact y.2.symm

private theorem proEtConstToLocallyConstant_locallyInjective (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    Presheaf.IsLocallyInjective (ProEt.topology X)
      (proEtConstToLocallyConstant X A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  constructor
  intro U a b h
  by_cases hab : a = b
  · subst hab
    exact (ProEt.topology X).superset_covering (fun _ _ _ ↦ rfl)
      ((ProEt.topology X).top_mem _)
  · have : IsEmpty U.unop.left :=
      ⟨fun x ↦ hab (congrArg (fun f : C(U.unop.left, A) ↦ f x) h)⟩
    exact (ProEt.topology X).superset_covering bot_le (ProEt.bot_mem_topology _)

private noncomputable def proEtConstantToLocallyConstant (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of A) ⟶ proEtLocallyConstant X A :=
  ⟨sheafifyLift _ (proEtConstToLocallyConstant X A)
    (proEtLocallyConstant X A).property⟩

private theorem proEt_toSheafify_constantToLocallyConstant (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    toSheafify (ProEt.topology X) _ ≫
      (proEtConstantToLocallyConstant X A).hom = proEtConstToLocallyConstant X A :=
  toSheafify_sheafifyLift _ _ _

private theorem proEtConstantToLocallyConstant_isIso (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    IsIso (proEtConstantToLocallyConstant X A) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have := proEtConstToLocallyConstant_locallyInjective X A
  have := proEtConstToLocallyConstant_locallySurjective X A
  have h := proEt_toSheafify_constantToLocallyConstant X A
  refine (Sheaf.isLocallyBijective_iff_isIso (proEtConstantToLocallyConstant X A)).1
    ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify (ProEt.topology X) _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify (ProEt.topology X) _), h]
    infer_instance

private noncomputable def proEtLocallyConstantToFunctions (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    proEtLocallyConstant X A ⟶ proEtFunctions X A := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  refine ⟨{ app := fun V ↦ AddCommGrpCat.ofHom
              { toFun := fun f ↦ (proEtFunctionsEquiv X A V.unop).symm f
                map_zero' := rfl
                map_add' := fun _ _ ↦ rfl }
            naturality := fun _ _ _ ↦ rfl }⟩

private theorem proEtLocallyConstantToFunctions_mono (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    Mono (proEtLocallyConstantToFunctions X A) := by
  apply (sheafToPresheaf (ProEt.topology X) AddCommGrpCat).mono_of_mono_map
  have (V : X.ProEtᵒᵖ) : Mono
      (((sheafToPresheaf (ProEt.topology X) AddCommGrpCat).map
        (proEtLocallyConstantToFunctions X A)).app V) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro f g h
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    apply ContinuousMap.ext
    exact congrFun (congrArg (proEtFunctionsEquiv X A V.unop) h)
  exact NatTrans.mono_of_mono_app _

private theorem proEtLocallyConstantToFunctions_range (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] (V : X.ProEt) (f : V.left → A) :
    (∃ s, proEtFunctionsEquiv X A V
      ((proEtLocallyConstantToFunctions X A).hom.app (op V) s) = f) ↔
      IsLocallyConstant f := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  constructor
  · rintro ⟨s, rfl⟩
    exact (IsLocallyConstant.iff_continuous _).mpr s.continuous
  · intro hf
    exact ⟨⟨f, hf.continuous⟩, rfl⟩

private theorem exists_sheafCokernelComparison (X : Scheme.{u})
    {G F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} (i : G ⟶ F) :
    ∃ c : (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (cokernel i.hom) ≅ cokernel i,
      ∀ (V : X.ProEt) (s : F.obj.obj (op V)),
        c.hom.hom.app (op V)
            ((toSheafify (ProEt.topology X) (cokernel i.hom)).app (op V)
              ((cokernel.π i.hom).app (op V) s)) =
          (cokernel.π i).hom.app (op V) s := by
  let L := presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}
  let ε := (sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}).counit
  let eG : L.obj G.obj ≅ G := asIso (ε.app G)
  let eF : L.obj F.obj ≅ F := asIso (ε.app F)
  let c := (PreservesCokernel.iso L i.hom) ≪≫
    cokernel.mapIso (L.map i.hom) i eG eF (ε.naturality i)
  refine ⟨c, ?_⟩
  have h : L.map (cokernel.π i.hom) ≫ c.hom = eF.hom ≫ cokernel.π i := by
    simp [c, PreservesCokernel.π_iso_hom_assoc]
  intro V s
  have h' : toSheafify (ProEt.topology X) F.obj ≫
      (L.map (cokernel.π i.hom)).hom ≫ c.hom.hom = (cokernel.π i).hom := by
    change toSheafify (ProEt.topology X) F.obj ≫
      (L.map (cokernel.π i.hom) ≫ c.hom).hom = _
    rw [h]
    change toSheafify _ _ ≫ (ε.app F).hom ≫ (cokernel.π i).hom = _
    rw [← Category.assoc]
    simp [ε, sheafificationAdjunction_counit_app_val]
  have hn := toSheafify_naturality (ProEt.topology X) (cokernel.π i.hom)
  have hh := congrArg (fun t ↦ t.app (op V) s) h'
  rw [← Category.assoc, ← hn] at hh
  exact hh

private theorem exists_quotientSections_of_surjective (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A]
    {G F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (i : G ⟶ F) [Mono i] (V : X.ProEt)
    (e : F.obj.obj (op V) ≃+ (V.left → A))
    (hrange : ∀ f : V.left → A,
      (∃ s, e (i.hom.app (op V) s) = f) ↔ IsLocallyConstant f)
    (hsurj : Function.Surjective ((cokernel.π i).hom.app (op V))) :
    ∃ q : ((V.left → A) ⧸
        (LocallyConstant.coeFnAddMonoidHom : LocallyConstant V.left A →+
          (V.left → A)).range) ≃+ (cokernel i).obj.obj (op V),
      ∀ f : V.left → A,
        q (QuotientAddGroup.mk f) = (cokernel.π i).hom.app (op V) (e.symm f) := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  let E := sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)
  have hS : (S.map E).Exact :=
    (ShortComplex.exact_cokernel i).map_of_mono_of_preservesKernel E
      (inferInstance : Mono i) inferInstance
  let p : (V.left → A) →+ (cokernel i).obj.obj (op V) :=
    ((cokernel.π i).hom.app (op V)).hom.comp e.symm.toAddMonoidHom
  have hker : p.ker = (LocallyConstant.coeFnAddMonoidHom :
      LocallyConstant V.left A →+ (V.left → A)).range := by
    ext f
    change p f = 0 ↔ _
    constructor
    · intro hf
      obtain ⟨s, hs⟩ := (ShortComplex.ab_exact_iff _).mp hS (e.symm f) hf
      change i.hom.app (op V) s = e.symm f at hs
      have hf' : IsLocallyConstant f := (hrange f).mp ⟨s, by rw [hs, e.apply_symm_apply]⟩
      exact ⟨⟨f, hf'⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨s, hs⟩ := (hrange g).mpr g.isLocallyConstant
      change (cokernel.π i).hom.app (op V) (e.symm g) = 0
      rw [← hs, e.symm_apply_apply]
      have h := congrArg (fun t ↦ t.hom.app (op V) s) (cokernel.condition i)
      exact h
  have hp : Function.Surjective p := hsurj.comp e.symm.surjective
  let q := (QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective p hp)
  exact ⟨q, fun _ ↦ rfl⟩

private theorem residueFieldMap_bijective_of_surjectiveOnStalks
    {Y T : Scheme.{u}} (f : Y ⟶ T) [SurjectiveOnStalks f] (y : Y) :
    Function.Bijective (f.residueFieldMap y) := by
  refine ⟨(f.residueFieldMap y).hom.injective, ?_⟩
  intro b
  obtain ⟨a, rfl⟩ := Y.residue_surjective y b
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective y a
  exact ⟨T.residue (f y) c, rfl⟩

private theorem weaklyEtale_affine_field_points {K : Type u} [Field K] [IsSepClosed K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [WeaklyEtale g]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    T1Space U.toScheme ∧ (∀ y : U.toScheme, IsSepClosed (U.toScheme.residueField y)) := by
  let φ := Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ g)
  let := φ.hom.toAlgebra
  have : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, U)))) := by
    change WeaklyEtale (Spec.map φ)
    rw [Spec.map_preimage]
    infer_instance
  have := weaklyEtale_SpecMap_algebraMap_iff.1 this
  have : Ring.AbsolutelyFlat Γ(Y, U) :=
    .of_flat_lmul' K Γ(Y, U) (Algebra.WeaklyEtale.flat_lmul' K Γ(Y, U))
  have hh : Ring.AbsolutelyFlat Γ(Y, U) ↔
      _root_.IsReduced Γ(Y, U) ∧ ∀ p : Ideal Γ(Y, U), p.IsPrime → p.IsMaximal :=
    (Ring.AbsolutelyFlat.tfae Γ(Y, U)).out 0 1
  have hmax := (hh.mp this).2
  have : T1Space (Spec Γ(Y, U)) := by
    change T1Space (PrimeSpectrum Γ(Y, U))
    exact ⟨fun p ↦ (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr
      (hmax _ p.isPrime)⟩
  refine ⟨(Scheme.homeoOfIso hU.isoSpec).isEmbedding.t1Space, ?_⟩
  intro y
  let p := hU.isoSpec.hom y
  have : Algebra.IsSeparable K p.asIdeal.ResidueField :=
    (Algebra.weaklyEtale_field K Γ(Y, U)).2.2.2 p |>.1
  have : IsSepClosed p.asIdeal.ResidueField := IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective (algebraMap K p.asIdeal.ResidueField)
      (IsSepClosed.algebraMap_bijective K p.asIdeal.ResidueField))
  have : IsSepClosed ((Spec Γ(Y, U)).residueField p) := IsSepClosed.of_ringEquiv
    (Scheme.Spec.residueFieldIso Γ(Y, U) p).symm.commRingCatIsoToRingEquiv
  exact IsSepClosed.of_ringEquiv
    (asIso (hU.isoSpec.hom.residueFieldMap y)).commRingCatIsoToRingEquiv

private theorem weaklyEtale_field_points {K : Type u} [Field K] [IsSepClosed K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [WeaklyEtale g] :
    (∀ y : Y, IsClosed ({y} : Set Y)) ∧
      (∀ y : Y, IsSepClosed (Y.residueField y)) := by
  have ht : T1Space Y := by
    apply t1Space_iff_specializes_imp_eq.mpr
    intro a b hab
    obtain ⟨_, ⟨U, hU, rfl⟩, hb, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ b) isOpen_univ
    have ha : a ∈ U := hab.mem_open U.isOpen hb
    have htU : T1Space U := (weaklyEtale_affine_field_points g U hU).1
    have h : (⟨a, ha⟩ : U) ⤳ ⟨b, hb⟩ :=
      (subtype_specializes_iff _ _).mpr hab
    exact congrArg Subtype.val ((t1Space_iff_specializes_imp_eq.mp htU) h)
  refine ⟨fun y ↦ isClosed_singleton, ?_⟩
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsSepClosed ((Scheme.Opens.toScheme U).residueField ⟨y, hy⟩) :=
    (weaklyEtale_affine_field_points g U hU).2 ⟨y, hy⟩
  exact IsSepClosed.of_ringEquiv
    (asIso ((Scheme.Opens.ι U).residueFieldMap ⟨y, hy⟩)).symm.commRingCatIsoToRingEquiv

private theorem weaklyEtale_closed_sepclosed_points {Y T : Scheme.{u}}
    (f : Y ⟶ T) [WeaklyEtale f]
    (hclosed : ∀ x : T, IsClosed ({x} : Set T))
    (hsep : ∀ x : T, IsSepClosed (T.residueField x)) :
    (∀ y : Y, IsClosed ({y} : Set Y)) ∧
      (∀ y : Y, IsSepClosed (Y.residueField y)) := by
  have hf (x : T) := by
    have : IsSepClosed (T.residueField x) := hsep x
    have : WeaklyEtale (f.fiberToSpecResidueField x) := by
      change WeaklyEtale (pullback.snd f (T.fromSpecResidueField x))
      infer_instance
    exact weaklyEtale_field_points (K := T.residueField x) (f.fiberToSpecResidueField x)
  have hi (x : T) : IsClosedImmersion (f.fiberι x) := by
    have : IsClosedImmersion (T.fromSpecResidueField x) :=
      isClosed_singleton_iff_isClosedImmersion.mp (hclosed x)
    change IsClosedImmersion (pullback.fst f (T.fromSpecResidueField x))
    infer_instance
  constructor
  · intro y
    have := hi (f y)
    have h := (f.fiberι (f y)).isClosedEmbedding.isClosedMap
      _ ((hf (f y)).1 (f.asFiber y))
    simpa only [Set.image_singleton, Hom.fiberι_asFiber] using h
  · intro y
    have := hi (f y)
    have : IsSepClosed ((f.fiber (f y)).residueField (f.asFiber y)) :=
      (hf (f y)).2 (f.asFiber y)
    have he := RingEquiv.ofBijective ((f.fiberι (f y)).residueFieldMap (f.asFiber y)).hom
      (residueFieldMap_bijective_of_surjectiveOnStalks (f.fiberι (f y)) (f.asFiber y))
    have : IsSepClosed (Y.residueField (f.fiberι (f y) (f.asFiber y))) :=
      IsSepClosed.of_ringEquiv he.symm
    exact (congrArg (fun z : Y ↦ IsSepClosed (Y.residueField z))
      (f.fiberι_asFiber y)).mp this

private theorem proEtConstant_H_one_vanish (T : Scheme.{u}) [IsAffine T]
    (A : Type (u + 1)) [AddCommGroup A]
    (hclosed : ∀ x : T, IsClosed ({x} : Set T))
    (hsep : ∀ x : T, IsSepClosed (T.residueField x)) :
    Subsingleton (Sheaf.H ((constantSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of A)) 1) := by
  let C := (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of A)
  have : Subsingleton (Sheaf.H C 1) :=
    subsingleton_H_of_affine_closed_isSepClosed T hclosed hsep C 1 (by decide)
  have hb := ProEtale.comparisonCohomologyMap_bijective T C 1
  have hv : Subsingleton (Sheaf.H
      ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj C) 1) := by
    constructor
    intro x y
    obtain ⟨a, rfl⟩ := hb.surjective x
    obtain ⟨b, rfl⟩ := hb.surjective y
    exact congrArg _ (Subsingleton.elim a b)
  let c := (ProEtale.comparisonConstantSheafIso T).app (AddCommGrpCat.of A)
  let e := (Sheaf.functorH (ProEt.topology T) 1).mapIso c
  constructor
  intro x y
  apply (ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance |>.injective
  exact hv.elim _ _

private theorem proEtConstant_over_H_one_vanish (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] (V : X.ProEt)
    (hv : Subsingleton (Sheaf.H
      ((constantSheaf (ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A)) 1)) :
    Subsingleton (Sheaf.H
      (((constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A)).over V) 1) := by
  let J := (ProEt.topology X).over V
  let K := ProEt.topology V.left
  let e := ProEt.sliceEquiv X V
  have : e.inverse.IsDenseSubsite K J := ProEt.sliceDense X V
  let E := (e.sheafCongr J K AddCommGrpCat.{u + 1}).functor
  have : E.Additive := by
    constructor
    intro F G f g
    rfl
  let M := AddCommGrpCat.of A
  let G := ((constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj M).over V
  let c : E.obj G ≅ (constantSheaf K AddCommGrpCat.{u + 1}).obj M :=
    E.mapIso ((ProEt.topology X).overPullbackConstantSheafIso
      AddCommGrpCat.{u + 1} V |>.app M) ≪≫
      (e.constantSheafSheafCongrIso J K AddCommGrpCat.{u + 1}
        (Over.mkIdTerminal (X := V))).app M
  have hEG : Subsingleton (Sheaf.H (E.obj G) 1) := by
    let ec := (Sheaf.functorH K 1).mapIso c
    constructor
    intro x y
    apply (ConcreteCategory.isIso_iff_bijective ec.hom).mp inferInstance |>.injective
    exact hv.elim _ _
  let z := (e.constantSheafSheafCongrIso J K AddCommGrpCat.{u + 1}
    (Over.mkIdTerminal (X := V))).symm.app (AddCommGrpCat.of (ULift ℤ))
  have hb := Sheaf.H.mapFunctor_bijective E z G 1
  constructor
  intro x y
  exact hb.injective (hEG.elim _ _)

private theorem cokernel_pi_app_surjective_of_affine_closed_sepclosed
    (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (i : (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of A) ⟶ F) [Mono i]
    (hclosed : ∀ x : X, IsClosed ({x} : Set X))
    (hsep : ∀ x : X, IsSepClosed (X.residueField x))
    (V : X.ProEt) (hV : IsAffine V.left) :
    Function.Surjective ((cokernel.π i).hom.app (op V)) := by
  have hgeom : (∀ x : V.left, IsClosed ({x} : Set V.left)) ∧
      (∀ x : V.left, IsSepClosed (V.left.residueField x)) :=
    weaklyEtale_closed_sepclosed_points V.hom hclosed hsep
  have : IsAffine V.left := hV
  have hv := proEtConstant_H_one_vanish V.left A hgeom.1 hgeom.2
  have hG := proEtConstant_over_H_one_vanish X A V hv
  let R := (ProEt.topology X).overPullback AddCommGrpCat.{u + 1} V
  have : R.Additive := by
    constructor
    intro F G f g
    rfl
  have : R.IsLeftAdjoint :=
    ((Over.forget V).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      ((ProEt.topology X).over V) (ProEt.topology X)).isLeftAdjoint
  have : PreservesFiniteColimits R := inferInstance
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
  have hRS : (S.map R).ShortExact := hS.map R
  intro s
  have hzero : Sheaf.H.δ hRS (Over.mkIdTerminal (X := V)) s = 0 := hG.elim _ _
  have hmem := hzero
  rw [← AddMonoidHom.mem_ker, Sheaf.H.ker_δ] at hmem
  exact hmem


/-- Source: Stacks Project, Tag 0F6D
(blueprint: lem-cbc-proetale-functions-quotient-sections).
The functions presheaf is represented here by a sheaf `F`, with additive section
identifications `e` compatible with precomposition. The morphism `i` sends constant
sections to constant functions and its image is exactly the locally constant functions.
The first cokernel comparison identifies sheafification of the presheaf cokernel with
the sheaf cokernel, compatibly with their projections. The affine comparison sends a
function class to its image under the sheaf cokernel projection, specifying canonicity.

Proof plan:
1. Apply lem-cbc-continuous-functions-fpqc-sheaf with the indiscrete topology to obtain
all functions, and with the discrete topology to obtain locally constant functions.
Restrict these fpqc sheaves to the pro-etale site.
2. Glue constant values along open covers to identify locally constant functions with
constantSheaf (def-weil-pbc-constant-sheaf, def-weil-pbc-sheafification). Inclusion of
functions is componentwise injective, hence a monomorphism.
3. Sheafification preserves cokernels (lem-weil-pbc-sheafification-exact), giving the
short exact sequence with the abelian-sheaf cokernel.
4. For a weakly etale object over the stated base, closedness and separable closedness
pass to its points: use weakly etale base change, the weakly etale field description,
and lem-pc-sepclosed-finite-sep-trivial. The fibre over a closed base point is closed;
its affine coordinate rings are integral over a field and have separable residue fields.
5. The etale/pro-etale comparison identifies H1 of the constant sheaf with etale H1,
which vanishes by lem-cbc-affine-sepclosed-etale-acyclic. Slice localization identifies
this with object cohomology (lem-weil-pbc-proetale-restriction-injectives and
lem-weil-pbc-cohomology-over-object-localization).
6. Apply lem-weil-pbc-derived-functor-long-exact. The vanishing makes the cokernel
projection surjective on affine sections, with kernel the locally constant functions.
The first isomorphism theorem gives the displayed additive equivalence. -/
theorem exists_proEtale_functions_quotient_sections (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    ∃ (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
      (e : ∀ V : X.ProEt, F.obj.obj (op V) ≃+ (V.left → A)),
      (∀ (U V : X.ProEt) (f : U ⟶ V) (s : F.obj.obj (op V)) (x : U.left),
        e U (F.obj.map f.op s) x = e V s (f.left x)) ∧
      ∃ (i : (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of A) ⟶ F),
        Mono i ∧
        (∀ (V : X.ProEt) (a : A) (x : V.left),
          e V (i.hom.app (op V)
            ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app (op V) a)) x = a) ∧
        (∀ (V : X.ProEt) (f : V.left → A),
          (∃ s, e V (i.hom.app (op V) s) = f) ↔ IsLocallyConstant f) ∧
        (∃ c : (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
            (cokernel i.hom) ≅ cokernel i,
          ∀ (V : X.ProEt) (s : F.obj.obj (op V)),
            c.hom.hom.app (op V)
                ((toSheafify (ProEt.topology X) (cokernel i.hom)).app (op V)
                  ((cokernel.π i.hom).app (op V) s)) =
              (cokernel.π i).hom.app (op V) s) ∧
        ((∀ x : X, IsClosed ({x} : Set X)) →
          (∀ x : X, IsSepClosed (X.residueField x)) →
          ∀ (V : X.ProEt), IsAffine V.left →
            ∃ q : ((V.left → A) ⧸
                (LocallyConstant.coeFnAddMonoidHom : LocallyConstant V.left A →+
                  (V.left → A)).range) ≃+ (cokernel i).obj.obj (op V),
              ∀ f : V.left → A,
                q (QuotientAddGroup.mk f) =
                  (cokernel.π i).hom.app (op V) ((e V).symm f)) := by
  let F := proEtFunctions X A
  let e := proEtFunctionsEquiv X A
  let j := proEtConstantToLocallyConstant X A
  have : IsIso j := proEtConstantToLocallyConstant_isIso X A
  let k := proEtLocallyConstantToFunctions X A
  have : Mono k := proEtLocallyConstantToFunctions_mono X A
  let i := j ≫ k
  have : Mono i := inferInstance
  have hrange (V : X.ProEt) (f : V.left → A) :
      (∃ s, e V (i.hom.app (op V) s) = f) ↔ IsLocallyConstant f := by
    rw [← proEtLocallyConstantToFunctions_range X A V f]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨j.hom.app (op V) s, hs⟩
    · rintro ⟨s, hs⟩
      have hbij := (ConcreteCategory.isIso_iff_bijective (j.hom.app (op V))).mp
        (inferInstance : IsIso (j.hom.app (op V)))
      obtain ⟨t, rfl⟩ := hbij.surjective s
      exact ⟨t, hs⟩
  refine ⟨F, e, (fun _ _ _ _ _ ↦ rfl), i, inferInstance, ?_, hrange,
    exists_sheafCokernelComparison X i, ?_⟩
  · intro V a x
    have h := congrArg (fun t ↦ t.app (op V) a)
      (proEt_toSheafify_constantToLocallyConstant X A)
    exact congrArg (fun f ↦ e V (k.hom.app (op V) f) x) h
  · intro hclosed hsep V hV
    have hsurj : Function.Surjective ((cokernel.π i).hom.app (op V)) :=
      cokernel_pi_app_surjective_of_affine_closed_sepclosed X A F i
        hclosed hsep V hV
    exact exists_quotientSections_of_surjective X A i V (e V) (hrange V) hsurj

end AlgebraicGeometry.Scheme
