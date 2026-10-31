/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FiniteContinuousModule
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite continuous actions detect normal exactness

Source: Stacks Project, `pione.tex`, Tag 0BS9 (`lemma-functoriality-galois-ses`).
(blueprint: lem-dl-a1-galois-category-exactness-criterion)
-/

@[expose] public section

universe u v w t

open CategoryTheory
open scoped FintypeCatDiscrete

namespace ProfiniteGrp

private theorem restriction_faithful {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (f : G →ₜ* H) : (ContAction.res FintypeCat.{t} f).Faithful where
  map_injective := by
    intro X Y a b hab
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact congrArg (fun k ↦ k.hom.hom) hab

private theorem restriction_full {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    (ContAction.res FintypeCat.{t} f).Full where
  map_surjective := by
    intro X Y a
    refine ⟨ObjectProperty.homMk ⟨a.hom.hom, ?_⟩, ?_⟩
    · intro h
      obtain ⟨g, rfl⟩ := hf h
      exact a.hom.comm g
    · rfl

private theorem action_kernel_closed {G : ProfiniteGrp.{u}}
    (T : ContAction FintypeCat.{t} G) : IsClosed (T.obj.ρ.ker : Set G) := by
  have heq : (T.obj.ρ.ker : Set G) =
      ⋂ x : T.obj.V, {g : G | (T.obj.ρ g).hom x = x} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h x ↦ ConcreteCategory.congr_hom h x,
      fun h ↦ FintypeCat.hom_ext _ _ h⟩
  rw [heq]
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  exact T.property.continuous_smul.comp (continuous_id.prodMk continuous_const)

private theorem action_descends {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (f : G →ₜ* H) (hf : Function.Surjective f)
    (T : ContAction FintypeCat.{t} G) (hker : f.toMonoidHom.ker ≤ T.obj.ρ.ker) :
    ∃ X : ContAction FintypeCat.{t} H,
      Nonempty ((ContAction.res FintypeCat.{t} f).obj X ≅ T) := by
  classical
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hf
  let ρ : H →* End T.obj.V :=
    (QuotientGroup.lift _ T.obj.ρ hker).comp e.symm.toMonoidHom
  have hρ (g : G) : ρ (f g) = T.obj.ρ g := by
    change QuotientGroup.lift _ T.obj.ρ hker (e.symm (f g)) = _
    have he : e.symm (f g) = QuotientGroup.mk g := e.symm_apply_eq.mpr rfl
    rw [he]
    rfl
  let A : Action FintypeCat.{t} H := ⟨T.obj.V, ρ⟩
  have hA : A.IsContinuous := by
    rw [Action.isContinuous_def]
    change Continuous (fun p : H × T.obj.V ↦ (ρ p.1).hom p.2)
    rw [continuous_prod_of_discrete_right]
    intro x
    apply (Topology.IsQuotientMap.of_surjective_continuous hf f.continuous).continuous_iff.mpr
    change Continuous (fun g : G ↦ (ρ (f g)).hom x)
    simp_rw [hρ]
    exact T.property.continuous_smul.comp (continuous_id.prodMk continuous_const)
  refine ⟨⟨A, hA⟩, ⟨ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) ?_)⟩⟩
  intro g
  change ρ (f g) ≫ 𝟙 _ = 𝟙 _ ≫ T.obj.ρ g
  simpa using hρ g

private theorem iso_trivial {G : ProfiniteGrp.{u}}
    {X Y : ContAction FintypeCat.{t} G} (e : X ≅ Y) (g : G)
    (hg : X.obj.ρ g = 1) : Y.obj.ρ g = 1 := by
  have hc := e.hom.hom.comm g
  rw [hg] at hc
  have hi := congrArg (fun k : X.obj.V ⟶ Y.obj.V ↦ e.inv.hom.hom ≫ k) hc
  have hinv : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 Y.obj.V :=
    congrArg (fun k ↦ k.hom.hom) e.inv_hom_id
  simpa only [End.one_def, ← Category.assoc, hinv, Category.id_comp,
    Category.comp_id] using hi.symm

-- A finite continuous action can be moved to any finite-set universe.
private theorem finite_action_model (G : ProfiniteGrp.{u})
    (S : Type v) [Finite S] [TopologicalSpace S] [DiscreteTopology S]
    [MulAction G S] [ContinuousSMul G S] :
    ∃ (T : ContAction FintypeCat.{t} G) (e : S ≃ T.obj.V),
      ∀ (g : G) (x : S), (T.obj.ρ g).hom (e x) = e (g • x) := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let V : FintypeCat.{t} := FintypeCat.of (ULift.{t} (Fin (Fintype.card S)))
  let : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  let e : S ≃ V := (Fintype.equivFin S).trans Equiv.ulift.symm
  let A : Action FintypeCat.{t} G := {
    V := V
    ρ := {
      toFun := fun g ↦ FintypeCat.homMk (fun x ↦ e (g • e.symm x))
      map_one' := by
        apply FintypeCat.hom_ext
        intro x
        change e (1 • e.symm x) = x
        simp
      map_mul' := by
        intro g h
        apply FintypeCat.hom_ext
        intro x
        change e ((g * h) • e.symm x) = e (g • e.symm (e (h • e.symm x)))
        simp [mul_smul] } }
  have hA : A.IsContinuous := by
    rw [Action.isContinuous_def]
    change Continuous (fun p : G × V ↦ e (p.1 • e.symm p.2))
    rw [continuous_prod_of_discrete_right]
    intro x
    change Continuous (fun g : G ↦ e (g • e.symm x))
    exact continuous_of_discreteTopology.comp (continuous_id.smul continuous_const)
  have he (g : G) (x : S) : (A.ρ g).hom (e x) = e (g • x) := by
    change e (g • e.symm (e x)) = e (g • x)
    rw [e.symm_apply_apply]
  exact ⟨⟨A, hA⟩, e, he⟩

private theorem coset_action (G : ProfiniteGrp.{u}) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) :
    ∃ (T : ContAction FintypeCat.{t} G) (e : (G ⧸ U) ≃ T.obj.V),
      ∀ (g a : G), (T.obj.ρ g).hom (e (QuotientGroup.mk a)) =
        e (QuotientGroup.mk (g * a)) := by
  have : Finite (G ⧸ U) := U.quotient_finite_of_isOpen hU
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  obtain ⟨T, e, he⟩ := finite_action_model.{u, u, t} G (G ⧸ U)
  exact ⟨T, e, fun g a ↦ he g (QuotientGroup.mk a)⟩

private theorem coset_fixed_iff {G : Type*} [Group G] (U : Subgroup G) (g : G) :
    (QuotientGroup.mk g : G ⧸ U) = QuotientGroup.mk 1 ↔ g ∈ U := by
  rw [QuotientGroup.eq]
  simp

private theorem full_implies_surjective {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (f : G →ₜ* H) (hf : (ContAction.res FintypeCat.{t} f).Full) :
    Function.Surjective f := by
  have := hf
  let K : ClosedSubgroup H :=
    ⟨f.toMonoidHom.range, isCompact_range f.continuous |>.isClosed⟩
  have hK : K.toSubgroup = ⊤ := by
    apply top_unique
    intro g _
    rw [closedSubgroup_eq_sInf_open K]
    apply Subgroup.mem_sInf.mpr
    intro U hU
    obtain ⟨T, e, he⟩ := coset_action.{v, t} H U hU.1
    let P : ContAction FintypeCat.{t} H :=
      ⟨⟨FintypeCat.of PUnit.{t+1}, 1⟩, ⟨continuous_snd⟩⟩
    let a : (ContAction.res FintypeCat.{t} f).obj P ⟶
        (ContAction.res FintypeCat.{t} f).obj T := ObjectProperty.homMk {
      hom := FintypeCat.homMk (fun _ ↦ e (QuotientGroup.mk 1))
      comm := by
        intro z
        apply FintypeCat.hom_ext
        intro x
        change e (QuotientGroup.mk 1) = (T.obj.ρ (f z)).hom (e (QuotientGroup.mk 1))
        rw [he, mul_one]
        apply e.injective.eq_iff.mpr
        exact ((coset_fixed_iff U (f z)).mpr (hU.2 ⟨z, rfl⟩)).symm }
    obtain ⟨b, hb⟩ := (ContAction.res FintypeCat.{t} f).map_surjective a
    have hb' : b.hom.hom = a.hom.hom := congrArg (fun k ↦ k.hom.hom) hb
    have hc := ConcreteCategory.congr_hom (b.hom.comm g) PUnit.unit
    change b.hom.hom PUnit.unit = (T.obj.ρ g).hom (b.hom.hom PUnit.unit) at hc
    rw [hb'] at hc
    change e (QuotientGroup.mk 1) = (T.obj.ρ g).hom (e (QuotientGroup.mk 1)) at hc
    rw [he, mul_one] at hc
    exact (coset_fixed_iff U g).mp (e.injective hc.symm)
  intro y
  have hy : y ∈ K.toSubgroup := by rw [hK]; exact Subgroup.mem_top y
  exact hy

private theorem actions_separate {G : ProfiniteGrp.{u}} (g : G)
    (hg : ∀ T : ContAction FintypeCat.{t} G, T.obj.ρ g = 1) : g = 1 := by
  have hbot : g ∈ (⊥ : Subgroup G) := by
    let B : ClosedSubgroup G := ⟨⊥, by
      change IsClosed ({1} : Set G)
      exact isClosed_singleton⟩
    change g ∈ B.toSubgroup
    rw [closedSubgroup_eq_sInf_open B]
    apply Subgroup.mem_sInf.mpr
    intro U hU
    obtain ⟨T, e, he⟩ := coset_action.{u, t} G U hU.1
    have h := ConcreteCategory.congr_hom (hg T) (e (QuotientGroup.mk 1))
    change (T.obj.ρ g).hom (e (QuotientGroup.mk 1)) = e (QuotientGroup.mk 1) at h
    rw [he, mul_one] at h
    exact (coset_fixed_iff U g).mp (e.injective h)
  exact hbot

/-- Restriction of finite continuous actions detects surjectivity and the closed normal kernel.
Source: Stacks Project, Tag 0BS9 (`lemma-functoriality-galois-ses`), conditions (1) and (2).
(blueprint: lem-dl-a1-galois-category-exactness-criterion)

Proof:
1. Use `ContAction FintypeCat` from `def-pod-finite-continuous-module` and Mathlib's restriction
functor `ContAction.res`. Restriction keeps the underlying finite sets and equivariant maps, so
faithfulness is automatic and fullness asserts that restricted equivariance implies equivariance.
2. Suppose the group condition holds. Surjectivity gives fullness. If the restricted `G''`-action
on a finite `G'`-set is trivial, its action kernel is an open, hence closed, normal subgroup
containing the image of `h'`. Minimality puts `ker h` in this kernel, so the action descends to
`G`. The descended action is continuous because a continuous surjection from compact `G'` to
Hausdorff `G` is a quotient map. Conversely, `h.comp h' = 1` makes every restricted `G`-action
trivial on `G''`; this property is preserved by equivariant isomorphisms.
3. Suppose the action condition holds. The image of `h` is compact and closed. If it is proper,
`lem-wf-profinite-closed-subgroup-intersection-open`, namely
`ProfiniteGrp.closedSubgroup_eq_sInf_open`, supplies a proper open subgroup `U` containing it.
The finite continuous `G`-set `G/U` has a `G'`-fixed coset `U` which is not `G`-fixed. The map
from the singleton to that coset contradicts fullness. Thus `h` is surjective.
4. Every restricted `G`-set is in the essential image, so `G''` acts trivially on all `G/V` for
open subgroups `V` of `G`. Their intersection is trivial by the same separation lemma, giving
`h.comp h' = 1`. Let `N` be the smallest closed normal subgroup containing the image of `h'`.
Then `N` is contained in `ker h`. For any open subgroup `U` containing `N`, normality of `N`
makes the `G''`-action on `G'/U` trivial. The essential-image condition implies that `ker h`
acts trivially on this quotient, hence is contained in `U`. Intersect all such open `U`, using
the separation lemma again, to get `ker h` contained in `N`, proving the leastness assertion.
-/
theorem finite_continuous_action_exactness_iff
    (G'' : ProfiniteGrp.{w}) (G' : ProfiniteGrp.{v}) (G : ProfiniteGrp.{u})
    (h' : G'' →ₜ* G') (h : G' →ₜ* G) :
    (Function.Surjective h ∧ h.comp h' = 1 ∧
      IsLeast {N : Subgroup G' | IsClosed (N : Set G') ∧ N.Normal ∧
        Set.range h' ⊆ (N : Set G')} h.toMonoidHom.ker) ↔
    ((ContAction.res FintypeCat.{t} h).Full ∧
      (ContAction.res FintypeCat.{t} h).Faithful ∧
      ∀ T : ContAction FintypeCat.{t} G',
        (∃ X : ContAction FintypeCat.{t} G,
          Nonempty ((ContAction.res FintypeCat.{t} h).obj X ≅ T)) ↔
        ∀ g'' : G'', ((ContAction.res FintypeCat.{t} h').obj T).obj.ρ g'' = 1) := by
  constructor
  · rintro ⟨hs, hc, hn⟩
    refine ⟨restriction_full h hs, restriction_faithful h, ?_⟩
    intro T
    constructor
    · rintro ⟨X, ⟨e⟩⟩ g''
      apply iso_trivial ((ContAction.res FintypeCat.{t} h').mapIso e) g''
      change X.obj.ρ (h (h' g'')) = 1
      have hh : h (h' g'') = 1 := DFunLike.congr_fun hc g''
      rw [hh, map_one]
    · intro ht
      apply action_descends h hs T
      apply hn.2
      refine ⟨action_kernel_closed T, inferInstance, ?_⟩
      rintro _ ⟨g'', rfl⟩
      exact ht g''
  · rintro ⟨hfull, _, himage⟩
    have hs : Function.Surjective h := full_implies_surjective h hfull
    have hc : h.comp h' = 1 := by
      ext g''
      apply actions_separate.{u, t} (h (h' g''))
      intro X
      exact ((himage ((ContAction.res FintypeCat.{t} h).obj X)).mp
        ⟨X, ⟨Iso.refl _⟩⟩) g''
    refine ⟨hs, hc, ?_⟩
    constructor
    · refine ⟨?_, inferInstance, ?_⟩
      · exact isClosed_eq h.continuous continuous_const
      · rintro _ ⟨g'', rfl⟩
        exact DFunLike.congr_fun hc g''
    · intro N hN
      have : N.Normal := hN.2.1
      intro k hk
      change h k = 1 at hk
      change k ∈ (⟨N, hN.1⟩ : ClosedSubgroup G').toSubgroup
      rw [closedSubgroup_eq_sInf_open (⟨N, hN.1⟩ : ClosedSubgroup G')]
      apply Subgroup.mem_sInf.mpr
      intro U hU
      obtain ⟨T, e, he⟩ := coset_action.{v, t} G' U hU.1
      have ht : ∀ g'' : G'', ((ContAction.res FintypeCat.{t} h').obj T).obj.ρ g'' = 1 := by
        intro g''
        apply FintypeCat.hom_ext
        intro x
        obtain ⟨q, rfl⟩ := e.surjective x
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
        change (T.obj.ρ (h' g'')).hom (e (QuotientGroup.mk a)) = e (QuotientGroup.mk a)
        rw [he]
        apply congrArg e
        apply Eq.symm
        apply QuotientGroup.eq.mpr
        apply hU.2
        have hh : h' g'' ∈ N := hN.2.2 ⟨g'', rfl⟩
        simpa [mul_assoc] using hN.2.1.conj_mem' (h' g'') hh a
      obtain ⟨X, ⟨i⟩⟩ := (himage T).mpr ht
      have hi : T.obj.ρ k = 1 := iso_trivial i k (by
        change X.obj.ρ (h k) = 1
        rw [hk, map_one])
      have hx := ConcreteCategory.congr_hom hi (e (QuotientGroup.mk 1))
      change (T.obj.ρ k).hom (e (QuotientGroup.mk 1)) = e (QuotientGroup.mk 1) at hx
      rw [he, mul_one] at hx
      exact (coset_fixed_iff U k).mp (e.injective hx)

end ProfiniteGrp
