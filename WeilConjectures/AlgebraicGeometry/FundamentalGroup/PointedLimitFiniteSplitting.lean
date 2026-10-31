/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Splittings over arbitrary connected pointed finite étale limits

Source: Stacks Project, Tag 0BND (1), (3), and the finite-coset and limit arguments
(blueprint: lem-sfb-pointed-limit-finite-splitting).

`PointedCosetSystem` and `PointedCosetLimit` package precisely the input system and
its given connected pointed limit. `PointedLimitSplitting` packages the simultaneous
splitting, factorization, and normalized right deck action. A small profinite model
of the fundamental group is identified with the fibre-functor automorphisms by
`IsFundamentalGroup`; no additional restriction on monodromy is imposed.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits PreGaloisCategory
namespace AlgebraicGeometry.Scheme

/-- Forget a finite étale cover to a scheme over its base.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-limit-finite-splitting). -/
abbrev finiteEtaleOver (X : Scheme.{u}) : X.FiniteEtale ⥤ Over X :=
  ObjectProperty.ι _ ⋙ MorphismProperty.Over.forget _ _ X

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ Y, MulAction G ((FiniteEtale.fiber x).obj Y)]

/-- The given pointed connected covers with fibres `G/N`, and their pointed quotient
transitions. Equivariance and the transition formula are imposed on all representatives,
so they specify the quotient maps without making any choices of representatives.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-limit-finite-splitting). -/
structure PointedCosetSystem where
  covers : OpenNormalSubgroup G ⥤ X.FiniteEtale
  connected : ∀ N, ConnectedSpace (covers.obj N).obj.left
  label : ∀ N, (G ⧸ N.toSubgroup) ≃ (FiniteEtale.fiber x).obj (covers.obj N)
  label_smul : ∀ (N : OpenNormalSubgroup G) (a b : G),
    label N (QuotientGroup.mk (a * b)) = a • label N (QuotientGroup.mk b)
  transition : ∀ {M N : OpenNormalSubgroup G} (h : M ≤ N) (a : G),
    (FiniteEtale.fiber x).map (covers.map (homOfLE h)) (label M (QuotientGroup.mk a)) =
      label N (QuotientGroup.mk a)

/-- A given limit in schemes over `X`, with the compatible geometric marked point and
connected total scheme. Source: Stacks 0BND and the agent limit argument
(blueprint: lem-sfb-pointed-limit-finite-splitting). -/
structure PointedCosetLimit (S : PointedCosetSystem x G) where
  cone : Cone (S.covers ⋙ finiteEtaleOver X)
  isLimit : IsLimit cone
  point : Spec (.of Ω) ⟶ cone.pt.left
  point_base : point ≫ cone.pt.hom = x
  point_leg : ∀ N, point ≫ (cone.π.app N).left = (S.label N 1).left
  connected : ConnectedSpace cone.pt.left

variable {x G} {S : PointedCosetSystem x G} (L : PointedCosetLimit x G S)

/-- The full finite-cover splitting and right deck action on this given limit.
`IsColimit` of the graph cofan says exactly that the canonical map from the coproduct
of copies of `T` is an isomorphism; it also covers an empty geometric fibre.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-limit-finite-splitting). -/
structure PointedLimitSplitting where
  sectionMap : ∀ Y : X.FiniteEtale, (FiniteEtale.fiber x).obj Y →
    (L.cone.pt ⟶ (finiteEtaleOver X).obj Y)
  section_point : ∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y),
    L.point ≫ (sectionMap Y s).left = s.left
  section_unique : ∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y)
    (b : L.cone.pt ⟶ (finiteEtaleOver X).obj Y),
    L.point ≫ b.left = s.left → b = sectionMap Y s
  splitting : ∀ Y : X.FiniteEtale,
    Nonempty (IsColimit (Cofan.mk (Limits.pullback L.cone.pt.hom Y.obj.hom)
      (fun s : (FiniteEtale.fiber x).obj Y ↦
        Limits.pullback.lift (𝟙 L.cone.pt.left) (sectionMap Y s).left
          ((Category.id_comp _).trans (Over.w (sectionMap Y s)).symm))))
  finiteStage : ∀ (Y : X.FiniteEtale) (N : OpenNormalSubgroup G),
    (∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s) →
    (FiniteEtale.fiber x).obj Y → (S.covers.obj N ⟶ Y)
  finiteStage_formula : ∀ (Y : X.FiniteEtale) (N : OpenNormalSubgroup G)
    (k : ∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s)
    (s : (FiniteEtale.fiber x).obj Y) (a : G),
    (FiniteEtale.fiber x).map (finiteStage Y N k s) (S.label N (QuotientGroup.mk a)) =
      a • s
  finiteStage_unique : ∀ (Y : X.FiniteEtale) (N : OpenNormalSubgroup G)
    (k : ∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s)
    (s : (FiniteEtale.fiber x).obj Y) (b : S.covers.obj N ⟶ Y),
    (∀ a : G, (FiniteEtale.fiber x).map b (S.label N (QuotientGroup.mk a)) = a • s) →
      b = finiteStage Y N k s
  factor : ∀ (Y : X.FiniteEtale) (N : OpenNormalSubgroup G)
    (k : ∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s)
    (s : (FiniteEtale.fiber x).obj Y),
    (L.cone.π.app N).left ≫ (finiteStage Y N k s).hom.left = (sectionMap Y s).left
  refinement : ∀ (Y : X.FiniteEtale) (M N : OpenNormalSubgroup G) (h : M ≤ N)
    (kM : ∀ (n : M.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s)
    (kN : ∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s)
    (s : (FiniteEtale.fiber x).obj Y),
    S.covers.map (homOfLE h) ≫ finiteStage Y N kN s = finiteStage Y M kM s
  natural : ∀ {Y Z : X.FiniteEtale} (b : Y ⟶ Z) (s : (FiniteEtale.fiber x).obj Y),
    (sectionMap Y s).left ≫ b.hom.left =
      (sectionMap Z ((FiniteEtale.fiber x).map b s)).left
  deck : G → Aut L.cone.pt
  deck_leg : ∀ (g : G) (N : OpenNormalSubgroup G),
    (deck g).hom.left ≫ (L.cone.π.app N).left =
      (sectionMap (S.covers.obj N) (S.label N (QuotientGroup.mk g))).left
  deck_unique : ∀ (g : G) (b : Aut L.cone.pt),
    (∀ N : OpenNormalSubgroup G, b.hom.left ≫ (L.cone.π.app N).left =
      (sectionMap (S.covers.obj N) (S.label N (QuotientGroup.mk g))).left) → b = deck g
  section_deck : ∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y) (g : G),
    (deck g).hom.left ≫ (sectionMap Y s).left = (sectionMap Y (g • s)).left
  deck_one : deck 1 = 1
  deck_mul : ∀ g h : G, (deck g).hom ≫ (deck h).hom = (deck (g * h)).hom

private theorem finiteEtale_point_ext {T : Scheme.{u}} [ConnectedSpace T]
    (t : Spec (.of Ω) ⟶ T) (a : T ⟶ X) (Y : X.FiniteEtale)
    (b c : T ⟶ Y.obj.left) (hb : b ≫ Y.obj.hom = a) (hc : c ≫ Y.obj.hom = a)
    (h : t ≫ b = t ≫ c) : b = c := by
  let U : T.FiniteEtale :=
    ⟨Etale.mk (𝟙 T), inferInstanceAs (IsFinite (𝟙 T))⟩
  let V := (FiniteEtale.pullback a).obj Y
  let β : U ⟶ V := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.lift (f := Y.obj.hom) (g := a) b (𝟙 T)
      (hb.trans (Category.id_comp a).symm)) (by
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = 𝟙 T
      simp))
  let γ : U ⟶ V := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.lift (f := Y.obj.hom) (g := a) c (𝟙 T)
      (hc.trans (Category.id_comp a).symm)) (by
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = 𝟙 T
      simp))
  have : ConnectedSpace U.obj.left := inferInstanceAs (ConnectedSpace T)
  have : IsConnected U := FiniteEtale.isConnected_of_connectedSpace U
  have e : β = γ := evaluation_injective_of_isConnected (FiniteEtale.fiber t) U V
    (FiniteEtale.fiberMk t U t (Category.comp_id t)) (FiniteEtale.fiber_ext t (by
      change t ≫ Limits.pullback.lift b (𝟙 T) _ =
        t ≫ Limits.pullback.lift c (𝟙 T) _
      apply Limits.pullback.hom_ext <;> simp [h]))
  have := congrArg (fun v : U ⟶ V ↦ v.hom.left ≫ Limits.pullback.fst Y.obj.hom a) e
  simpa [β, γ] using this

private theorem pointedLimit_hom_ext {T : Scheme.{u}}
    (a : T ⟶ X) (b c : T ⟶ L.cone.pt.left)
    (hb : b ≫ L.cone.pt.hom = a) (hc : c ≫ L.cone.pt.hom = a)
    (h : ∀ N, b ≫ (L.cone.π.app N).left = c ≫ (L.cone.π.app N).left) : b = c := by
  have e : (Over.homMk b hb : Over.mk a ⟶ L.cone.pt) = Over.homMk c hc := by
    apply L.isLimit.hom_ext
    intro N
    apply Over.OverMorphism.ext
    exact h N
  exact congrArg (fun v ↦ v.left) e

private theorem pointedLimit_point_ext {T : Scheme.{u}} [ConnectedSpace T]
    (t : Spec (.of Ω) ⟶ T) (a : T ⟶ X) (b c : T ⟶ L.cone.pt.left)
    (hb : b ≫ L.cone.pt.hom = a) (hc : c ≫ L.cone.pt.hom = a)
    (h : t ≫ b = t ≫ c) : b = c := by
  apply pointedLimit_hom_ext L a b c hb hc
  intro N
  apply finiteEtale_point_ext t a (S.covers.obj N)
  · rw [Category.assoc, show (L.cone.π.app N).left ≫ (S.covers.obj N).obj.hom =
      L.cone.pt.hom from Over.w (L.cone.π.app N), hb]
  · rw [Category.assoc, show (L.cone.π.app N).left ≫ (S.covers.obj N).obj.hom =
      L.cone.pt.hom from Over.w (L.cone.π.app N), hc]
  · simpa only [← Category.assoc] using congrArg (· ≫ (L.cone.π.app N).left) h

private theorem exists_trivializing_subgroup [ConnectedSpace X]
    [IsFundamentalGroup (FiniteEtale.fiber x) G] (Y : X.FiniteEtale) :
    ∃ N : OpenNormalSubgroup G,
      ∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s := by
  let E := (FiniteEtale.fiber x).obj Y
  let ρ := MulAction.toPermHom G E
  have : ContinuousSMul G E := IsFundamentalGroup.continuous_smul Y
  have hopen : IsOpen (ρ.ker : Set G) := by
    have he : (ρ.ker : Set G) = ⋂ s : E, (MulAction.stabilizer G s : Set G) := by
      ext g
      simp only [Set.mem_iInter]
      exact ⟨fun h s ↦ congrArg (fun v : Equiv.Perm E ↦ v s) h,
        fun h ↦ Equiv.ext h⟩
    rw [he]
    exact isOpen_iInter_of_finite fun s ↦ stabilizer_isOpen G s
  let N : OpenNormalSubgroup G := { toSubgroup := ρ.ker, isOpen' := hopen }
  refine ⟨N, fun n s ↦ ?_⟩
  exact congrArg (fun v : Equiv.Perm E ↦ v s) n.property

private theorem exists_finiteStage [ConnectedSpace X]
    [IsFundamentalGroup (FiniteEtale.fiber x) G]
    (Y : X.FiniteEtale) (N : OpenNormalSubgroup G)
    (k : ∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s)
    (s : (FiniteEtale.fiber x).obj Y) :
    ∃ b : S.covers.obj N ⟶ Y, ∀ a : G,
      (FiniteEtale.fiber x).map b (S.label N (QuotientGroup.mk a)) = a • s := by
  let E := (FiniteEtale.fiber x).obj Y
  let ρ : G ⧸ N.toSubgroup →* Equiv.Perm E :=
    QuotientGroup.lift N.toSubgroup (MulAction.toPermHom G E) (fun n hn ↦
      Equiv.ext (fun z ↦ k ⟨n, hn⟩ z))
  let e := FiniteEtale.equivalenceContAction x G
  let m : e.functor.obj (S.covers.obj N) ⟶ e.functor.obj Y :=
    ObjectProperty.homMk
      { hom := FintypeCat.homMk (fun z ↦ ρ ((S.label N).symm z) s)
        comm g := FintypeCat.hom_ext _ _ fun z ↦ by
          obtain ⟨q, rfl⟩ := (S.label N).surjective z
          obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
          change ρ ((S.label N).symm (g • S.label N (QuotientGroup.mk a))) s =
            g • ρ ((S.label N).symm (S.label N (QuotientGroup.mk a))) s
          rw [← S.label_smul N g a, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          change (g * a) • s = g • (a • s)
          exact mul_smul g a s }
  refine ⟨e.fullyFaithfulFunctor.preimage m, fun a ↦ ?_⟩
  have hm := congrArg (fun v ↦ v.hom.hom (S.label N (QuotientGroup.mk a)))
    (e.fullyFaithfulFunctor.map_preimage m)
  change (FiniteEtale.fiber x).map (e.fullyFaithfulFunctor.preimage m)
    (S.label N (QuotientGroup.mk a)) =
      ρ ((S.label N).symm (S.label N (QuotientGroup.mk a))) s at hm
  rw [Equiv.symm_apply_apply] at hm
  exact hm

private theorem finiteStage_ext [ConnectedSpace X]
    (Y : X.FiniteEtale) (N : OpenNormalSubgroup G)
    (b c : S.covers.obj N ⟶ Y)
    (h : ∀ a : G, (FiniteEtale.fiber x).map b (S.label N (QuotientGroup.mk a)) =
      (FiniteEtale.fiber x).map c (S.label N (QuotientGroup.mk a))) : b = c := by
  apply (FiniteEtale.fiber x).map_injective
  apply FintypeCat.hom_ext
  intro z
  obtain ⟨q, rfl⟩ := (S.label N).surjective z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact h a

private theorem graph_isColimit {T : Scheme.{u}} [ConnectedSpace T]
    (t : Spec (.of Ω) ⟶ T) (a : T ⟶ X) (ht : t ≫ a = x) (Y : X.FiniteEtale)
    (σ : (FiniteEtale.fiber x).obj Y → (Over.mk a ⟶ (finiteEtaleOver X).obj Y))
    (hσ : ∀ s, t ≫ (σ s).left = s.left) :
    Nonempty (IsColimit (Cofan.mk (Limits.pullback a Y.obj.hom)
      (fun s : (FiniteEtale.fiber x).obj Y ↦
        Limits.pullback.lift (f := a) (g := Y.obj.hom) (𝟙 T) (σ s).left
          ((Category.id_comp _).trans (Over.w (σ s)).symm)))) := by
  classical
  let E := (FiniteEtale.fiber x).obj Y
  let d : (∐ fun _ : E ↦ T) ⟶ T := Sigma.desc fun _ ↦ 𝟙 T
  have : Etale d := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let A : T.FiniteEtale := ⟨Etale.mk d, inferInstanceAs (IsFinite d)⟩
  have : Etale Y.obj.hom := Y.obj.prop
  have : IsFinite Y.obj.hom := Y.property
  let B : T.FiniteEtale := ⟨Etale.mk (Limits.pullback.fst a Y.obj.hom),
    inferInstanceAs (IsFinite (Limits.pullback.fst a Y.obj.hom))⟩
  let v (s : E) := Limits.pullback.lift (f := a) (g := Y.obj.hom) (𝟙 T) (σ s).left
    ((Category.id_comp _).trans (Over.w (σ s)).symm)
  let φ : A ⟶ B := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Sigma.desc v) (Sigma.hom_ext _ _ fun s ↦ by
      change Sigma.ι _ s ≫ Sigma.desc v ≫ Limits.pullback.fst a Y.obj.hom =
        Sigma.ι _ s ≫ d
      simp [v, d]))
  have : IsIso ((FiniteEtale.fiber t).map φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro z w hzw
      have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
      obtain ⟨i, z', hz'⟩ := exists_comp_sigmaι_eq_of_subsingleton
        (show Spec (.of Ω) ⟶ _ from z.left)
      obtain ⟨j, w', hw'⟩ := exists_comp_sigmaι_eq_of_subsingleton
        (show Spec (.of Ω) ⟶ _ from w.left)
      change z' ≫ Sigma.ι (fun _ : E ↦ T) i = z.left at hz'
      change w' ≫ Sigma.ι (fun _ : E ↦ T) j = w.left at hw'
      have hz : z' = t := by
        have hz := FiniteEtale.fiber_left_comp t z
        rw [← hz', Category.assoc] at hz
        simpa [A, d] using hz
      have hw : w' = t := by
        have hw := FiniteEtale.fiber_left_comp t w
        rw [← hw', Category.assoc] at hw
        simpa [A, d] using hw
      have hij : i = j := FiniteEtale.fiber_ext x (by
        have hh := congrArg (fun q ↦ q.left ≫ Limits.pullback.snd a Y.obj.hom) hzw
        change (z.left ≫ Sigma.desc v) ≫ _ = (w.left ≫ Sigma.desc v) ≫ _ at hh
        rw [← hz', ← hw', hz, hw] at hh
        simpa only [Category.assoc, Sigma.ι_desc_assoc, v, Limits.pullback.lift_snd,
          hσ] using hh)
      exact FiniteEtale.fiber_ext t (by rw [← hz', ← hw', hz, hw, hij])
    · intro z
      let y : E := FiniteEtale.fiberMk x Y
        (z.left ≫ Limits.pullback.snd a Y.obj.hom) (by
          rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc]
          exact (congrArg (· ≫ a) (FiniteEtale.fiber_left_comp t z)).trans ht)
      refine ⟨FiniteEtale.fiberMk t A (t ≫ Sigma.ι (fun _ : E ↦ T) y)
        (by simp [A, d]), FiniteEtale.fiber_ext t ?_⟩
      change (t ≫ Sigma.ι (fun _ : E ↦ T) y) ≫ Sigma.desc v = z.left
      apply Limits.pullback.hom_ext
      · have hz := (FiniteEtale.fiber_left_comp t z).symm
        change t = z.left ≫ Limits.pullback.fst a Y.obj.hom at hz
        simpa only [Category.assoc, Sigma.ι_desc_assoc, v, Limits.pullback.lift_fst,
          Category.comp_id] using hz
      · have hy := hσ y
        change t ≫ (σ y).left = z.left ≫ Limits.pullback.snd a Y.obj.hom at hy
        simpa only [Category.assoc, Sigma.ι_desc_assoc, v, Limits.pullback.lift_snd]
          using hy
  have : IsIso φ := isIso_of_reflects_iso φ (FiniteEtale.fiber t)
  have : IsIso (Sigma.desc v) :=
    inferInstanceAs (IsIso ((finiteEtaleOver T ⋙ Over.forget T).map φ))
  apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr
  change IsIso (Sigma.desc v)
  infer_instance

/-- Finite covers split over every connected pointed limit of the specified coset system.
Source: Stacks 0BND (1), (3) (blueprint: lem-sfb-pointed-limit-finite-splitting).

Proof (node steps 1--5). The kernel of the finite permutation action on each fibre is
open normal (the whole group for the empty fibre). For every subgroup killing the fibre,
the equivariant formula `aN ↦ a • s` gives the unique finite-stage map by
`thm-galois-fundamental`. The equivariant inverse bijections `(aN,s) ↦ (aN,a • s)` and
`(aN,e) ↦ (aN,a⁻¹ • e)` give the finite-stage splitting. Pulling back along the limit
projection gives the graph coproduct, including the empty coproduct. On connected `T`,
sections of this split cover correspond to one label, proving marked-point uniqueness.
Refinement formulas agree on all cosets, and intersections compare any two choices of
subgroup. Cover naturality follows from marked-point uniqueness. For `g`, the maps with
labels `gN` form a cone, hence determine a unique limit endomorphism `d_g`. Applying the
finite-stage formula gives `f_s d_g = f_(g s)`. Equality on all limit legs gives
`d_1 = 1` and `d_h d_g = d_(g h)`; `d_(g⁻¹)` is the inverse, hence these are automorphisms. -/
theorem exists_pointedLimitSplitting [ConnectedSpace X] [CompactSpace X]
    [QuasiSeparatedSpace X] [IsFundamentalGroup (FiniteEtale.fiber x) G] :
    Nonempty (PointedLimitSplitting L) := by
  classical
  let := L.connected
  let b (Y : X.FiniteEtale) (N : OpenNormalSubgroup G)
      (k : ∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s)
      (s : (FiniteEtale.fiber x).obj Y) : S.covers.obj N ⟶ Y :=
    (exists_finiteStage Y N k s).choose
  have bf (Y : X.FiniteEtale) (N : OpenNormalSubgroup G) (k) (s) (a : G) :
      (FiniteEtale.fiber x).map (b Y N k s) (S.label N (QuotientGroup.mk a)) = a • s :=
    (exists_finiteStage Y N k s).choose_spec a
  choose N k using (exists_trivializing_subgroup (x := x) (G := G))
  let sec (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y) :
      L.cone.pt ⟶ (finiteEtaleOver X).obj Y :=
    L.cone.π.app (N Y) ≫ (finiteEtaleOver X).map (b Y (N Y) (k Y) s)
  have sp (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y) :
      L.point ≫ (sec Y s).left = s.left := by
    change L.point ≫ (L.cone.π.app (N Y)).left ≫ (b Y (N Y) (k Y) s).hom.left = _
    rw [← Category.assoc, L.point_leg]
    have e := congrArg (fun z ↦ z.left) (bf Y (N Y) (k Y) s 1)
    simpa only [one_smul, FiniteEtale.fiber_map_left, QuotientGroup.mk_one] using e
  have su (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y)
      (v : L.cone.pt ⟶ (finiteEtaleOver X).obj Y)
      (h : L.point ≫ v.left = s.left) : v = sec Y s := by
    apply Over.OverMorphism.ext
    exact finiteEtale_point_ext L.point L.cone.pt.hom Y v.left (sec Y s).left
      (Over.w v) (Over.w (sec Y s)) (h.trans (sp Y s).symm)
  have sn {Y Z : X.FiniteEtale} (v : Y ⟶ Z) (s : (FiniteEtale.fiber x).obj Y) :
      (sec Y s).left ≫ v.hom.left = (sec Z ((FiniteEtale.fiber x).map v s)).left := by
    have e := su Z ((FiniteEtale.fiber x).map v s)
      (sec Y s ≫ (finiteEtaleOver X).map v) (by
        change L.point ≫ (sec Y s).left ≫ v.hom.left = _
        rw [← Category.assoc, sp, FiniteEtale.fiber_map_left])
    exact congrArg (fun z ↦ z.left) e
  have fac (Y : X.FiniteEtale) (N : OpenNormalSubgroup G) (k) (s) :
      (L.cone.π.app N).left ≫ (b Y N k s).hom.left = (sec Y s).left := by
    have e := su Y s (L.cone.π.app N ≫ (finiteEtaleOver X).map (b Y N k s)) (by
      change L.point ≫ (L.cone.π.app N).left ≫ (b Y N k s).hom.left = _
      rw [← Category.assoc, L.point_leg]
      have e := congrArg (fun z ↦ z.left) (bf Y N k s 1)
      simpa only [one_smul, FiniteEtale.fiber_map_left, QuotientGroup.mk_one] using e)
    exact congrArg (fun z ↦ z.left) e
  let dc (g : G) : Cone (S.covers ⋙ finiteEtaleOver X) :=
    { pt := L.cone.pt
      π :=
        { app N := sec (S.covers.obj N) (S.label N (QuotientGroup.mk g))
          naturality M N h := by
            apply Over.OverMorphism.ext
            change (sec (S.covers.obj N) _).left =
              (sec (S.covers.obj M) _).left ≫ (S.covers.map h).hom.left
            rw [sn]
            congr 2
            have e : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
            simpa only [e] using (S.transition (leOfHom h) g).symm } }
  let d (g : G) : L.cone.pt ⟶ L.cone.pt := L.isLimit.lift (dc g)
  have dl (g : G) (N : OpenNormalSubgroup G) :
      (d g).left ≫ (L.cone.π.app N).left =
        (sec (S.covers.obj N) (S.label N (QuotientGroup.mk g))).left :=
    congrArg (fun z ↦ z.left) (L.isLimit.fac (dc g) N)
  have ds (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y) (g : G) :
      (d g).left ≫ (sec Y s).left = (sec Y (g • s)).left := by
    rw [← fac Y (N Y) (k Y) s, ← Category.assoc, dl, sn, bf Y (N Y) (k Y) s g]
  have d1 : d 1 = 𝟙 _ := by
    apply L.isLimit.hom_ext
    intro N
    apply Over.OverMorphism.ext
    change (d 1).left ≫ (L.cone.π.app N).left = (L.cone.π.app N).left
    rw [dl]
    exact congrArg (fun z ↦ z.left) (su (S.covers.obj N) (S.label N 1)
      (L.cone.π.app N) (L.point_leg N)).symm
  have dm (g h : G) : d g ≫ d h = d (g * h) := by
    apply L.isLimit.hom_ext
    intro N
    apply Over.OverMorphism.ext
    change ((d g).left ≫ (d h).left) ≫ (L.cone.π.app N).left =
      (d (g * h)).left ≫ (L.cone.π.app N).left
    rw [Category.assoc, dl, ds, ← S.label_smul N g h, dl]
  let deck (g : G) : Aut L.cone.pt :=
    { hom := d g
      inv := d g⁻¹
      hom_inv_id := by rw [dm, mul_inv_cancel, d1]
      inv_hom_id := by rw [dm, inv_mul_cancel, d1] }
  refine ⟨{ sectionMap := sec
            section_point := sp
            section_unique := su
            splitting := fun Y ↦ graph_isColimit L.point L.cone.pt.hom L.point_base Y
              (sec Y) (sp Y)
            finiteStage := b
            finiteStage_formula := bf
            finiteStage_unique := ?_
            factor := fac
            refinement := ?_
            natural := sn
            deck := deck
            deck_leg := dl
            deck_unique := ?_
            section_deck := ds
            deck_one := ?_
            deck_mul := dm }⟩
  · intro Y N k s v hv
    exact finiteStage_ext Y N v (b Y N k s) (fun a ↦ (hv a).trans (bf Y N k s a).symm)
  · intro Y M N h kM kN s
    apply finiteStage_ext Y M
    intro a
    simp only [Functor.map_comp, FintypeCat.comp_apply]
    rw [S.transition h a, bf Y N kN s a, bf Y M kM s a]
  · intro g v hv
    apply Iso.ext
    apply L.isLimit.hom_ext
    intro N
    apply Over.OverMorphism.ext
    exact (hv N).trans (dl g N).symm
  · apply Iso.ext
    exact d1

/-- A pointed comparison of two specified limits over a pointed morphism of bases.
The target point is literally the composite of the source point with the base map,
as in Stacks 0BND (3).
Source: Stacks 0BND (blueprint: lem-sfb-pointed-limit-finite-splitting). -/
structure PointedLimitComparison {X' : Scheme.{u}} (f : X' ⟶ X)
    (x' : Spec (.of Ω) ⟶ X') (G' : ProfiniteGrp.{u})
    [∀ Y, MulAction G' ((FiniteEtale.fiber x').obj Y)]
    [∀ Y, MulAction G ((FiniteEtale.fiber (x' ≫ f)).obj Y)]
    {S' : PointedCosetSystem x' G'} (L' : PointedCosetLimit x' G' S')
    {S₀ : PointedCosetSystem (x' ≫ f) G} (L₀ : PointedCosetLimit (x' ≫ f) G S₀) where
  hom : L'.cone.pt.left ⟶ L₀.cone.pt.left
  over : hom ≫ L₀.cone.pt.hom = L'.cone.pt.hom ≫ f
  point : L'.point ≫ hom = L₀.point

/-- Every pointed base morphism gives a unique pointed map between the given limits,
with the explicit fibre base-change formula and deck equivariance.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-limit-finite-splitting).

Proof (node steps 6--7). For each `N`, take the primed section with label
`tau_(Y_N)⁻¹(N)` and compose with the pullback projection. Naturality of the actual
`pullbackFiberIso` (lem-galois-pi1-functoriality) makes these a cone; their values at the
marked point are `y_N`. The limit property supplies the pointed comparison. Any other
pointed comparison gives, after pairing into each pullback cover, the same primed
section by marked-point uniqueness, hence has the same limit legs. The same argument
for an arbitrary finite cover gives the displayed section comparison. Intertwining
monodromy under `tau` and `fundamentalGroupMap_smul` gives deck equivariance after
composition with each limit leg; the limit property gives equality. -/
theorem exists_unique_pointedLimitComparison {X' : Scheme.{u}}
    [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace X'] [CompactSpace X'] [QuasiSeparatedSpace X']
    (f : X' ⟶ X) (x' : Spec (.of Ω) ⟶ X') (G' : ProfiniteGrp.{u})
    [∀ Y, MulAction G' ((FiniteEtale.fiber x').obj Y)]
    [∀ Y, MulAction G ((FiniteEtale.fiber (x' ≫ f)).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x') G']
    [IsFundamentalGroup (FiniteEtale.fiber (x' ≫ f)) G]
    {S' : PointedCosetSystem x' G'} (L' : PointedCosetLimit x' G' S')
    {S₀ : PointedCosetSystem (x' ≫ f) G} (L₀ : PointedCosetLimit (x' ≫ f) G S₀)
    (C' : PointedLimitSplitting L') (C₀ : PointedLimitSplitting L₀) :
    ∃ F : PointedLimitComparison f x' G' L' L₀,
      (∀ F' : PointedLimitComparison f x' G' L' L₀, F'.hom = F.hom) ∧
      (∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y),
        F.hom ≫ (C₀.sectionMap Y s).left =
          (C'.sectionMap ((FiniteEtale.pullback f).obj Y)
            ((FiniteEtale.pullbackFiberIso f x').inv.app Y s)).left ≫
              Limits.pullback.fst Y.obj.hom f) ∧
      (∀ h : G', (C'.deck h).hom.left ≫ F.hom =
        F.hom ≫ (C₀.deck (FiniteEtale.fundamentalGroupMap
          (FiniteEtale.pullbackFiberIso f x') G' G h)).hom.left) := by
  classical
  let := L'.connected
  let τ := FiniteEtale.pullbackFiberIso f x'
  let r (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y) := τ.inv.app Y s
  let q (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y) :=
    (C'.sectionMap ((FiniteEtale.pullback f).obj Y) (r Y s)).left ≫
      Limits.pullback.fst Y.obj.hom f
  have qo (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y) :
      q Y s ≫ Y.obj.hom = L'.cone.pt.hom ≫ f := by
    dsimp only [q]
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (C'.sectionMap _ (r Y s)))
  have qp (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y) :
      L'.point ≫ q Y s = s.left := by
    dsimp only [q]
    rw [← Category.assoc, C'.section_point]
    have ht := congrArg (fun z ↦ z.left) (ConcreteCategory.congr_hom (τ.inv_hom_id_app Y) s)
    exact ht
  have qn {Y Z : X.FiniteEtale} (b : Y ⟶ Z)
      (s : (FiniteEtale.fiber (x' ≫ f)).obj Y) :
      q Y s ≫ b.hom.left = q Z ((FiniteEtale.fiber (x' ≫ f)).map b s) := by
    apply finiteEtale_point_ext L'.point (L'.cone.pt.hom ≫ f) Z
    · rw [Category.assoc, FiniteEtale.hom_left_comp, qo]
    · exact qo _ _
    · rw [← Category.assoc, qp, qp, FiniteEtale.fiber_map_left]
  let c : Cone (S₀.covers ⋙ finiteEtaleOver X) :=
    { pt := Over.mk (L'.cone.pt.hom ≫ f)
      π :=
        { app N := Over.homMk (q (S₀.covers.obj N) (S₀.label N 1)) (qo _ _)
          naturality M N h := by
            apply Over.OverMorphism.ext
            change q (S₀.covers.obj N) (S₀.label N 1) =
              q (S₀.covers.obj M) (S₀.label M 1) ≫ (S₀.covers.map h).hom.left
            rw [qn]
            congr 1
            have e : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
            simpa only [QuotientGroup.mk_one, e] using
              (S₀.transition (leOfHom h) 1).symm } }
  let v := L₀.isLimit.lift c
  have vl (N : OpenNormalSubgroup G) :
      v.left ≫ (L₀.cone.π.app N).left = q (S₀.covers.obj N) (S₀.label N 1) :=
    congrArg (fun z ↦ z.left) (L₀.isLimit.fac c N)
  have vp : L'.point ≫ v.left = L₀.point := by
    apply pointedLimit_hom_ext L₀ (x' ≫ f)
    · rw [Category.assoc, Over.w v]
      change L'.point ≫ (L'.cone.pt.hom ≫ f) = x' ≫ f
      rw [← Category.assoc, L'.point_base]
    · exact L₀.point_base
    · intro N
      rw [Category.assoc, vl, qp, L₀.point_leg]
  let F : PointedLimitComparison f x' G' L' L₀ := ⟨v.left, Over.w v, vp⟩
  have cf (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y) :
      F.hom ≫ (C₀.sectionMap Y s).left = q Y s := by
    apply finiteEtale_point_ext L'.point (L'.cone.pt.hom ≫ f) Y
    · rw [Category.assoc, show (C₀.sectionMap Y s).left ≫ Y.obj.hom =
        L₀.cone.pt.hom from Over.w (C₀.sectionMap Y s), F.over]
    · exact qo Y s
    · rw [← Category.assoc, F.point, C₀.section_point, qp]
  have leg (N : OpenNormalSubgroup G) :
      (L₀.cone.π.app N).left =
        (C₀.sectionMap (S₀.covers.obj N) (S₀.label N 1)).left :=
    congrArg (fun z ↦ z.left)
      (C₀.section_unique _ _ (L₀.cone.π.app N) (L₀.point_leg N))
  refine ⟨F, ?_, cf, ?_⟩
  · intro F'
    exact pointedLimit_point_ext L₀ L'.point (L'.cone.pt.hom ≫ f)
      F'.hom F.hom F'.over F.over (F'.point.trans F.point.symm)
  · intro h
    apply pointedLimit_hom_ext L₀ (L'.cone.pt.hom ≫ f)
    · rw [Category.assoc, F.over, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w (C'.deck h).hom)
    · rw [Category.assoc, Over.w, F.over]
    · intro N
      rw [Category.assoc, leg, cf]
      dsimp only [q]
      rw [← Category.assoc, C'.section_deck]
      rw [← leg]
      rw [Category.assoc, C₀.deck_leg, cf]
      dsimp only [q]
      congr 3
      apply ((ConcreteCategory.isIso_iff_bijective (τ.hom.app (S₀.covers.obj N))).mp
        inferInstance).1
      rw [← FiniteEtale.fundamentalGroupMap_smul τ G' G]
      have hr (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y) :
          τ.hom.app Y (r Y s) = s := ConcreteCategory.congr_hom (τ.inv_hom_id_app Y) s
      rw [hr, hr]
      exact (S₀.label_smul N _ 1).symm.trans (by simp only [mul_one]; rfl)

/-- A pointed comparison over the identity is the identity.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-limit-finite-splitting).
Proof (node step 7): the identity map is pointed over the identity base morphism;
uniqueness of the pointed comparison makes every such comparison equal to it. -/
theorem pointedLimitComparison_id [ConnectedSpace X] [CompactSpace X]
    [QuasiSeparatedSpace X] [IsFundamentalGroup (FiniteEtale.fiber x) G]
    (b : L.cone.pt.left ⟶ L.cone.pt.left)
    (hb : b ≫ L.cone.pt.hom = L.cone.pt.hom) (hp : L.point ≫ b = L.point) :
    b = 𝟙 _ := by
  let := L.connected
  exact pointedLimit_point_ext L L.point L.cone.pt.hom b (𝟙 _) hb
    (by simp) (by simpa using hp)

/-- Pointed comparisons respect composition, including arbitrary (not necessarily
surjective) maps on fundamental groups.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-limit-finite-splitting).
Proof (node step 7): the composite comparison lies over the composite base morphism
and carries the marked point to the marked point. Uniqueness of the pointed comparison
therefore identifies it with the comparison over the composite. -/
theorem pointedLimitComparison_comp {X₁ X₂ X₃ : Scheme.{u}}
    [ConnectedSpace X₁] [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    [ConnectedSpace X₂] [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    [ConnectedSpace X₃] [CompactSpace X₃] [QuasiSeparatedSpace X₃]
    (x₁ : Spec (.of Ω) ⟶ X₁) (x₂ : Spec (.of Ω) ⟶ X₂) (x₃ : Spec (.of Ω) ⟶ X₃)
    (G₁ G₂ G₃ : ProfiniteGrp.{u})
    [∀ Y, MulAction G₁ ((FiniteEtale.fiber x₁).obj Y)]
    [∀ Y, MulAction G₂ ((FiniteEtale.fiber x₂).obj Y)]
    [∀ Y, MulAction G₃ ((FiniteEtale.fiber x₃).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x₁) G₁]
    [IsFundamentalGroup (FiniteEtale.fiber x₂) G₂]
    [IsFundamentalGroup (FiniteEtale.fiber x₃) G₃]
    {S₁ : PointedCosetSystem x₁ G₁} (L₁ : PointedCosetLimit x₁ G₁ S₁)
    {S₂ : PointedCosetSystem x₂ G₂} (L₂ : PointedCosetLimit x₂ G₂ S₂)
    {S₃ : PointedCosetSystem x₃ G₃} (L₃ : PointedCosetLimit x₃ G₃ S₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hf : x₁ ≫ f = x₂) (hg : x₂ ≫ g = x₃)
    (F : L₁.cone.pt.left ⟶ L₂.cone.pt.left)
    (H : L₂.cone.pt.left ⟶ L₃.cone.pt.left)
    (K : L₁.cone.pt.left ⟶ L₃.cone.pt.left)
    (hF : F ≫ L₂.cone.pt.hom = L₁.cone.pt.hom ≫ f) (pF : L₁.point ≫ F = L₂.point)
    (hH : H ≫ L₃.cone.pt.hom = L₂.cone.pt.hom ≫ g) (pH : L₂.point ≫ H = L₃.point)
    (hK : K ≫ L₃.cone.pt.hom = L₁.cone.pt.hom ≫ (f ≫ g))
    (pK : L₁.point ≫ K = L₃.point) : F ≫ H = K := by
  let := L₁.connected
  have _ := hf
  have _ := hg
  apply pointedLimit_point_ext L₃ L₁.point (L₁.cone.pt.hom ≫ (f ≫ g))
  · rw [Category.assoc, hH, ← Category.assoc, hF, Category.assoc]
  · exact hK
  · rw [← Category.assoc, pF, pH, pK]

end AlgebraicGeometry.Scheme
