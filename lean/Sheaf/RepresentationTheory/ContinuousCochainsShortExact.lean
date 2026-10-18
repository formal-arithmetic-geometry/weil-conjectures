/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker C1
-/
module

public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.RepresentationTheory.HomogeneousInhomogeneousContinuousCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Short exact sequences of continuous inhomogeneous cochains

Source: Stacks Project, Etale Cohomology, Tag 0DVG, section continuous-group-cohomology
(blueprint: lem-exc-continuous-cochains-short-exact).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

section Construction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type v} [Ring A]
  (M : DiscreteContinuousRep.{v, u, w} A G)
  [TopologicalSpace M.obj.V] [DiscreteTopology M.obj.V]
  [ContinuousConstSMul A M.obj.V]

omit [ContinuousConstSMul A M.obj.V] in
private theorem continuous_action : Continuous (fun p : G × M.obj.V ↦ M.obj.ρ p.1 p.2) := by
  let : MulAction G M.obj.V :=
    { smul := fun a x ↦ M.obj.ρ a x
      one_smul := by intro x; change M.obj.ρ 1 x = x; rw [map_one]; rfl
      mul_smul := by
        intro a b x
        change M.obj.ρ (a * b) x = M.obj.ρ a (M.obj.ρ b x)
        rw [map_mul]
        rfl }
  have : ContinuousSMul G M.obj.V :=
    continuousSMul_iff_stabilizer_isOpen.mpr M.property
  exact continuous_smul

private noncomputable def contD (n : ℕ) :
    C(Fin n → G, M.obj.V) →ₗ[A] C(Fin (n + 1) → G, M.obj.V) where
  toFun c := ⟨fun g ↦ M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) • c (Fin.contractNth k (· * ·) g), by
    apply Continuous.add
    · exact (continuous_action M).comp
        (show Continuous (fun g : Fin (n + 1) → G ↦ (g 0, c (fun i ↦ g i.succ))) from
          (continuous_apply 0).prodMk
            (c.continuous.comp (continuous_pi fun i : Fin n ↦ continuous_apply i.succ)))
    · apply continuous_finsetSum
      intro k _
      apply Continuous.zsmul
      apply c.continuous.comp
      apply continuous_pi
      intro i
      unfold Fin.contractNth
      split_ifs
      · exact continuous_apply _
      · exact (continuous_apply _).mul (continuous_apply _)
      · exact continuous_apply _⟩
  map_add' c d := by
    ext g
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' a c := by
    ext g
    simp [Finset.smul_sum, smul_comm a]

private theorem contD_sq [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (n : ℕ) (c : C(Fin n → G, M.obj.V)) :
    contD M (n + 1) (contD M n c) = 0 := by
  let ρ : ContRepresentation ℤ G (ULift.{u} M.obj.V) := .ofMonoidHom
    { toFun := fun g ↦
        { toFun := fun x ↦ ULift.up (M.obj.ρ g x.down)
          map_add' := by intro x y; apply ULift.ext; exact map_add _ _ _
          map_smul' := by intro a x; apply ULift.ext; exact map_zsmul _ _ _
          cont := continuous_of_discreteTopology }
      map_one' := by
        ext x
        change M.obj.ρ 1 x.down = x.down
        simp
      map_mul' := by
        intro g h
        ext x
        change M.obj.ρ (g * h) x.down = M.obj.ρ g (M.obj.ρ h x.down)
        rw [map_mul]
        rfl }
  let N : TopRep.{max u w} ℤ G := TopRep.of ρ
  have hN : ∀ x : N.V, IsOpen {g : G | N.ρ g x = x} := by
    intro x
    change IsOpen {g : G | ULift.up (M.obj.ρ g x.down) = ULift.up x.down}
    simpa only [ULift.up_inj] using M.property x.down
  obtain ⟨e, he⟩ := exists_homogeneousCochains_inhomogeneous_coordinates G N hN
  let lift (n : ℕ) (f : C(Fin n → G, M.obj.V)) :
      LocallyConstant (Fin n → G) N.V :=
    ⟨fun g ↦ ULift.up (f g), (IsLocallyConstant.iff_continuous _).mpr
      (continuous_uliftUp.comp f.continuous)⟩
  have hd : ∀ n x, e (n + 1) (((TopRep.homogeneousCochains N).d n (n + 1)).hom x) =
      lift (n + 1) (contD M n (⟨fun g ↦ (e n x g).down,
        continuous_uliftDown.comp (e n x).continuous⟩)) := by
    intro n x
    ext g
    rw [he]
    change M.obj.ρ (g 0) (((e n x) (fun i ↦ g i.succ)).down) +
      (∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
        e n x (Fin.contractNth k (· * ·) g)).down =
      M.obj.ρ (g 0) (((e n x) (fun i ↦ g i.succ)).down) +
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
          (e n x (Fin.contractNth k (· * ·) g)).down
    congr 1
    exact map_sum (ULift.moduleEquiv (R := ℤ) (M := M.obj.V)).toAddMonoidHom _ _
  let x := (e n).symm (lift n c)
  have hx : e n x = lift n c := (e n).apply_symm_apply _
  have hy : e (n + 1) (((TopRep.homogeneousCochains N).d n (n + 1)).hom x) =
      lift (n + 1) (contD M n c) := by
    rw [hd, hx]
    rfl
  have hz := hd (n + 1) (((TopRep.homogeneousCochains N).d n (n + 1)).hom x)
  rw [hy] at hz
  have hs := (TopRep.homogeneousCochains N).d_comp_d n (n + 1) (n + 2)
  have hh := congrArg (fun f ↦ f.hom x) hs
  change (((TopRep.homogeneousCochains N).d (n + 1) (n + 2)).hom
    (((TopRep.homogeneousCochains N).d n (n + 1)).hom x)) = 0 at hh
  rw [hh, map_zero] at hz
  ext g
  exact (congrArg (fun f : LocallyConstant (Fin (n + 2) → G) N.V ↦ (f g).down) hz).symm

private noncomputable abbrev contComplex
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A C(Fin n → G, M.obj.V))
    (fun n ↦ ModuleCat.ofHom (contD M n)) (fun n ↦ by
      ext c g
      exact DFunLike.congr_fun (contD_sq M n c) g)

variable {M} {N : DiscreteContinuousRep.{v, u, w} A G}
  [TopologicalSpace N.obj.V] [DiscreteTopology N.obj.V]
  [ContinuousConstSMul A N.obj.V]

private noncomputable def contPost (f : M ⟶ N) (n : ℕ) :
    C(Fin n → G, M.obj.V) →ₗ[A] C(Fin n → G, N.obj.V) where
  toFun c := ⟨fun g ↦ f.hom.hom (c g), continuous_of_discreteTopology.comp c.continuous⟩
  map_add' c d := by
    ext g
    change f.hom.hom (c g + d g) = f.hom.hom (c g) + f.hom.hom (d g)
    exact map_add _ _ _
  map_smul' a c := by
    ext g
    change f.hom.hom (a • c g) = a • f.hom.hom (c g)
    exact map_smul _ _ _

private noncomputable abbrev contMap
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (f : M ⟶ N) :
    contComplex M ⟶ contComplex N :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (contPost f n)) (fun n ↦ by
    ext c g
    simp only [contComplex, CochainComplex.of_d]
    change N.obj.ρ (g 0) (f.hom.hom (c (fun i ↦ g i.succ))) +
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
        f.hom.hom (c (Fin.contractNth k (· * ·) g)) =
      f.hom.hom (M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
          c (Fin.contractNth k (· * ·) g))
    simp [map_add, map_sum, map_zsmul, Rep.hom_comm_apply])

end Construction

set_option maxHeartbeats 800000 in
-- Elaborating the three dependent coefficient topologies and degreewise exactness needs
-- extra heartbeats; the complete file remains well within the single-file time limit.
/-- Continuous inhomogeneous cochains carry a short exact sequence of discrete continuous
representations to a short exact sequence of complexes. The equivalences `e` identify
complex terms with continuous maps, and specify both differentials and postcomposition maps.
The final term of the sum, indexed by `Fin.last n`, omits the last argument; the other terms
multiply adjacent arguments. At `n = 0` the formula is `g • m - m`.

Proof: (1) Underlying module exactness follows from `lem-exc-discrete-modules-abelian`.
Postcomposition with the injection is injective. A cochain in the kernel has a unique
pointwise preimage, continuous since inverse images of singletons are open. A set-theoretic
section of the surjection is continuous between discrete modules and lifts every cochain.
(2) Projections, adjacent multiplication and the action are continuous; the displayed
alternating sum therefore defines a continuous linear differential. Regard the underlying
integer representation, lifted to the common coefficient universe, as a topological
representation. The proved homogeneous-to-inhomogeneous coordinate theorem identifies
this formula with the homogeneous differential. Its square-zero relation transports through
the additive coordinates and the lift, including degree zero.
(3) Equivariant linear maps commute with each term of the differential, so postcomposition
gives cochain maps. Degreewise exactness gives short exactness directly for nonnegative
complexes by `lem-weil-pbc-cochain-complexes-degreewise-exact`.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential and paragraph
beginning "However, a short exact sequence of discrete G-modules"
(blueprint: lem-exc-continuous-cochains-short-exact). -/
theorem continuousCochains_shortExact
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (S : ShortComplex (DiscreteContinuousRep.{v, u, w} A G)) :
    S.ShortExact →
    let X : Fin 3 → DiscreteContinuousRep.{v, u, w} A G := ![S.X₁, S.X₂, S.X₃]
    letI : ∀ j : Fin 3, TopologicalSpace (X j).obj.V := fun _ ↦ ⊥
    letI : ∀ j : Fin 3, DiscreteTopology (X j).obj.V := fun _ ↦ ⟨rfl⟩
    letI : ∀ j : Fin 3, ContinuousConstSMul A (X j).obj.V :=
      fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
    ∃ (K : Fin 3 → CochainComplex (ModuleCat.{max u w} A) ℕ)
      (e : ∀ (j : Fin 3) (n : ℕ),
        (K j).X n ≃ₗ[A] C((Fin n → G), (X j).obj.V))
      (i : K 0 ⟶ K 1) (p : K 1 ⟶ K 2) (hip : i ≫ p = 0),
      (ShortComplex.mk i p hip).ShortExact ∧
      (∀ n : ℕ, Function.Injective (i.f n) ∧
        Set.range (i.f n) = {x | p.f n x = 0} ∧ Function.Surjective (p.f n)) ∧
      (∀ (n : ℕ) (f : (K 0).X n) (g : Fin n → G),
        e 1 n (i.f n f) g = S.f.hom.hom (e 0 n f g)) ∧
      (∀ (n : ℕ) (f : (K 1).X n) (g : Fin n → G),
        e 2 n (p.f n f) g = S.g.hom.hom (e 1 n f g)) ∧
      (∀ (j : Fin 3) (n : ℕ) (f : (K j).X n) (g : Fin (n + 1) → G),
        e j (n + 1) ((K j).d n (n + 1) f) g =
          (X j).obj.ρ (g 0) (e j n f (fun k ↦ g k.succ)) +
            ∑ k : Fin (n + 1),
              (-1 : ℤ) ^ (k.val + 1) • e j n f (Fin.contractNth k (· * ·) g)) := by
  classical
  intro hS
  dsimp only
  let X : Fin 3 → DiscreteContinuousRep.{v, u, w} A G := ![S.X₁, S.X₂, S.X₃]
  let : ∀ j : Fin 3, TopologicalSpace (X j).obj.V := fun _ ↦ ⊥
  let : ∀ j : Fin 3, DiscreteTopology (X j).obj.V := fun _ ↦ ⟨rfl⟩
  let : ∀ j : Fin 3, ContinuousConstSMul A (X j).obj.V :=
    fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let F : DiscreteContinuousRep.{v, u, w} A G ⥤ ModuleCat.{w} A :=
    ObjectProperty.ι (fun Y : Rep.{w} A G ↦
      ∀ m : Y.V, IsOpen {g : G | Y.ρ g m = m}) ⋙
      forget₂ (Rep.{w} A G) (ModuleCat.{w} A)
  obtain ⟨hab, hprops⟩ := discreteModules_abelian.{u, v, w} G A
  obtain ⟨hz, hprops⟩ := hprops
  have : F.PreservesZeroMorphisms := hz
  obtain ⟨_, hlim, hcol, _⟩ := hprops
  have : CategoryTheory.Limits.PreservesFiniteLimits F := hlim
  have : CategoryTheory.Limits.PreservesFiniteColimits F := hcol
  have hT := hS.map_of_exact F
  have hf : Function.Injective S.f.hom.hom := hT.moduleCat_injective_f
  have hg : Function.Surjective S.g.hom.hom := hT.moduleCat_surjective_g
  have hex : ∀ y : S.X₂.obj.V, S.g.hom.hom y = 0 →
      ∃ x : S.X₁.obj.V, S.f.hom.hom x = y :=
    (ShortComplex.moduleCat_exact_iff (S.map F)).1 hT.exact
  let K (j : Fin 3) := contComplex (X j)
  let i : K 0 ⟶ K 1 := contMap (M := X 0) (N := X 1) S.f
  let p : K 1 ⟶ K 2 := contMap (M := X 1) (N := X 2) S.g
  have hip : i ≫ p = 0 := by
    ext n c g
    change S.g.hom.hom (S.f.hom.hom (c g)) = 0
    exact congrArg (fun f ↦ f.hom.hom (c g)) S.zero
  have hdeg : ∀ n : ℕ, Function.Injective (i.f n) ∧
      Set.range (i.f n) = {x | p.f n x = 0} ∧ Function.Surjective (p.f n) := by
    intro n
    refine ⟨?_, ?_, ?_⟩
    · intro c d h
      ext g
      apply hf
      exact congrArg (fun f : C(Fin n → G, (X 1).obj.V) ↦ f g) h
    · ext c
      constructor
      · rintro ⟨b, rfl⟩
        change p.f n (i.f n b) = 0
        ext g
        change S.g.hom.hom (S.f.hom.hom (b g)) = 0
        exact congrArg (fun f ↦ f.hom.hom (b g)) S.zero
      · intro hc
        change p.f n c = 0 at hc
        let lift : (X 1).obj.V → (X 0).obj.V := fun y ↦
          if hy : S.g.hom.hom y = 0 then Classical.choose (hex y hy) else 0
        let b : C(Fin n → G, (X 0).obj.V) :=
          ⟨fun g ↦ lift (c g),
            (show Continuous lift from continuous_of_discreteTopology).comp c.continuous⟩
        refine ⟨b, ?_⟩
        ext g
        change S.f.hom.hom (lift (c g)) = c g
        have hy : S.g.hom.hom (c g) = 0 :=
          congrArg (fun f : C(Fin n → G, (X 2).obj.V) ↦ f g) hc
        simp only [lift, dif_pos hy]
        exact Classical.choose_spec (hex _ hy)
    · intro c
      let b : C(Fin n → G, (X 1).obj.V) :=
        ⟨fun g ↦ Function.surjInv hg (c g),
          (show Continuous (Function.surjInv hg : (X 2).obj.V → (X 1).obj.V) from
            continuous_of_discreteTopology).comp c.continuous⟩
      refine ⟨b, ?_⟩
      ext g
      exact Function.surjInv_eq hg (c g)
  refine ⟨K, fun _ _ ↦ LinearEquiv.refl A _, i, p, hip, ?_, ?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    apply ShortComplex.ShortExact.mk'
    · apply (ShortComplex.moduleCat_exact_iff _).2
      intro c hc
      have hm : c ∈ Set.range (i.f n) := (hdeg n).2.1.symm ▸ hc
      exact hm
    · exact (ModuleCat.mono_iff_injective _).2 (hdeg n).1
    · exact (ModuleCat.epi_iff_surjective _).2 (hdeg n).2.2
  · exact hdeg
  · intro n f g
    rfl
  · intro n f g
    rfl
  · intro j n f g
    simp only [K, contComplex, CochainComplex.of_d]
    rfl

end Rep
