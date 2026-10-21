/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Paper.AdicLisseModule
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.Order.Filter.Bases.Basic
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion

/-! # Normalized completion of compact adic continuous coefficients

Source: blueprint main-20261015, integral coefficient comparison, steps 3--4;
Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj Topology
namespace AlgebraicGeometry.ProEtale

private theorem quotient_locallyConstant
    (A : Type u) [CommRing A] [TopologicalSpace A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (n : ℕ) : IsLocallyConstant
      (Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1))) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact (hb x).mem_of_mem (i := n) trivial

private theorem residue_lift
    (A : Type u) [CommRing A] [TopologicalSpace A] [CompactSpace A] [T2Space A]
    (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (b : ∀ n : ℕ, A ⧸ Ideal.span ({p} : Set A) ^ (n + 1))
    (hcompat : ∀ n : ℕ,
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
        (b (n + 1)) = b n) :
    ∃! a : A, ∀ n : ℕ, Ideal.Quotient.mk
      (Ideal.span ({p} : Set A) ^ (n + 1)) a = b n := by
  let q (n : ℕ) := Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1))
  let S (n : ℕ) : Set A := {a | q n a = b n}
  have hclosed (n : ℕ) : IsClosed (S n) :=
    (quotient_locallyConstant A p hb n).isClosed_fiber _
  have hnon (n : ℕ) : (S n).Nonempty := Ideal.Quotient.mk_surjective (b n)
  have hstep (n : ℕ) : S (n + 1) ⊆ S n := by
    intro a ha
    exact (congrArg (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ha).trans (hcompat n)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnon (hclosed 0).isCompact hclosed
  have hqa (n : ℕ) : q n a = b n := Set.mem_iInter.mp ha n
  refine ⟨a, hqa, ?_⟩
  intro a' ha'
  apply pure_le_nhds_iff.mp
  intro V hV
  obtain ⟨n, _, hn⟩ := (hb a).mem_iff.mp hV
  exact hn ((ha' n).trans (hqa n).symm)

private theorem continuous_of_residues
    (A : Type u) [CommRing A] [TopologicalSpace A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    {X : Type v} [TopologicalSpace X] (f : X → A)
    (hf : ∀ n : ℕ, IsLocallyConstant (fun x ↦
      Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) (f x))) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, (hb (f x)).tendsto_right_iff]
  intro n _
  exact (hf n).eventually_eq x

private theorem continuous_division
    (A : Type u) [CommRing A] [IsDomain A] [TopologicalSpace A]
    [IsTopologicalRing A] [CompactSpace A] [T2Space A]
    (p : A) (hp : p ≠ 0) {X : Type v} [TopologicalSpace X] (f : C(X, A))
    (a : A) (n : ℕ)
    (h : ∀ x, Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) (f x) =
      Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) a) :
    ∃ g : C(X, A), ∀ x, f x = a + p ^ (n + 1) * g x := by
  classical
  have hm : Continuous (fun z : A ↦ p ^ (n + 1) * z) :=
    continuous_const.mul continuous_id
  have hi : Function.Injective (fun z : A ↦ p ^ (n + 1) * z) :=
    mul_right_injective₀ (pow_ne_zero _ hp)
  have he := hm.isClosedEmbedding hi
  have hd (x : X) : ∃ z : A, p ^ (n + 1) * z = f x - a := by
    have hx := Ideal.Quotient.eq.mp (h x)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, hz.symm⟩
  let g (x : X) : A := (hd x).choose
  have hg (x : X) : p ^ (n + 1) * g x = f x - a := (hd x).choose_spec
  have hgc : Continuous g := he.isEmbedding.isInducing.continuous_iff.mpr (by
    change Continuous (fun x ↦ p ^ (n + 1) * g x)
    have hc : Continuous (fun x : X ↦ f x - a) :=
      f.continuous.sub (continuous_const : Continuous (fun _ : X ↦ a))
    exact (show (fun x ↦ p ^ (n + 1) * g x) = (fun x ↦ f x - a) from
      funext hg) ▸ hc)
  refine ⟨⟨g, hgc⟩, ?_⟩
  intro x
  rw [show (⟨g, hgc⟩ : C(X, A)) x = g x from rfl, hg]
  exact (add_sub_cancel _ _).symm

private theorem continuousFiniteQuotientHom_ext
    (A : Type (u + 1)) [CommRing A] [IsDomain A] [TopologicalSpace A]
    [IsTopologicalRing A] [CompactSpace A] [T2Space A]
    (p : A) (hp : p ≠ 0)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) (n : ℕ) (B : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ ψ : Scheme.continuousCoefficientSheaf T A ⟶ B)
    (hscalar : ∀ (U : T.ProEtᵒᵖ) (a : A),
      φ.hom.app U (ContinuousMap.const U.unop.left a) =
        ψ.hom.app U (ContinuousMap.const U.unop.left a))
    (hkill : ∀ U : T.ProEtᵒᵖ,
      φ.hom.app U (ContinuousMap.const U.unop.left p) ^ (n + 1) = 0) : φ = ψ := by
  classical
  ext U f
  change C(U.unop.left, A) at f
  let q := Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1))
  have hlocal : IsLocallyConstant (fun x ↦ q (f x)) :=
    (quotient_locallyConstant A p hb n).comp_continuous f.continuous
  let O (x : U.unop.left) : U.unop.left.Opens :=
    ⟨{y | q (f y) = q (f x)}, hlocal.isOpen_fiber _⟩
  have hc : Presheaf.equalizerSieve (φ.hom.app U f) (ψ.hom.app U f) ∈
      Scheme.ProEt.topology T U.unop := by
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      let W := U.unop.ofOpenImmersion (O x).ι
      let j : W ⟶ U.unop := Scheme.ProEt.ofOpenImmersionHom U.unop (O x).ι
      let V := op W
      let f' : C(W.left, A) := f.comp (O x).ι.base.hom
      obtain ⟨g, hg⟩ := continuous_division A p hp f' (f x) n (fun y ↦ y.property)
      have heq : f' = ContinuousMap.const _ (f x) +
          ContinuousMap.const _ p ^ (n + 1) * g := by
        ext y
        exact hg y
      change B.obj.map j.op (φ.hom.app U f) = B.obj.map j.op (ψ.hom.app U f)
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      change φ.hom.app V f' = ψ.hom.app V f'
      rw [heq, map_add, map_add, map_mul, map_mul, map_pow, map_pow]
      rw [← hscalar V p, hkill V, zero_mul, zero_mul, add_zero, add_zero,
        hscalar V (f x)]
  exact B.isSeparated U.unop _ hc _ _ (fun _ _ h ↦ h)

private theorem totallyDisconnected_of_basis
    (A : Type u) [CommRing A] [TopologicalSpace A] [T2Space A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x})) :
    TotallyDisconnectedSpace A := by
  let Q (n : ℕ) := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)
  let : ∀ n, TopologicalSpace (Q n) := fun _ ↦ ⊥
  let : ∀ n, DiscreteTopology (Q n) := fun _ ↦ ⟨rfl⟩
  let f : A → ∀ n, Q n := fun x n ↦ Ideal.Quotient.mk _ x
  have hc : Continuous f := continuous_pi (fun n ↦
    (IsLocallyConstant.iff_continuous _).mp (quotient_locallyConstant A p hb n))
  have hi : Function.Injective f := by
    intro x y hxy
    apply pure_le_nhds_iff.mp
    intro V hV
    obtain ⟨n, _, hn⟩ := (hb y).mem_iff.mp hV
    exact hn (congrFun hxy n)
  exact ⟨isTotallyDisconnected_of_image hc.continuousOn hi
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem ulift_basis
    (A : Type u) [CommRing A] [TopologicalSpace A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (x : ULift.{u + 1} A) :
    (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) x}) := by
  let e : ULift.{u + 1} A ≃+* A := ULift.ringEquiv
  have hm (n : ℕ) : Ideal.span ({p} : Set A) ^ (n + 1) =
      Ideal.map e.toRingHom
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1)) := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl
  have hq (n : ℕ) (y : ULift.{u + 1} A) :
      Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) x ↔
      Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y.down =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x.down :=
    (Ideal.quotientEquiv _ _ e (hm n)).injective.eq_iff.symm
  rw [Topology.IsEmbedding.uliftDown.isInducing.nhds_eq_comap x]
  simpa only [Set.preimage_ofPred_eq, ← hq] using
    (hb x.down).comap (ULift.down : ULift.{u + 1} A → A)

private def quotientTower (A : Type (u + 1)) [CommRing A] (p : A) :
    ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    CommRingCat.of (A ⧸ Ideal.span ({p} : Set A) ^ (n + 1))) (fun n ↦
    CommRingCat.ofHom (Ideal.Quotient.factorPowSucc (Ideal.span ({p} : Set A)) (n + 1)))

private def continuousResidueCone (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) :
    Cone (quotientTower A p ⋙ Scheme.discreteContinuousCoefficientFunctor T) := by
  let Q (n : ℕ) := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)
  let : ∀ n, TopologicalSpace (Q n) := fun _ ↦ ⊥
  let : ∀ n, DiscreteTopology (Q n) := fun _ ↦ ⟨rfl⟩
  refine { pt := Scheme.continuousCoefficientSheaf T A, π := ?_ }
  exact NatTrans.ofOpSequence (fun n ↦ Scheme.continuousCoefficientMap
    (Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)))
    ((IsLocallyConstant.iff_continuous _).mp (quotient_locallyConstant A p hb n)) T)
    (by
      intro n
      simp only [Functor.const_obj_map, Functor.comp_map, quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      ext U f
      apply @ContinuousMap.ext U.unop.left (Q n) _ ⊥
      intro x
      rfl)

private def continuousResidueCone_isLimit (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [CompactSpace A] [T2Space A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) : IsLimit (continuousResidueCone A p hb T) := by
  classical
  let Q (n : ℕ) := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)
  let : ∀ n, TopologicalSpace (Q n) := fun _ ↦ ⊥
  let : ∀ n, DiscreteTopology (Q n) := fun _ ↦ ⟨rfl⟩
  apply isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro U
  apply Classical.choice
  apply Scheme.commRingForgetReflectsLimit
  apply Classical.choice
  apply (Types.isLimit_iff_bijective_sectionOfCone _).mpr
  constructor
  · intro f g hfg
    change C(U.unop.left, A) at f g
    apply ContinuousMap.ext
    intro x
    have hf (n : ℕ) : Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) (f x) =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) (g x) :=
      congrArg (fun s ↦ (s.val (op n) : C(U.unop.left, Q n)) x) hfg
    apply pure_le_nhds_iff.mp
    intro V hV
    obtain ⟨n, _, hn⟩ := (hb (g x)).mem_iff.mp hV
    exact hn (hf n)
  · intro s
    let t (n : ℕ) : C(U.unop.left, Q n) := s.val (op n)
    have ht (x : U.unop.left) : ∃! a : A, ∀ n, Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) a = t n x := by
      apply residue_lift A p hb (fun n ↦ t n x)
      intro n
      have hn := s.property (homOfLE (Nat.le_succ n)).op
      simp only [Functor.comp_map, quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ] at hn
      exact congrArg (fun f : C(U.unop.left, Q n) ↦ f x) hn
    let f (x : U.unop.left) : A := (ht x).exists.choose
    have hres (n : ℕ) (x : U.unop.left) : Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) (f x) = t n x :=
      (ht x).exists.choose_spec n
    have hf : Continuous f := by
      apply continuous_of_residues A p hb f
      intro n
      have h := (IsLocallyConstant.iff_continuous (t n)).mpr (t n).continuous
      exact (show (fun x ↦ Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) (f x)) = t n from funext (hres n)) ▸ h
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Subtype.ext
    funext n
    apply @ContinuousMap.ext U.unop.left (Q n.unop) _ ⊥
    intro x
    exact hres n.unop x

private def quotientTowerConstantIso (A : Type (u + 1)) [CommRing A] (p : A)
    (T : Scheme.{u}) :
    quotientTower A p ⋙ constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ≅
      Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A)) := by
  let η : quotientTower A p ⋙
      constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ⟶
      Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, quotientTower, Scheme.adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp])
  let : ∀ n, IsIso (η.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  let := NatIso.isIso_of_isIso_app η
  exact asIso η

private def continuousCompletionIso (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [CompactSpace A] [T2Space A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) : Scheme.continuousCoefficientSheaf T A ≅
      Scheme.adicLisseCompletedRing T (Ideal.span ({p} : Set A)) := by
  let e := Functor.isoWhiskerLeft (quotientTower A p)
    (Scheme.discreteContinuousCoefficientIso T)
  exact (continuousResidueCone_isLimit A p hb T).conePointsIsoOfNatIso
    (limit.isLimit (Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A))))
    (e.symm ≪≫ quotientTowerConstantIso A p T)

/-- A compact separated principal-adic domain is realized by its positive finite quotient
constant sheaves, uniquely with the prescribed constant scalars.

Source: blueprint main-20261015, integral coefficient comparison steps 3--4;
Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1)
(blueprint: lem-sfb-compact-adic-continuous-identification).

Proof: The quotient fibres are open by the given neighborhood basis. Each finite
quotient's continuous-function sheaf is canonically its constant sheaf, by gluing on
these open fibres, including the empty object. Compatible residues have a unique lift
in A: compactness intersects the nested nonempty closed cosets, and the Hausdorff
neighborhood basis separates points. The coordinate maps and their inverse are
continuous, since the same cosets are a neighborhood basis. Thus continuous A-valued
functions are the sectionwise inverse limit of finite continuous quotient functions.
The canonical continuous-ring realization identifies these functions with the actual
pulled-back coefficient ring and carries scalar constants to constant functions.
This constructs the normalized comparison as a ring isomorphism. For uniqueness,
fix n and restrict a continuous function to the open fibres of its n-th residue.
On such a fibre choose a scalar lift a. The difference from a is p^(n+1) times a
continuous function: multiplication by this nonzero power embeds compact A in the
Hausdorff space A, and its inverse onto its image is continuous. Every normalized
ring map to the n-th quotient therefore takes the original function to the residue
of a. Hence two candidates have equal finite projections locally, and thus globally.
Joint monicity of the limit projections gives equality of the ring isomorphisms. -/
theorem compact_adic_continuous_identification
    (A : Type u) [CommRing A] [IsDomain A] [TopologicalSpace A] [IsTopologicalRing A]
    [CompactSpace A] [T2Space A] (p : A) (hp : p ≠ 0)
    (hf : ∀ n : ℕ, Finite (A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)))
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) :
    (∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
    Scheme.adicLisseCompletedRing T
      (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))),
    ∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      ((limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)).hom.app U)
        ((e.hom.hom.app U)
          ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
            ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
                (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A)))).app U (ULift.up a)))) =
      (toSheafify (D := CommRingCat.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} A ⧸
            (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))))).app U
          (Ideal.Quotient.mk
            ((Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))
            (ULift.up a))) := by
  sorry

end AlgebraicGeometry.ProEtale
