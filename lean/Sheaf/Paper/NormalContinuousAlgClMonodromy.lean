/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.NormContinuousMonodromyData
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
import Sheaf.Paper.CompactTorsorAssociatedLisse
import Sheaf.AlgebraicGeometry.FundamentalGroup.NormalSchemeGaloisInertiaPresentation
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.FibreFunctorBasepointTransport
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Normal-scheme monodromy for full norm-topology coefficients

Source: Bhatt--Scholze, Section 7.4, Lemmas 7.4.7 and 7.4.10, pp. 70--71,
with the agent norm-topology strengthening and its nine-step proof in the DAG.
Remark 7.4.8 uses a different topology and is not used for the algebraic-closure case.
(blueprint: lem-sfb-normal-continuous-algcl-monodromy).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite IsUltrametricDist
open scoped TensorProduct CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private def restrictRep {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [Group H] [TopologicalSpace H] (q : G →ₜ* H) :
    NormContinuousRepresentations A H ⥤ NormContinuousRepresentations A G where
  obj V := ⟨Rep.of (V.obj.ρ.comp q.toMonoidHom), by
    obtain ⟨n, b, hb⟩ := V.property
    exact ⟨n, b, fun i j ↦ (hb i j).comp q.continuous⟩⟩
  map f := ObjectProperty.homMk (Rep.ofHom
    { toLinearMap := f.hom.hom.toLinearMap
      isIntertwining' := fun g ↦ f.hom.hom.isIntertwining' (q g) })
  map_id _ := rfl
  map_comp _ _ := rfl

private def descendRep {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [Group H] [TopologicalSpace H]
    (q : G →ₜ* H) (hq : Topology.IsQuotientMap q)
    (V : NormContinuousRepresentations A G)
    (hk : q.toMonoidHom.ker ≤ V.obj.ρ.asGroupHom.ker) :
    NormContinuousRepresentations A H :=
  let r := q.toMonoidHom.liftOfSurjective hq.surjective ⟨V.obj.ρ.asGroupHom, hk⟩
  ⟨Rep.of ((Units.coeHom _).comp r), by
    obtain ⟨n, b, hb⟩ := V.property
    refine ⟨n, b, fun i j ↦ hq.continuous_iff.mpr ?_⟩
    convert hb i j using 1
    funext g
    change b.repr ((q.toMonoidHom.liftOfSurjective hq.surjective
      ⟨V.obj.ρ.asGroupHom, hk⟩ (q g)).val (b j)) i = b.repr (V.obj.ρ g (b j)) i
    exact congrArg (fun z : (Module.End A V.obj.V)ˣ ↦ b.repr (z.val (b j)) i)
      (q.toMonoidHom.liftOfRightInverse_comp_apply (Function.surjInv hq.surjective)
        (Function.rightInverse_surjInv hq.surjective) ⟨V.obj.ρ.asGroupHom, hk⟩ g)⟩

private theorem descendRep_action {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [Group H] [TopologicalSpace H]
    (q : G →ₜ* H) (hq : Topology.IsQuotientMap q)
    (V : NormContinuousRepresentations A G)
    (hk : q.toMonoidHom.ker ≤ V.obj.ρ.asGroupHom.ker) (g : G) :
    (descendRep q hq V hk).obj.ρ (q g) = V.obj.ρ g := by
  change ↑(q.toMonoidHom.liftOfSurjective hq.surjective
    ⟨V.obj.ρ.asGroupHom, hk⟩ (q g)) = V.obj.ρ g
  exact congrArg Units.val
    (q.toMonoidHom.liftOfRightInverse_comp_apply (Function.surjInv hq.surjective)
      (Function.rightInverse_surjInv hq.surjective) ⟨V.obj.ρ.asGroupHom, hk⟩ g)

private def descendTrivialIso {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [Group H] [TopologicalSpace H]
    (q : G →ₜ* H) (hq : Topology.IsQuotientMap q)
    (V : NormContinuousRepresentations A G)
    (hk : q.toMonoidHom.ker ≤ V.obj.ρ.asGroupHom.ker)
    {M : Type (u + 1)} [AddCommGroup M] [Module A M]
    (i : V.obj ≅ Rep.trivial A G M) :
    (descendRep q hq V hk).obj ≅ Rep.trivial A H M := by
  refine Rep.mkIso (Representation.Equiv.mk
    (Representation.equivOfIso i).toLinearEquiv ?_)
  intro h
  obtain ⟨g, rfl⟩ := hq.surjective h
  change _ ∘ₗ (descendRep q hq V hk).obj.ρ (q g) = _
  rw [descendRep_action]
  exact i.hom.hom.isIntertwining' g

private def descendFunctor {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [Group H] [TopologicalSpace H]
    {C : Type*} [Category* C] (q : G →ₜ* H) (hq : Topology.IsQuotientMap q)
    (F : C ⥤ NormContinuousRepresentations A G)
    (hk : ∀ L, q.toMonoidHom.ker ≤ (F.obj L).obj.ρ.asGroupHom.ker) :
    C ⥤ NormContinuousRepresentations A H where
  obj L := descendRep q hq (F.obj L) (hk L)
  map {L M} f := ObjectProperty.homMk (Rep.ofHom
    { toLinearMap := (F.map f).hom.hom.toLinearMap
      isIntertwining' := fun h ↦ by
        obtain ⟨g, rfl⟩ := hq.surjective h
        change _ ∘ₗ (descendRep q hq (F.obj L) (hk L)).obj.ρ (q g) =
          (descendRep q hq (F.obj M) (hk M)).obj.ρ (q g) ∘ₗ _
        rw [descendRep_action, descendRep_action]
        exact (F.map f).hom.hom.isIntertwining' g })
  map_id L := by ext v; exact congrArg (fun f ↦ f.hom.hom v) (F.map_id L)
  map_comp f g := by ext v; exact congrArg (fun f ↦ f.hom.hom v) (F.map_comp f g)

private def descendFunctor_fullyFaithful {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [Group H] [TopologicalSpace H]
    {C : Type*} [Category* C] (q : G →ₜ* H) (hq : Topology.IsQuotientMap q)
    (F : C ⥤ NormContinuousRepresentations A G)
    (hk : ∀ L, q.toMonoidHom.ker ≤ (F.obj L).obj.ρ.asGroupHom.ker)
    (hF : F.FullyFaithful) : (descendFunctor q hq F hk).FullyFaithful where
  preimage {L M} f := hF.preimage (ObjectProperty.homMk (Rep.ofHom
    { toLinearMap := f.hom.hom.toLinearMap
      isIntertwining' := fun g ↦ by
        have h := f.hom.hom.isIntertwining' (q g)
        change _ ∘ₗ (descendRep q hq (F.obj L) (hk L)).obj.ρ (q g) =
          (descendRep q hq (F.obj M) (hk M)).obj.ρ (q g) ∘ₗ _ at h
        simpa only [descendRep_action] using h }))
  map_preimage {L M} f := by
    ext v
    let f' : F.obj L ⟶ F.obj M := ObjectProperty.homMk (Rep.ofHom
      { toLinearMap := f.hom.hom.toLinearMap
        isIntertwining' := fun g ↦ by
          have h := f.hom.hom.isIntertwining' (q g)
          change _ ∘ₗ (descendRep q hq (F.obj L) (hk L)).obj.ρ (q g) =
            (descendRep q hq (F.obj M) (hk M)).obj.ρ (q g) ∘ₗ _ at h
          simpa only [descendRep_action] using h })
    exact congrArg (fun f : F.obj L ⟶ F.obj M ↦ f.hom.hom.toLinearMap v)
      (hF.map_preimage f')
  preimage_map f := by
    apply hF.map_injective
    rw [hF.map_preimage]
    rfl

private theorem descendFunctor_additive {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G]
    {H : Type w} [Group H] [TopologicalSpace H]
    {C : Type*} [Category* C] [Preadditive C]
    (q : G →ₜ* H) (hq : Topology.IsQuotientMap q)
    (F : C ⥤ NormContinuousRepresentations A G) [F.Additive]
    (hk : ∀ L, q.toMonoidHom.ker ≤ (F.obj L).obj.ρ.asGroupHom.ker) :
    (descendFunctor q hq F hk).Additive where
  map_add {L M f g} := by
    ext v
    exact congrArg (fun f ↦ f.hom.hom v) (F.map_add (f := f) (g := g))

private def matrixRepresentation {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : NormContinuousRepresentations A G) (n : ℕ)
    (b : Module.Basis (Fin n) A V.obj.V)
    (hb : ∀ i j, Continuous (fun g : G ↦ b.repr (V.obj.ρ g (b j)) i)) :
    G →ₜ* Matrix.GeneralLinearGroup (Fin n) A where
  toMonoidHom := (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    V.obj.ρ.asGroupHom
  continuous_toFun := by
    let r : G →* Matrix.GeneralLinearGroup (Fin n) A :=
      (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp V.obj.ρ.asGroupHom
    change Continuous r
    apply Units.continuous_iff.mpr
    have hc : Continuous (fun g : G ↦ (r g).val) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      convert hb i j using 1
      funext g
      exact LinearMap.toMatrixAlgEquiv_apply b (V.obj.ρ g) i j
    refine ⟨hc, ?_⟩
    convert hc.comp continuous_inv using 1
    funext g
    exact congrArg Units.val (r.map_inv g).symm

private theorem matrixRepresentation_apply {A : Type u} [NormedField A]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : NormContinuousRepresentations A G) (n : ℕ)
    (b : Module.Basis (Fin n) A V.obj.V)
    (hb : ∀ i j, Continuous (fun g : G ↦ b.repr (V.obj.ρ g (b j)) i)) (g : G) :
    (matrixRepresentation V n b hb g : Matrix (Fin n) (Fin n) A) =
      LinearMap.toMatrix b b (V.obj.ρ g) := rfl

private def sectionLinearEquiv {X : Scheme.{u}} [IsIntegral X]
    {A : Type u} [NormedField A] {ks : Type u} [Field ks]
    [Algebra X.functionField ks] [IsSepClosure X.functionField ks]
    (F : NormalGenericLisse.FiberFunctor X A ks) (hF : F.IsNormalized)
    (L : NormContinuousLisse A X) :
    (F.functor.obj L).obj.V ≃ₗ[A] NormalGenericLisse.geometricSections X A ks L :=
  { F.sections L with map_smul' := hF.2.2.1 L }

private theorem generic_action_kernel
    (B : NormalTorsorBase.{u}) [IsIntegral B.X]
    (ks : Type u) [Field ks] [Algebra B.X.functionField ks]
    [IsSepClosure B.X.functionField ks] [Algebra ks B.Ω] [IsAlgClosure ks B.Ω]
    [Algebra B.X.functionField B.Ω] [IsScalarTower B.X.functionField ks B.Ω]
    (hx : B.x = Spec.map (CommRingCat.ofHom (algebraMap B.X.functionField B.Ω)) ≫
      NormalGenericLisse.genericMap B.X)
    (q : (ks ≃ₐ[B.X.functionField] ks) →* B.pi)
    (hq : ∀ (g : ks ≃ₐ[B.X.functionField] ks) (gbar : B.Ω ≃ₐ[B.X.functionField] B.Ω),
      (∀ a : ks, gbar (algebraMap ks B.Ω a) = algebraMap ks B.Ω (g a)) →
        q g = Scheme.FiniteEtale.galoisToFundamentalGroup
          (NormalGenericLisse.genericMap B.X) (eqToIso (congrArg Scheme.FiniteEtale.fiber hx.symm))
            B.pi gbar)
    (A : Type u) [NormedField A]
    (hA : ∀ x y : A, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (F : NormalGenericLisse.FiberFunctor B.X A ks) (hF : F.IsNormalized)
    (L : NormContinuousLisse A B.X) :
    q.ker ≤ (F.functor.obj L).obj.ρ.asGroupHom.ker := by
  obtain ⟨n, b, _⟩ := (F.functor.obj L).property
  obtain ⟨_, _, hN, hC, P, e, _, U, t, ht, eA, s, tbar, htbar,
    _, _, _, _, hkill, _⟩ :=
    CompletedFrameGeneric.completed_frame_generic_comparison B ks hx q hq A hA F hF n L b
  intro g hg
  apply Units.ext
  apply (LinearMap.toMatrix b b).injective
  change LinearMap.toMatrix b b ((F.functor.obj L).obj.ρ g) =
    LinearMap.toMatrix b b LinearMap.id
  rw [LinearMap.toMatrix_id]
  exact hkill g hg

set_option genSizeOfSpec false in
set_option genInjectivity false in
private structure SectionMonodromy (X : Scheme.{u}) [IsIntegral X]
    (A : Type u) [NormedField A] (ks : Type u) [Field ks]
    [Algebra X.functionField ks] [IsSepClosure X.functionField ks]
    (G : Type v) [Group G] [TopologicalSpace G]
    (q : (ks ≃ₐ[X.functionField] ks) →* G) where
  monodromy : NormContinuousMonodromy A X G
  sections (L : NormContinuousLisse A X) :
    (monodromy.equivalence.functor.obj L).obj.V ≃ₗ[A]
      NormalGenericLisse.geometricSections X A ks L
  map_sections : ∀ (L M : NormContinuousLisse A X) (f : L ⟶ M)
    (v : (monodromy.equivalence.functor.obj L).obj.V),
    sections M ((monodromy.equivalence.functor.map f).hom.hom v) =
      GenericLisseScalar.map X ks f (sections L v)
  action_sections : ∀ (L : NormContinuousLisse A X) (g : ks ≃ₐ[X.functionField] ks)
    (v : (monodromy.equivalence.functor.obj L).obj.V),
    sections L ((monodromy.equivalence.functor.obj L).obj.ρ (q g) v) =
      GenericLisseScalar.action X ks L g (sections L v)

private def isoOfBasisMatrices {A : Type u} [NormedField A]
    {G : Type v} [Group G] (V W : Rep.{u + 1} A G) (n : ℕ)
    (b : Module.Basis (Fin n) A V.V) (d : Module.Basis (Fin n) A W.V)
    (h : ∀ (g : G) (i j : Fin n),
      b.repr (V.ρ g (b j)) i = d.repr (W.ρ g (d j)) i) : V ≅ W := by
  let e := b.repr.trans d.repr.symm
  have he (v : V.V) : d.repr (e v) = b.repr v := by
    change d.repr (d.repr.symm (b.repr v)) = b.repr v
    exact d.repr.apply_symm_apply _
  have heb (j : Fin n) : e (b j) = d j := by
    apply d.repr.injective
    rw [he]
    ext i
    simp only [Module.Basis.repr_self_apply]
  exact Rep.mkIso (Representation.Equiv.mk e (fun g ↦ by
    apply b.ext
    intro j
    apply d.repr.injective
    ext i
    change d.repr (e (V.ρ g (b j))) i = d.repr (W.ρ g (e (b j))) i
    rw [he, heb]
    exact h g i j))

private theorem buildSectionMonodromy
    (B : NormalTorsorBase.{u}) [IsIntegral B.X]
    (ks : Type u) [Field ks] [Algebra B.X.functionField ks]
    [IsSepClosure B.X.functionField ks] [Algebra ks B.Ω] [IsAlgClosure ks B.Ω]
    [Algebra B.X.functionField B.Ω] [IsScalarTower B.X.functionField ks B.Ω]
    (hx : B.x = Spec.map (CommRingCat.ofHom (algebraMap B.X.functionField B.Ω)) ≫
      NormalGenericLisse.genericMap B.X)
    (q : (ks ≃ₐ[B.X.functionField] ks) →* B.pi)
    (hq : ∀ (g : ks ≃ₐ[B.X.functionField] ks) (gbar : B.Ω ≃ₐ[B.X.functionField] B.Ω),
      (∀ a : ks, gbar (algebraMap ks B.Ω a) = algebraMap ks B.Ω (g a)) →
        q g = Scheme.FiniteEtale.galoisToFundamentalGroup
          (NormalGenericLisse.genericMap B.X) (eqToIso (congrArg Scheme.FiniteEtale.fiber hx.symm))
            B.pi gbar)
    (hqc : Continuous q) (hqs : Function.Surjective q)
    {G : Type v} [Group G] [TopologicalSpace G] (c : B.pi ≃ₜ* G)
    (A : Type u) [NormedField A] [IsUltrametricDist A]
    (hX : NormalGenericLisse.Assertions B.X) :
    Nonempty (SectionMonodromy B.X A ks G (c.toMonoidHom.comp q)) := by
  classical
  let hA : ∀ a b : A, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := norm_add_le_max
  obtain ⟨F, hF, _, _, _, _, hunit⟩ := (hX.2 A).2.2.2.2 ks
  let qc : (ks ≃ₐ[B.X.functionField] ks) →ₜ* G :=
    ⟨c.toMonoidHom.comp q, c.continuous.comp hqc⟩
  have hquot : Topology.IsQuotientMap qc :=
    c.toHomeomorph.isQuotientMap.comp
      (Topology.IsQuotientMap.of_surjective_continuous hqs hqc)
  have hk (L : NormContinuousLisse A B.X) :
      qc.toMonoidHom.ker ≤ (F.functor.obj L).obj.ρ.asGroupHom.ker := by
    intro g hg
    apply generic_action_kernel B ks hx q hq A hA F hF L
    apply c.injective
    change c (q g) = c 1
    rw [map_one]
    exact hg
  let D := descendFunctor qc hquot F.functor hk
  let ff := descendFunctor_fullyFaithful qc hquot F.functor hk hF.1.some
  let := ff.full
  let := ff.faithful
  let := hF.2.1
  let : D.Additive := descendFunctor_additive qc hquot F.functor hk
  have hess : D.EssSurj := by
    refine ⟨fun V ↦ ?_⟩
    obtain ⟨n, b, hb⟩ := V.property
    let V' := (restrictRep (⟨c.toMonoidHom, c.continuous⟩ : B.pi →ₜ* G)).obj V
    have hb' (i j) : Continuous (fun γ : B.pi ↦ b.repr (V'.obj.ρ γ (b j)) i) :=
      (hb i j).comp c.continuous
    let r := matrixRepresentation V' n b hb'
    obtain ⟨H, hH, eH, rH, θ, hrH, hθ, P, p, hP, L, a, ha, bL, _, hbL⟩ :=
      (TorsorAssociatedModule.compact_torsor_associated_lisse B ks hx q hq A hA).2 n r
    let s := sectionLinearEquiv F hF L
    let bF := bL.map s.symm
    refine ⟨L, ⟨ObjectProperty.isoMk _
      (isoOfBasisMatrices (D.obj L).obj V.obj n bF b ?_)⟩⟩
    intro γ i j
    obtain ⟨g, rfl⟩ := hquot.surjective γ
    have hj := hF.2.2.2.1 L g (bF j)
    have hm := hbL g i j
    change bL.repr (GenericLisseScalar.action B.X ks L g (bL j)) i = _ at hm
    rw [matrixRepresentation_apply] at hm
    change bF.repr ((descendRep qc hquot (F.functor.obj L) (hk L)).obj.ρ
      (qc g) (bF j)) i = _
    rw [descendRep_action]
    change bL.repr (s ((F.functor.obj L).obj.ρ g (s.symm (bL j)))) i = _
    have hj' : s ((F.functor.obj L).obj.ρ g (s.symm (bL j))) =
        GenericLisseScalar.action B.X ks L g (bL j) := by
      change F.sections L ((F.functor.obj L).obj.ρ g (bF j)) = _
      rw [hj]
      change GenericLisseScalar.action B.X ks L g (s (s.symm (bL j))) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [hj']
    rw [LinearMap.toMatrix_apply] at hm
    change bL.repr (GenericLisseScalar.action B.X ks L g (bL j)) i =
      b.repr (V.obj.ρ (c (q g)) (b j)) i at hm
    exact hm
  let := hess
  let : D.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  let e := D.asEquivalence
  let : e.functor.Additive := inferInstanceAs D.Additive
  have hlinear : ∀ (V W : NormContinuousRepresentations A G) (f : V ⟶ W) (a : A),
      (e.inverse.map (a • f)).hom.hom =
        (e.inverse.map f).hom.hom ≫
          normContinuousScalar B.X a (e.inverse.obj W).obj := by
    intro V W f a
    obtain ⟨t, ht, hFt⟩ := hF.2.2.2.2.2 (e.inverse.obj V) (e.inverse.obj W)
      (e.inverse.map f) a
    have hDt : D.map t = a • D.map (e.inverse.map f) := by
      ext v
      exact congrArg (fun f ↦ f.hom.hom v) hFt
    have he : e.inverse.map (a • f) = t := by
      apply D.map_injective
      rw [hDt]
      change e.functor.map (e.inverse.map (a • f)) =
        a • e.functor.map (e.inverse.map f)
      simp only [Equivalence.fun_inv_map, Linear.comp_smul, Linear.smul_comp]
    rw [he]
    exact ht
  have hregular : ∃ h : IsLisseCoefficientModule (normContinuousRing A).X
      (Mod.regular (coefficientRing B.X (normContinuousRing A)).X),
      Nonempty ((D.obj ⟨_, h⟩).obj ≅ Rep.trivial A G (ULift.{u + 1} A)) := by
    obtain ⟨h, ⟨i⟩⟩ := hunit.1
    exact ⟨h, ⟨descendTrivialIso qc hquot (F.functor.obj ⟨_, h⟩) (hk ⟨_, h⟩) i⟩⟩
  refine ⟨{ monodromy := ⟨e, inferInstance, hlinear, hregular⟩
            sections := fun L ↦ sectionLinearEquiv F hF L
            map_sections := ?_
            action_sections := ?_ }⟩
  · exact hF.2.2.2.2.1
  · intro L g v
    change F.sections L ((descendRep qc hquot (F.functor.obj L) (hk L)).obj.ρ (qc g) v) = _
    rw [descendRep_action]
    exact hF.2.2.2.1 L g v

private theorem sectionScalarComparison
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (ks : Type u) [Field ks] [Algebra X.functionField ks]
    [IsSepClosure X.functionField ks]
    {G : Type v} [Group G] [TopologicalSpace G]
    (q : (ks ≃ₐ[X.functionField] ks) →* G) (hq : Function.Surjective q)
    {A K : Type u} [NormedField A] [NormedField K] [Algebra A K]
    (hA : IsNonarchimedean (norm : A → ℝ))
    (hK : IsNonarchimedean (norm : K → ℝ)) (hφ : Continuous (algebraMap A K))
    (eA : SectionMonodromy X A ks G q) (eK : SectionMonodromy X K ks G q) :
    Nonempty (NormContinuousScalarComparison X G hφ eA.monodromy eK.monodromy) := by
  classical
  obtain ⟨t, _, ht, hg, _⟩ := GenericLisseScalar.comparison X ks hnormal hA hK hφ
  let ext := GenericLisseScalar.extension X (algebraMap A K) hφ
  let comparison (L : NormContinuousLisse A X) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) (eA.sections L)).trans
      ((t L).trans (eK.sections (ext.obj L)).symm)
  refine ⟨{ extension := ext
            extensionIso := Iso.refl _
            comparison := comparison
            equivariant := ?_
            naturality := ?_ }⟩
  · intro L γ a v
    obtain ⟨g, rfl⟩ := hq γ
    apply (eK.sections (ext.obj L)).injective
    simpa only [comparison, ext, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      LinearEquiv.apply_symm_apply, eA.action_sections,
      eK.action_sections] using hg L g a (eA.sections L v)
  · intro L M f a v
    apply (eK.sections (ext.obj M)).injective
    simpa only [comparison, ext, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      LinearEquiv.apply_symm_apply, eA.map_sections,
      eK.map_sections] using ht L M f a (eA.sections L v)

/-- Simultaneous linear equivalences for the algebraic closure and every finite intermediate
field, compatible with ordinary internal extension along the actual continuous-map inclusion.
The norm on Ω extends the p-adic norm, and intermediate fields have their induced norm.
The finite-basis representation category includes rank zero and uses all continuous entries.

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10, pp. 70--71, and the norm-topology
strengthening recorded in this node (blueprint: lem-sfb-normal-continuous-algcl-monodromy).

Proof: (1) Noetherian normal components are finitely many disjoint clopen integral schemes;
connectedness and nonemptiness make X integral. Identify p_X^*C(-,K) with continuous functions,
using total disconnectedness of K. (2) The normal-generic section bijection extends every
matrix uniquely from the generic fibre; uniqueness and sheaf descent glue maps and inverses.
This proves full faithfulness of generic restriction and constancy of the free rank.
(3) Over a separable closure, evaluate the Cech descent matrix on G_k. The cocycle identity
is the representation law; maps are constant intertwining matrices. Coefficient extension
acts entrywise. (4) Complete K to F. Small congruence subgroups give GL_n(F) an open-subgroup
basis, and entrywise limits of Cauchy matrices and inverses prove two-sided completeness.
This includes n=0. (5) Extend L to F and apply complete-group torsor monodromy to its frame
torsor. Pointed generic pullback and the field clause identify its cocycle with the image of
the K-valued generic cocycle. (6) The generic Galois-to-etale-pi1 map is surjective. Injectivity
of K → F kills its kernel on the K-cocycle. A surjection of profinite groups is a quotient map,
so the factor has continuous entries; generic full faithfulness identifies all intertwiners.
(7) Conversely the compact image of a continuous representation has an open-subgroup basis;
its torsor glues free K-modules by its transition matrices. Effective sheaf descent glues
addition and action, and completion plus injectivity identifies its generic cocycle.
(8) Transport the fundamental group from the generic basepoint to the prescribed point by
one path for every coefficient field. Regular and finite-sum matrices are respectively 1
and block sums; empty matrices give rank zero. Matrix operations prove linearity.
(9) On each free chart scalar extension sends entries by E → Ω. The generic Cech comparison
is Ω ⊗_E V with g(a ⊗ v)=a ⊗ ρ(g)v. The same generic quotient and basepoint path give the
comparison here; its equality on every morphism matrix proves naturality. All continuous
Ω-valued functions are retained throughout. -/
theorem normal_continuous_algCl_monodromy (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [NormedField Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (hnorm : ∀ a : ℚ_[l], ‖algebraMap ℚ_[l] Ω a‖ = ‖a‖)
    (X : Scheme.{u}) [ConnectedSpace X] [IsNoetherian X] [X.IsSeparated]
    (hinvertible : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    {Ωx : Type u} [Field Ωx] [IsAlgClosed Ωx] (x : Spec (.of Ωx) ⟶ X) :
    ∃ eΩ : NormContinuousMonodromy Ω X (Aut (Scheme.flcFiber x)),
      ∀ E : IntermediateField ℚ_[l] Ω, FiniteDimensional ℚ_[l] E →
        ∃ eE : NormContinuousMonodromy E X (Aut (Scheme.flcFiber x)),
          ∃ hE : Continuous (algebraMap E Ω),
            Nonempty (NormContinuousScalarComparison X (Aut (Scheme.flcFiber x)) hE eE eΩ) := by
  classical
  have _ := hinvertible
  obtain ⟨hIntegral, hAssertions⟩ := normal_generic_lisse_cocycle X hnormal
  let := hIntegral
  let k := X.functionField
  let ks := SeparableClosure k
  let Ωbar := AlgebraicClosure k
  let : IsAlgClosure ks Ωbar :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := k) ks⟩
  let y : Spec (.of Ωbar) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ωbar)) ≫ NormalGenericLisse.genericMap X
  obtain ⟨π, hact, hπ⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup y
  let := hact
  let := hπ
  let B : NormalTorsorBase.{u} :=
    { X := X
      connected := inferInstance
      noetherian := inferInstance
      compact := inferInstance
      normal := hnormal
      Ω := Ωbar
      field := inferInstance
      closed := inferInstance
      x := y
      pi := π
      actions := hact
      fundamental := hπ }
  let Ωz (z : X) := AlgebraicClosure (X.residueField z)
  let sz (z : X) : Spec (.of (Ωz z)) ⟶ X :=
    (X.SpecToEquivOfField (Ωz z)).symm
      ⟨z, CommRingCat.ofHom (algebraMap (X.residueField z) (Ωz z))⟩
  have hsz (z : X) : (X.SpecToEquivOfField (Ωz z) (sz z)).1 = z := by
    simp only [sz, Equiv.apply_symm_apply]
  obtain ⟨_, _, _, q, hq, hqc, hqs, _⟩ :=
    Scheme.FiniteEtale.normalScheme_galois_inertia_presentation
      (Ω := ks) (Ωbar := Ωbar) (fun z ↦ (hnormal z).2) Ωz sz hsz π
  obtain ⟨_, _, cη, _⟩ := Scheme.FiniteEtale.exists_fiber_flc_equivalence y π
  obtain ⟨⟨t⟩, ht, _⟩ := Scheme.fibre_functor_basepoint_transport y x
  obtain ⟨ct, _, _⟩ := ht t
  let c := cη.trans ct
  have hΩ : IsUltrametricDist Ω :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      simpa only [map_natCast] using
        (hnorm (n : ℚ_[l])).le.trans (IsUltrametricDist.norm_natCast_le_one ℚ_[l] n)
  let := hΩ
  obtain ⟨eΩ⟩ := buildSectionMonodromy B ks rfl q hq hqc hqs c Ω (hAssertions hIntegral)
  refine ⟨eΩ.monodromy, ?_⟩
  intro E _hE
  let : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      change ‖((n : E) : Ω)‖ ≤ 1
      simpa only [SubringClass.coe_natCast] using
        (IsUltrametricDist.norm_natCast_le_one Ω n)
  obtain ⟨eE⟩ := buildSectionMonodromy B ks rfl q hq hqc hqs c E (hAssertions hIntegral)
  have hE : Continuous (algebraMap E Ω) := continuous_subtype_val
  refine ⟨eE.monodromy, hE, ?_⟩
  exact sectionScalarComparison hnormal ks (c.toMonoidHom.comp q)
    (c.surjective.comp hqs) isNonarchimedean_norm isNonarchimedean_norm hE eE eΩ

end AlgebraicGeometry.ProEtale
