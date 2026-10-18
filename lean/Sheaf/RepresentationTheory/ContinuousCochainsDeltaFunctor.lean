/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF workers E2, M2
-/
module

public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.RepresentationTheory.ContinuousCochainsShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Continuous cochain delta-functor

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology (blueprint: lem-exc-continuous-cochains-delta-functor).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

private theorem cochainFunctor_deltaFunctor
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (F : C ⥤ CochainComplex D ℕ) [F.Additive]
    (hF : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact) :
    ∃ T : CohomologicalDeltaFunctor C D,
      T.F = fun q ↦ F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q := by
  refine ⟨{
    F := fun q ↦ F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q
    additive := fun _ ↦ inferInstance
    delta := fun S hS n ↦ (hF S hS).δ n (n + 1) rfl
    mono_zero := ?_
    exact_middle := ?_
    exact_right := ?_
    exact_left := ?_
    naturality := ?_ }, rfl⟩
  · intro S hS
    have : Mono (F.map S.f) := (hF S hS).mono_f
    have : Mono ((F.map S.f).f 0) := inferInstance
    exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
      (F.map S.f) 0 (fun i ↦ by simp)
  · intro S hS n
    exact ⟨_, (hF S hS).homology_exact₂ n⟩
  · intro S hS n
    exact ⟨_, (hF S hS).homology_exact₃ n (n + 1) rfl⟩
  · intro S hS n
    exact ⟨_, (hF S hS).homology_exact₁ n (n + 1) rfl⟩
  · intro S T hS hT φ n
    exact HomologicalComplex.HomologySequence.δ_naturality
      (F.mapShortComplex.map φ) (hF S hS) (hF T hT) n (n + 1) rfl

private def cochainPostcompose
    {A : Type*} [Ring A] {X Y B : Type*}
    [AddCommGroup X] [Module A X] [TopologicalSpace X] [DiscreteTopology X]
    [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [ContinuousConstSMul A X] [ContinuousConstSMul A Y]
    [TopologicalSpace B] (f : X →ₗ[A] Y) : C(B, X) →ₗ[A] C(B, Y) where
  toFun c := ⟨fun g ↦ f (c g), continuous_of_discreteTopology.comp c.continuous⟩
  map_add' _ _ := ContinuousMap.ext (fun _ ↦ f.map_add _ _)
  map_smul' _ _ := ContinuousMap.ext (fun _ ↦ f.map_smul _ _)

private theorem continuousCochains_shortExact_compatible
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    [z : HasZeroMorphisms (DiscreteContinuousRep.{v, u, w} A G)]
    (S : @ShortComplex (DiscreteContinuousRep.{v, u, w} A G) inferInstance z) :
    @ShortComplex.ShortExact _ _ z S →
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
  have hz : z = ObjectProperty.instHasZeroMorphismsFullSubcategory
      (fun X : Rep.{w} A G ↦ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}) :=
    Subsingleton.elim _ _
  cases hz
  exact continuousCochains_shortExact G A S


private theorem continuousCochains_model
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    [Abelian (DiscreteContinuousRep.{v, u, max u w} A G)]
    (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    letI : TopologicalSpace M.obj.V := ⊥
    letI : DiscreteTopology M.obj.V := ⟨rfl⟩
    letI : ContinuousConstSMul A M.obj.V :=
      ⟨fun _ ↦ continuous_of_discreteTopology⟩
    ∃ (K : CochainComplex (ModuleCat.{max u w} A) ℕ)
      (e : ∀ n, K.X n ≃ₗ[A] C(Fin n → G, M.obj.V)),
      ∀ (n : ℕ) (x : K.X n) (g : Fin (n + 1) → G),
        e (n + 1) ((K.d n (n + 1)).hom x) g =
          M.obj.ρ (g 0) (e n x (fun k ↦ g k.succ)) +
            ∑ k : Fin (n + 1),
              (-1 : ℤ) ^ (k.val + 1) • e n x (Fin.contractNth k (· * ·) g) := by
  let : Zero (DiscreteContinuousRep.{v, u, max u w} A G) := HasZeroObject.zero' _
  let S : ShortComplex (DiscreteContinuousRep.{v, u, max u w} A G) :=
    ShortComplex.mk (𝟙 M) (0 : M ⟶ 0) (by simp)
  have : Epi S.g := (isZero_zero _).epi S.g
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_epi rfl).2 (inferInstance : Epi (𝟙 M)) }
  obtain ⟨K, e, i, p, hip, _, _, _, _, hd⟩ := continuousCochains_shortExact G A S hS
  exact ⟨K 0, e 0, hd 0⟩

/-- Continuous inhomogeneous cochains form a cohomological delta-functor.

Proof: Apply `continuousCochains_shortExact` to the split sequence M --id--> M --> 0
for each coefficient object. Its first complex has the required terms and differential.
Conjugate continuous postcomposition by the term equivalences to define coefficient maps;
equivariance and linearity prove that these commute with differentials. The equivalences
prove functoriality pointwise. The underlying-module functor preserves finite limits and
zero maps, hence is additive; its map-add identity proves additivity of the cochain functor.
For a short exact coefficient sequence, apply `continuousCochains_shortExact` again and
transport its degreewise short exact sequences along the term equivalences. Degreewise
short exactness gives short exactness of complexes. The homology long exact sequence and
its naturality supply the delta-functor axioms; degree zero has no incoming differential,
so its homology map is monic whenever the degree-zero cochain map is monic.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology, paragraph on short exact discrete coefficients.
(blueprint: lem-exc-continuous-cochains-delta-functor). -/
theorem continuousCochains_deltaFunctor
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
    letI := h
    letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
    letI : Preadditive (ModuleCat.{max u w} A) :=
      (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
    letI := (Classical.choose_spec
      (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
      fun _ ↦ ⊥
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
      fun _ ↦ ⟨rfl⟩
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
        ContinuousConstSMul A M.obj.V :=
      fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
    ∃ F : DiscreteContinuousRep.{v, u, max u w} A G ⥤
        CochainComplex (ModuleCat.{max u w} A) ℕ,
      ∃ e : ∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ),
        (F.obj M).X n ≃ₗ[A] C(Fin n → G, M.obj.V),
        (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
          (n : ℕ) (x : (F.obj M).X n) (g : Fin n → G),
          e N n (((F.map f).f n).hom x) g = f.hom.hom (e M n x g)) ∧
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
          (x : (F.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((F.obj M).d n (n + 1)).hom x) g =
            M.obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) ∧
        ∃ T : CohomologicalDeltaFunctor
            (DiscreteContinuousRep.{v, u, max u w} A G) (ModuleCat.{max u w} A),
          T.F = (fun q ↦ F ⋙ HomologicalComplex.homologyFunctor
            (ModuleCat.{max u w} A) (ComplexShape.up ℕ) q) := by
  classical
  dsimp only
  let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
  let := h
  let : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
  let : Preadditive (ModuleCat.{max u w} A) :=
    (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
  let := (Classical.choose_spec
    (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
  let : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
    fun _ ↦ ⊥
  let : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
    fun _ ↦ ⟨rfl⟩
  let : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
      ContinuousConstSMul A M.obj.V := fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  choose K e hd using (continuousCochains_model.{u, v, w} G A)
  let t {M N : DiscreteContinuousRep.{v, u, max u w} A G} (f : M ⟶ N) (n : ℕ) :
      (K M).X n ⟶ (K N).X n :=
    ModuleCat.ofHom ((e N n).symm.toLinearMap.comp
      ((cochainPostcompose (B := Fin n → G) f.hom.hom.toLinearMap).comp (e M n).toLinearMap))
  have ht {M N : DiscreteContinuousRep.{v, u, max u w} A G} (f : M ⟶ N)
      (n : ℕ) (x : (K M).X n) (g : Fin n → G) :
      e N n ((t f n).hom x) g = f.hom.hom (e M n x g) := by
    simp [t, cochainPostcompose]
  have tc {M N : DiscreteContinuousRep.{v, u, max u w} A G} (f : M ⟶ N)
      (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
      t f i ≫ (K N).d i j = (K M).d i j ≫ t f j := by
    obtain rfl : i + 1 = j := hij
    ext x
    apply (e N (i + 1)).injective
    ext g
    change e N (i + 1) (((K N).d i (i + 1)).hom ((t f i).hom x)) g =
      e N (i + 1) ((t f (i + 1)).hom (((K M).d i (i + 1)).hom x)) g
    simp only [hd, ht, map_add, map_sum, map_zsmul, Rep.hom_comm_apply]
  let F : DiscreteContinuousRep.{v, u, max u w} A G ⥤
      CochainComplex (ModuleCat.{max u w} A) ℕ :=
    { obj := K
      map := fun f ↦ { f := t f, comm' := tc f }
      map_id := by
        intro M
        ext n x
        apply (e M n).injective
        ext g
        change e M n ((t (𝟙 M) n).hom x) g = e M n x g
        rw [ht]
        rfl
      map_comp := by
        intro M N P f g
        ext n x
        apply (e P n).injective
        ext z
        change e P n ((t (f ≫ g) n).hom x) z =
          e P n ((t g n).hom ((t f n).hom x)) z
        simp only [ht]
        rfl }
  let U : DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A :=
    ObjectProperty.ι (fun X : Rep.{max u w} A G ↦
      ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}) ⋙
      forget₂ (Rep.{max u w} A G) (ModuleCat.{max u w} A)
  obtain ⟨hU, _, hlim, _, _⟩ :=
    Classical.choose_spec (discreteModules_abelian.{u, v, max u w} G A)
  have : U.PreservesZeroMorphisms := hU
  have : PreservesFiniteLimits U := hlim
  have : U.Additive := U.additive_of_preserves_binary_products
  have hadd {M N : DiscreteContinuousRep.{v, u, max u w} A G}
      (f g : M ⟶ N) (x : M.obj.V) :
      (f + g).hom.hom x = f.hom.hom x + g.hom.hom x := by
    exact congrArg (fun k : U.obj M ⟶ U.obj N ↦ k.hom x) (U.map_add (f := f) (g := g))
  have : F.Additive :=
    { map_add := by
        intro M N f g
        ext n x
        apply (e N n).injective
        ext z
        change e N n ((t (f + g) n).hom x) z =
          e N n ((t f n).hom x + (t g n).hom x) z
        simp only [map_add, ContinuousMap.add_apply, ht]
        exact hadd f g (e M n x z) }
  refine ⟨F, e, ?_, ?_, ?_⟩
  · exact fun M N f n x g ↦ ht f n x g
  · exact hd
  · apply cochainFunctor_deltaFunctor F
    intro S hS
    let : HasZeroMorphisms (DiscreteContinuousRep.{v, u, max u w} A G) :=
      Preadditive.preadditiveHasZeroMorphisms
    obtain ⟨L, eL, i, p, hip, hL, _, hi, hp, _⟩ :=
      continuousCochains_shortExact_compatible G A
        (z := Preadditive.preadditiveHasZeroMorphisms) S hS
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let X : Fin 3 → DiscreteContinuousRep.{v, u, max u w} A G := ![S.X₁, S.X₂, S.X₃]
    let E (j : Fin 3) : (L j).X n ≅ (K (X j)).X n :=
      ((eL j n).trans (e (X j) n).symm).toModuleIso
    have hE (j : Fin 3) (x : (L j).X n) (g : Fin n → G) :
        e (X j) n ((E j).hom.hom x) g = eL j n x g := by
      change e (X j) n ((e (X j) n).symm (eL j n x)) g = eL j n x g
      exact congrArg (fun c : C(Fin n → G, (X j).obj.V) ↦ c g)
        ((e (X j) n).apply_symm_apply (eL j n x))
    have hLn := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hL n
    apply ShortComplex.shortExact_of_iso (S₁ := (ShortComplex.mk i p hip).map
      (HomologicalComplex.eval (ModuleCat.{max u w} A) (ComplexShape.up ℕ) n)) _ hLn
    refine ShortComplex.isoMk (E 0) (E 1) (E 2) ?_ ?_
    · change (E 0).hom ≫ t S.f n = i.f n ≫ (E 1).hom
      ext x
      apply (e S.X₂ n).injective
      ext g
      change e S.X₂ n ((t S.f n).hom ((E 0).hom.hom x)) g =
        e S.X₂ n ((E 1).hom.hom ((i.f n).hom x)) g
      rw [ht]
      exact (congrArg (fun y ↦ S.f.hom.hom y) (hE 0 x g)).trans
        ((hi n x g).symm.trans (hE 1 ((i.f n).hom x) g).symm)
    · change (E 1).hom ≫ t S.g n = p.f n ≫ (E 2).hom
      ext x
      apply (e S.X₃ n).injective
      ext g
      change e S.X₃ n ((t S.g n).hom ((E 1).hom.hom x)) g =
        e S.X₃ n ((E 2).hom.hom ((p.f n).hom x)) g
      rw [ht]
      exact (congrArg (fun y ↦ S.g.hom.hom y) (hE 1 x g)).trans
        ((hp n x g).symm.trans (hE 2 ((p.f n).hom x) g).symm)

end Rep
