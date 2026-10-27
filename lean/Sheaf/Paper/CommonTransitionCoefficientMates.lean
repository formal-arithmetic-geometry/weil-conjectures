/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Common-stage transition comparisons and their counit mates

Source: blueprint, exceptional inverse image, extracted common-stage construction and
refinement-compatible adjunction argument, old steps 6 and 7
(blueprint: lem-sf-common-transition-coefficient-mates).

The categories are the literal finite-coefficient pair categories. The representative
normalization is expanded using the two factors of delta and their inverses.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory

namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients

private theorem pairFunctor_transition
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {S' : StageSystem D} (H : S.Morphism S')
    {i j : I} (h : i ≤ j) (K : C i) :
    H.functor.map ((S.transIso h).hom.app K) =
      (S'.ι j).map ((H.β h).inv.app K) ≫
        (S'.transIso h).hom.app ((H.Φ i).obj K) := by
  rw [StageSystem.transIso_hom_app_eq, H.functor_map_mkHom,
    StageSystem.ι_map_eq le_rfl, StageSystem.transIso_hom_app_eq,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  change (H.β le_rfl).hom.app ((S.T h).obj K) ≫
      (H.Φ j).map ((S.assoc h le_rfl).hom.app K) ≫ (H.β h).inv.app K =
    (S'.T le_rfl).map ((H.β h).inv.app K) ≫
      (S'.assoc h le_rfl).hom.app ((H.Φ i).obj K)
  rw [← cancel_epi ((S'.T le_rfl).map ((H.β h).hom.app K))]
  rw [reassoc_of% (H.coh h le_rfl K)]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  change (S'.assoc h le_rfl).hom.app ((H.Φ i).obj K) ≫ 𝟙 _ =
    (S'.T le_rfl).map (𝟙 ((S'.T h).obj ((H.Φ i).obj K))) ≫
      (S'.assoc h le_rfl).hom.app ((H.Φ i).obj K)
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- The actual scalar unitor on the published normalized stage transition.
Source: blueprint exceptional inverse image, common-stage identity representative
(blueprint: lem-sf-common-transition-coefficient-mates).
This is equality transport of the existing scalar unitor, retaining all its components. -/
noncomputable def sfCommonTransitionScalarUnit
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : AlgebraicGeometry.Scheme.{u}) (i : Padic.FiniteCoefficientFields l Ω) :
    stageTransition l Ω X i i le_rfl ≅ 𝟭 (Stage l Ω X i) :=
  eqToIso ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 i i le_rfl) ≪≫
    unitor l Ω X i

/-- Representative-normalized common comparisons commute with scalar transitions,
and the counit-normalized right comparisons obey the same transition equation.
Source: blueprint exceptional inverse image, extracted common-stage construction and
refinement-compatible adjunction, old steps 6 and 7
(blueprint: lem-sf-common-transition-coefficient-mates).

Proof:
1. The canonical identity transition tau_jj is the inclusion of the actual scalar
unitor. The rational identity equation therefore identifies delta_jj,A with the
inclusion of F_j applied to the inverse unitor at A. The canonical inverse transition
from (i,K) to (j,T_ij K) has precisely this stage-j unitor representative.
2. Apply the representative normalization to this inverse transition. Cancel the
middle inverse delta_jj with its just computed representative. Substitute the two
factors of delta_ij and compose with q_i and tau_ij. This gives the first equation.
3. For L, write A for the left side of the second equation, B for its right side,
and Q for the first equation's left side evaluated at G_i L. Transpose A by the
common adjunction and precompose by Q. Naturality of q_j at b_ji and the common
and finite counit normalizations give I_j T_ij(epsilon_i,L).
4. Rewrite Q using step 2. Transpose B; counit naturality at the inverse transition,
cancellation of inverse transitions, the common counit normalization at i, and
naturality of tau^Y at epsilon_i,L give the very same I_j T_ij(epsilon_i,L).
5. Cancel the isomorphism Q. The counit-transpose bijection of
CategoryTheory.mateEquiv (def-weil-pbc-adjunction-mate) then gives A = B.
All steps retain actual unitors for i = j, and use neither faithfulness of an
inclusion nor any Karoubi completion. -/
theorem sfCommonTransitionCoefficientMates
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X Y : AlgebraicGeometry.Scheme.{u})
    (F : ∀ i : Padic.FiniteCoefficientFields l Ω, Stage l Ω X i ⥤ Stage l Ω Y i)
    (G : ∀ i : Padic.FiniteCoefficientFields l Ω, Stage l Ω Y i ⥤ Stage l Ω X i)
    (adj : ∀ i, F i ⊣ G i)
    (FΩ : Pair l Ω X ⥤ Pair l Ω Y) (GΩ : Pair l Ω Y ⥤ Pair l Ω X)
    (adjΩ : FΩ ⊣ GΩ)
    (q : ∀ (i j : Padic.FiniteCoefficientFields l Ω) (h : i ≤ j),
      F i ⋙ stageTransition l Ω Y i j h ≅ stageTransition l Ω X i j h ⋙ F j)
    (b : ∀ (i j : Padic.FiniteCoefficientFields l Ω) (h : i ≤ j),
      G i ⋙ stageTransition l Ω X i j h ≅ stageTransition l Ω Y i j h ⋙ G j)
    (qΩ : ∀ i, F i ⋙ inclusion (l := l) (Ω := Ω) (Y := Y) i ≅
      inclusion (l := l) (Ω := Ω) (Y := X) i ⋙ FΩ)
    (bΩ : ∀ i, G i ⋙ inclusion (l := l) (Ω := Ω) (Y := X) i ≅
      inclusion (l := l) (Ω := Ω) (Y := Y) i ⋙ GΩ)
    (finite_counit : ∀ (i j : Padic.FiniteCoefficientFields l Ω) (h : i ≤ j)
      (L : Stage l Ω Y i),
      (q i j h).hom.app ((G i).obj L) ≫ (F j).map ((b i j h).hom.app L) ≫
          (adj j).counit.app ((stageTransition l Ω Y i j h).obj L) =
        (stageTransition l Ω Y i j h).map ((adj i).counit.app L))
    (common_counit : ∀ (i : Padic.FiniteCoefficientFields l Ω) (L : Stage l Ω Y i),
      (qΩ i).hom.app ((G i).obj L) ≫ FΩ.map ((bΩ i).hom.app L) ≫
          adjΩ.counit.app ((inclusion i).obj L) =
        (inclusion i).map ((adj i).counit.app L))
    (scalar_assoc : ∀ (i j m : Padic.FiniteCoefficientFields l Ω)
      (h : i ≤ j) (k : j ≤ m) (K : Stage l Ω X i),
      (stageTransition l Ω Y j m k).map ((q i j h).hom.app K) ≫
          (q j m k).hom.app ((stageTransition l Ω X i j h).obj K) ≫
          (F m).map (((stageSystem l Ω X).assoc h k).hom.app K) =
        ((stageSystem l Ω Y).assoc h k).hom.app ((F i).obj K) ≫
          (q i m (h.trans k)).hom.app K)
    (scalar_unit : ∀ (i : Padic.FiniteCoefficientFields l Ω) (K : Stage l Ω X i),
      (q i i le_rfl).hom.app K ≫
          (F i).map ((sfCommonTransitionScalarUnit l Ω X i).hom.app K) =
        (sfCommonTransitionScalarUnit l Ω Y i).hom.app ((F i).obj K))
    (representative_action : ∀ (i j m : Padic.FiniteCoefficientFields l Ω)
      (hi : i ≤ m) (hj : j ≤ m) (K : Stage l Ω X i) (L : Stage l Ω X j)
      (v : (stageTransition l Ω X i m hi).obj K ⟶
        (stageTransition l Ω X j m hj).obj L),
      FΩ.map (ofHom ((inclusion i).obj K) ((inclusion j).obj L) m hi hj v) =
        (qΩ i).inv.app K ≫
          ((stageSystem l Ω Y).transIso hi).inv.app ((F i).obj K) ≫
          (inclusion m).map ((q i m hi).hom.app K) ≫
          (inclusion m).map ((F m).map v) ≫
          (inclusion m).map ((q j m hj).inv.app L) ≫
          ((stageSystem l Ω Y).transIso hj).hom.app ((F j).obj L) ≫
          (qΩ j).hom.app L) :
    (∀ (i j : Padic.FiniteCoefficientFields l Ω) (h : i ≤ j) (K : Stage l Ω X i),
      (inclusion j).map ((q i j h).hom.app K) ≫
          (qΩ j).hom.app ((stageTransition l Ω X i j h).obj K) =
        ((stageSystem l Ω Y).transIso h).hom.app ((F i).obj K) ≫
          (qΩ i).hom.app K ≫ FΩ.map (((stageSystem l Ω X).transIso h).inv.app K)) ∧
    (∀ (i j : Padic.FiniteCoefficientFields l Ω) (h : i ≤ j) (L : Stage l Ω Y i),
      (inclusion j).map ((b i j h).hom.app L) ≫
          (bΩ j).hom.app ((stageTransition l Ω Y i j h).obj L) =
        ((stageSystem l Ω X).transIso h).hom.app ((G i).obj L) ≫
          (bΩ i).hom.app L ≫ GΩ.map (((stageSystem l Ω Y).transIso h).inv.app L)) := by
  have _ := scalar_unit
  let H : (stageSystem l Ω X).Morphism (stageSystem l Ω Y) :=
    { Φ := F
      β := fun {i j} h ↦ q i j h
      coh := fun {i j m} h k K ↦ scalar_assoc i j m h k K }
  have hmap (i j m : Padic.FiniteCoefficientFields l Ω) (hi : i ≤ m) (hj : j ≤ m)
      (K : Stage l Ω X i) (L : Stage l Ω X j)
      (v : (stageTransition l Ω X i m hi).obj K ⟶
        (stageTransition l Ω X j m hj).obj L) :
      FΩ.map (ofHom ((inclusion i).obj K) ((inclusion j).obj L) m hi hj v) =
        (qΩ i).inv.app K ≫
          H.functor.map (ofHom ((inclusion i).obj K) ((inclusion j).obj L) m hi hj v) ≫
          (qΩ j).hom.app L := by
    rw [representative_action]
    rw [H.functor_map_mkHom, StageSystem.mkHom_eq_isoToStage]
    simp only [H, StageSystem.Morphism.mapAt, Functor.map_comp, Category.assoc]
    rfl
  have ht (i j : Padic.FiniteCoefficientFields l Ω) (h : i ≤ j)
      (K : Stage l Ω X i) :
      FΩ.map (((stageSystem l Ω X).transIso h).hom.app K) =
        (qΩ j).inv.app ((stageTransition l Ω X i j h).obj K) ≫
          (inclusion j).map ((q i j h).inv.app K) ≫
          ((stageSystem l Ω Y).transIso h).hom.app ((F i).obj K) ≫
          (qΩ i).hom.app K := by
    have e := hmap j i j le_rfl h ((stageTransition l Ω X i j h).obj K) K
      (((stageSystem l Ω X).assoc h le_rfl).hom.app K)
    change FΩ.map (((stageSystem l Ω X).transIso h).hom.app K) =
      (qΩ j).inv.app ((stageTransition l Ω X i j h).obj K) ≫
        H.functor.map (((stageSystem l Ω X).transIso h).hom.app K) ≫
        (qΩ i).hom.app K at e
    rw [pairFunctor_transition] at e
    simpa only [H, Category.assoc] using e
  have left (i j : Padic.FiniteCoefficientFields l Ω) (h : i ≤ j)
      (K : Stage l Ω X i) :
      (inclusion j).map ((q i j h).hom.app K) ≫
          (qΩ j).hom.app ((stageTransition l Ω X i j h).obj K) =
        ((stageSystem l Ω Y).transIso h).hom.app ((F i).obj K) ≫
          (qΩ i).hom.app K ≫ FΩ.map (((stageSystem l Ω X).transIso h).inv.app K) := by
    apply (cancel_mono (FΩ.map (((stageSystem l Ω X).transIso h).hom.app K))).mp
    simp only [Category.assoc, ← FΩ.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    rw [ht]
    simp
  refine ⟨left, ?_⟩
  intro i j h L
  apply (adjΩ.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  apply (cancel_epi ((inclusion j).map ((q i j h).hom.app ((G i).obj L)) ≫
    (qΩ j).hom.app ((stageTransition l Ω X i j h).obj ((G i).obj L)))).mp
  have n := (qΩ j).hom.naturality ((b i j h).hom.app L)
  dsimp only [Functor.comp_map] at n
  have ha :
      (inclusion j).map ((q i j h).hom.app ((G i).obj L)) ≫
        (qΩ j).hom.app ((stageTransition l Ω X i j h).obj ((G i).obj L)) ≫
        FΩ.map ((inclusion j).map ((b i j h).hom.app L) ≫
          (bΩ j).hom.app ((stageTransition l Ω Y i j h).obj L)) ≫
        adjΩ.counit.app ((inclusion j).obj ((stageTransition l Ω Y i j h).obj L)) =
      (inclusion j).map ((stageTransition l Ω Y i j h).map ((adj i).counit.app L)) := by
    simp only [FΩ.map_comp, Category.assoc]
    rw [← reassoc_of% n, common_counit]
    rw [← (inclusion j).map_comp, ← (inclusion j).map_comp, finite_counit]
  have hb :
      (inclusion j).map ((q i j h).hom.app ((G i).obj L)) ≫
        (qΩ j).hom.app ((stageTransition l Ω X i j h).obj ((G i).obj L)) ≫
        FΩ.map (((stageSystem l Ω X).transIso h).hom.app ((G i).obj L) ≫
          (bΩ i).hom.app L ≫
          GΩ.map (((stageSystem l Ω Y).transIso h).inv.app L)) ≫
        adjΩ.counit.app ((inclusion j).obj ((stageTransition l Ω Y i j h).obj L)) =
      (inclusion j).map ((stageTransition l Ω Y i j h).map ((adj i).counit.app L)) := by
    rw [← Category.assoc, left]
    simp only [FΩ.map_comp, Category.assoc]
    rw [← FΩ.map_comp_assoc, Iso.inv_hom_id_app, FΩ.map_id, Category.id_comp]
    have nc := adjΩ.counit.naturality (((stageSystem l Ω Y).transIso h).inv.app L)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at nc
    rw [nc, reassoc_of% (common_counit i L)]
    have nt := ((stageSystem l Ω Y).transIso h).inv.naturality ((adj i).counit.app L)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at nt
    rw [nt, Iso.hom_inv_id_app_assoc]
  exact (by simpa only [Category.assoc] using ha.trans hb.symm)

end WeilConjectures
