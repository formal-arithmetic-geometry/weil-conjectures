/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.HomCongr

/-! # Tensor transposition and contravariant dual adjunction

Source: the tensor-Hom arrows in the current blueprint's closed-costalk-duality proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory Opposite MonoidalCategory BraidedCategory
namespace WeilConjectures.CoefficientClosedStructure

variable {C : Type u} [Category.{v} C] {H : Cᵒᵖ × C ⥤ C}
  (S : CoefficientClosedStructure H)

/-- Naturality of transposition in the internal-Hom source follows from evaluation.
Source: Stacks 08J9, naturality of currying. -/
private theorem transpose_source {P P' N M : C} (f : P' ⟶ P)
    (g : S.tensor.obj (N, P) ⟶ M) :
    S.transpose N P' M (S.tensor.map (X := (N, P')) (Y := (N, P)) (𝟙 N, f) ≫ g) =
      S.transpose N P M g ≫ H.map (f.op, 𝟙 M) := by
  let : MonoidalCategory C := S.monoidal
  apply ((S.adjunction P').homEquiv N M).symm.injective
  change ((S.adjunction P').homEquiv N M).symm
      (((S.adjunction P').homEquiv N M) (S.tensor.map (X := (N, P')) (Y := (N, P)) (𝟙 N, f) ≫ g)) =
    ((S.adjunction P').homEquiv N M).symm
      (((S.adjunction P).homEquiv N M) g ≫ H.map (f.op, 𝟙 M))
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_counit]
  rw [S.evaluation_naturality P P' M f]
  simp only [tensor, MonoidalCategory.tensor_map, id_tensorHom]
  change (N ◁ f) ≫ g =
    (S.transpose N P M g ▷ P') ≫ (H.obj (op P, M) ◁ f) ≫ _
  rw [← whisker_exchange_assoc]
  congr 1
  change g = (tensorRight P).map (S.transpose N P M g) ≫ _
  exact (((S.adjunction P).homEquiv N M).symm_apply_apply g).symm.trans
    ((S.adjunction P).homEquiv_counit N M (((S.adjunction P).homEquiv N M) g))

private theorem untranspose_source {P P' N M : C} (f : P' ⟶ P)
    (g : N ⟶ H.obj (op P, M)) :
    ((S.adjunction P').homEquiv N M).symm (g ≫ H.map (f.op, 𝟙 M)) =
      S.tensor.map (X := (N, P')) (Y := (N, P)) (𝟙 N, f) ≫
        ((S.adjunction P).homEquiv N M).symm g := by
  let : MonoidalCategory C := S.monoidal
  apply ((S.adjunction P').homEquiv N M).injective
  rw [Equiv.apply_symm_apply]
  change _ = S.transpose N P' M _
  rw [S.transpose_source]
  exact congrArg (fun k : N ⟶ H.obj (op P, M) ↦
    k ≫ H.map (X := (op P, M)) (Y := (op P', M)) (f.op, 𝟙 M))
    (((S.adjunction P).homEquiv N M).apply_symm_apply g).symm

/-- Fixing the target of internal Hom gives the usual contravariant dual functor.
Source: Stacks 08J9, functoriality of derived internal Hom. -/
def dual (H : Cᵒᵖ × C ⥤ C) (M : C) : Cᵒᵖ ⥤ C :=
  ((𝟭 Cᵒᵖ).prod' ((Functor.const Cᵒᵖ).obj M)) ⋙ H

/-- In a symmetric closed category, dualization with respect to any object is
adjoint to its opposite. No biduality assertion is needed.
Source: Stacks 08J9, tensor-Hom and symmetry
(blueprint: lem-weil-closed-tensor-dual-adjunction).
Proof: Hom(L,D(K)) is Hom(L tensor K,M); precompose by the symmetry and curry
again to obtain Hom(K,D(L)). Naturality of currying and symmetry gives an adjunction. -/
theorem dual_adjunction (β : @SymmetricCategory C _ S.monoidal) (M : C) :
    Nonempty ((dual H M).rightOp ⊣ dual H M) := by
  let : MonoidalCategory C := S.monoidal
  let : SymmetricCategory C := β
  let E (K : C) (L : Cᵒᵖ) :
      ((dual H M).rightOp.obj K ⟶ L) ≃ (K ⟶ (dual H M).obj L) :=
    (opEquiv _ _).trans
      (((S.adjunction K).homEquiv L.unop M).symm.trans
        ((Iso.homCongr (β_ K L.unop).symm (Iso.refl M)).trans
          ((S.adjunction L.unop).homEquiv K M)))
  have hleft {K K' : C} {L : Cᵒᵖ}
      (f : K' ⟶ K) (g : (dual H M).rightOp.obj K ⟶ L) :
      E K' L ((dual H M).rightOp.map f ≫ g) = f ≫ E K L g := by
    simp only [E, Equiv.trans_apply, Iso.homCongr, Iso.symm_inv,
      Iso.refl_hom, Category.comp_id, opEquiv]
    change S.transpose K' L.unop M
        ((β_ K' L.unop).hom ≫
          ((S.adjunction K').homEquiv L.unop M).symm
            (g.unop ≫ H.map (f.op, 𝟙 M))) =
      f ≫ S.transpose K L.unop M
        ((β_ K L.unop).hom ≫ ((S.adjunction K).homEquiv L.unop M).symm g.unop)
    rw [S.untranspose_source]
    simp only [tensor, MonoidalCategory.tensor_map, id_tensorHom]
    rw [← Category.assoc, ← braiding_naturality_left, Category.assoc]
    exact (S.adjunction L.unop).homEquiv_naturality_left f _
  refine ⟨Adjunction.mkOfHomEquiv {
    homEquiv := E
    homEquiv_naturality_left_symm := ?_
    homEquiv_naturality_right := ?_ }⟩
  · intro K' K L f g
    apply (E K' L).injective
    rw [hleft]
    simp only [Equiv.apply_symm_apply]
  · intro K L L' f g
    simp only [E, Equiv.trans_apply, Iso.homCongr, Iso.symm_inv,
      Iso.refl_hom, Category.comp_id, opEquiv]
    change S.transpose K L'.unop M
        ((β_ K L'.unop).hom ≫ ((S.adjunction K).homEquiv L'.unop M).symm
          (g.unop ≫ f.unop)) =
      S.transpose K L.unop M
        ((β_ K L.unop).hom ≫ ((S.adjunction K).homEquiv L.unop M).symm f.unop) ≫
          H.map (g, 𝟙 M)
    rw [Adjunction.homEquiv_naturality_left_symm]
    change S.transpose K L'.unop M
        ((β_ K L'.unop).hom ≫ (g.unop ▷ K) ≫ _) = _
    rw [← Category.assoc, ← braiding_naturality_right, Category.assoc]
    simpa only [tensor, MonoidalCategory.tensor_map, id_tensorHom,
      Quiver.Hom.op_unop] using
      S.transpose_source (N := K) (M := M) g.unop
        ((β_ K L.unop).hom ≫ ((S.adjunction K).homEquiv L.unop M).symm f.unop)

/-- The closed-support projection isomorphism transports tensor-Hom transposition
across an exceptional adjunction. This is the complete natural Hom calculation,
including naturality in the test object and in the dualized object.
Source: current blueprint, closed-costalk-duality, the displayed Hom chain
(blueprint: lem-weil-closed-projection-common-adjunction).
Proof: the first adjunction is the composite of exceptional adjunction and dual
self-adjunction. For the second, uncurry, apply the projection isomorphism,
transpose by the exceptional adjunction, and curry on the closed part.
Naturality of these four operations proves the two adjunction naturality laws. -/
theorem common_left_of_projection
    {D : Type u'} [Category.{v'} D] {HD : Dᵒᵖ × D ⥤ D}
    (SD : CoefficientClosedStructure HD) (β : @SymmetricCategory C _ S.monoidal)
    (p : C ⥤ D) (q : D ⥤ C) (s : C ⥤ D) (a : q ⊣ s)
    (e : q.prod (𝟭 C) ⋙ S.tensor ≅ (𝟭 D).prod p ⋙ SD.tensor ⋙ q) (M : C) :
    ∃ F : D ⥤ Cᵒᵖ,
      Nonempty (Adjunction F (dual H M ⋙ s) ×
        Adjunction F (p.op ⋙ dual HD (s.obj M))) := by
  let : MonoidalCategory C := S.monoidal
  let : MonoidalCategory D := SD.monoidal
  obtain ⟨d⟩ := S.dual_adjunction β M
  let F := q ⋙ (dual H M).rightOp
  let E (N : D) (K : Cᵒᵖ) :
      (F.obj N ⟶ K) ≃ (N ⟶ (p.op ⋙ dual HD (s.obj M)).obj K) :=
    (d.homEquiv (q.obj N) K).trans
      (((S.adjunction K.unop).homEquiv (q.obj N) M).symm.trans
        ((Iso.homCongr (e.app (N, K.unop)) (Iso.refl M)).trans
          ((a.homEquiv _ M).trans ((SD.adjunction (p.obj K.unop)).homEquiv N (s.obj M)))))
  have hleft {N N' : D} {K : Cᵒᵖ} (f : N' ⟶ N) (g : F.obj N ⟶ K) :
      E N' K (F.map f ≫ g) = f ≫ E N K g := by
    simp only [E, Equiv.trans_apply, Iso.homCongr, Iso.refl_hom, Category.comp_id]
    change SD.transpose N' (p.obj K.unop) (s.obj M)
        ((a.homEquiv _ M) (e.inv.app (N', K.unop) ≫
          ((S.adjunction K.unop).homEquiv (q.obj N') M).symm
            ((d.homEquiv (q.obj N') K) ((dual H M).rightOp.map (q.map f) ≫ g)))) = _
    rw [d.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left_symm]
    have hn : e.inv.app (N', K.unop) ≫
        (@tensorRight C _ S.monoidal K.unop).map (q.map f) =
      q.map ((@tensorRight D _ SD.monoidal (p.obj K.unop)).map f) ≫
        e.inv.app (N, K.unop) := by
      have hc : S.tensor.map (X := (q.obj N', K.unop))
          (Y := (q.obj N, K.unop)) (q.map f, 𝟙 K.unop) =
          (@tensorRight C _ S.monoidal K.unop).map (q.map f) := by
        exact @tensorHom_id C _ S.monoidal _ _ (q.map f) K.unop
      have hd : SD.tensor.map (X := (N', p.obj K.unop))
          (Y := (N, p.obj K.unop)) (f, 𝟙 (p.obj K.unop)) =
          (@tensorRight D _ SD.monoidal (p.obj K.unop)).map f := by
        exact @tensorHom_id D _ SD.monoidal _ _ f (p.obj K.unop)
      have hn := (e.inv.naturality (X := (N', K.unop)) (Y := (N, K.unop))
        (f, 𝟙 K.unop)).symm
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Prod.mkHom] at hn
      simp only [p.map_id K.unop] at hn
      rw [hc, hd] at hn
      exact hn
    rw [← Category.assoc, hn, Category.assoc, Adjunction.homEquiv_naturality_left]
    exact (SD.adjunction (p.obj K.unop)).homEquiv_naturality_left f _
  have hright {N : D} {K K' : Cᵒᵖ} (f : F.obj N ⟶ K) (g : K ⟶ K') :
      E N K' (f ≫ g) = E N K f ≫ (p.op ⋙ dual HD (s.obj M)).map g := by
    simp only [E, Equiv.trans_apply, Iso.homCongr, Iso.refl_hom, Category.comp_id]
    change SD.transpose N (p.obj K'.unop) (s.obj M)
        ((a.homEquiv _ M) (e.inv.app (N, K'.unop) ≫
          ((S.adjunction K'.unop).homEquiv (q.obj N) M).symm
            ((d.homEquiv (q.obj N) K') (f ≫ g)))) = _
    rw [d.homEquiv_naturality_right]
    change SD.transpose N (p.obj K'.unop) (s.obj M)
        ((a.homEquiv _ M) (e.inv.app (N, K'.unop) ≫
          ((S.adjunction K'.unop).homEquiv (q.obj N) M).symm
            ((d.homEquiv (q.obj N) K) f ≫ H.map (g, 𝟙 M)))) = _
    have hu := S.untranspose_source (N := q.obj N) (M := M) g.unop
      ((d.homEquiv (q.obj N) K) f)
    simp only [Quiver.Hom.op_unop] at hu
    rw [hu]
    have hn : e.inv.app (N, K'.unop) ≫
        S.tensor.map (X := (q.obj N, K'.unop)) (Y := (q.obj N, K.unop))
          (𝟙 _, g.unop) =
      q.map (SD.tensor.map (X := (N, p.obj K'.unop)) (Y := (N, p.obj K.unop))
        (𝟙 _, p.map g.unop)) ≫ e.inv.app (N, K.unop) := by
      simpa only [Functor.comp_map, Functor.prod_map, Functor.id_map, q.map_id N, Prod.mkHom] using
        (e.inv.naturality (X := (N, K'.unop)) (Y := (N, K.unop))
          (𝟙 N, g.unop)).symm
    rw [← Category.assoc, hn, Category.assoc, Adjunction.homEquiv_naturality_left]
    change SD.transpose N (p.obj K'.unop) (s.obj M)
        (SD.tensor.map (X := (N, p.obj K'.unop)) (Y := (N, p.obj K.unop))
          (𝟙 _, p.map g.unop) ≫ _) =
      SD.transpose N (p.obj K.unop) (s.obj M) _ ≫
        HD.map (X := (op (p.obj K.unop), s.obj M))
          (Y := (op (p.obj K'.unop), s.obj M)) ((p.map g.unop).op, 𝟙 _)
    exact SD.transpose_source (N := N) (M := s.obj M) (p.map g.unop) _
  refine ⟨F, ⟨a.comp d, Adjunction.mkOfHomEquiv {
    homEquiv := E
    homEquiv_naturality_left_symm := ?_
    homEquiv_naturality_right := hright }⟩⟩
  intro N' N K f g
  apply (E N' K).injective
  rw [hleft]
  simp only [Equiv.apply_symm_apply]

end WeilConjectures.CoefficientClosedStructure

namespace CategoryTheory
open Limits
universe a b a' b' a'' b''
private theorem supportedUnit
    {C : Type a} [Category.{b} C] [HasZeroMorphisms C]
    {D : Type a'} [Category.{b'} D]
    {E : Type a''} [Category.{b''} E] [HasZeroMorphisms E]
    (p : C ⥤ D) (q : D ⥤ C) (r : C ⥤ E) (adj : p ⊣ q)
    [IsIso adj.counit]
    (detect : ∀ {X Y : C} (f : X ⟶ Y),
      IsIso (p.map f) → IsIso (r.map f) → IsIso f)
    (zero : ∀ N : D, IsZero (r.obj (q.obj N)))
    (X : C) (hX : IsZero (r.obj X)) : IsIso (adj.unit.app X) := by
  apply detect
  · have : IsIso (p.map (adj.unit.app X) ≫ adj.counit.app (p.obj X)) := by
      rw [adj.left_triangle_components X]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (p.obj X))
  · exact ⟨⟨0, hX.eq_of_src _ _, (zero _).eq_of_src _ _⟩⟩

private theorem projectionOfSupportedUnit
    {C : Type a} [Category.{b} C] {D : Type a'} [Category.{b'} D]
    (p : C ⥤ D) (q : D ⥤ C) (adj : p ⊣ q) [IsIso adj.counit]
    (tc : C × C ⥤ C) (td : D × D ⥤ D)
    (e : tc ⋙ p ≅ p.prod p ⋙ td)
    (hu : ∀ N K, IsIso (adj.unit.app (tc.obj (q.obj N, K)))) :
    Nonempty (q.prod (𝟭 C) ⋙ tc ≅ (𝟭 D).prod p ⋙ td ⋙ q) := by
  let f := q.prod (𝟭 C)
  let eta := Functor.whiskerLeft (f ⋙ tc) adj.unit
  have : IsIso eta := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact hu X.1 X.2
  let b : f ⋙ p.prod p ≅ (𝟭 D).prod p :=
    NatIso.prod (asIso adj.counit) (Iso.refl p)
  exact ⟨asIso eta ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft f e) q ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight b td) q⟩

end CategoryTheory
