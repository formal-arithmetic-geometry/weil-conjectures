/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal Hom and equivariant currying for fixed pairs

Source: blueprint `sec-six-functors-basics/sk-prop-diagonal-tower/`
`sk-prop-diagonal-tower-system.proof.md`, Step (2), auxiliary monoidal fixed-pair
structure (blueprint: lem-pur-fixed-pair-internal-hom-currying).

## Main definitions and statements

- `CategoryTheory.Endofunctor.IsoAlgebra.diagonalTensorPair`: the diagonal tensor pair.
- `CategoryTheory.Endofunctor.IsoAlgebra.conjugatedIhomStr`: the conjugated structure iso.
- `CategoryTheory.Endofunctor.IsoAlgebra.conjugatedIhomPair`: its fixed pair.
- `CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_internalHom_currying`: comparison
  invertibility, the equivariance criterion, and the natural restricted adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.Endofunctor.IsoAlgebra

open MonoidalCategory MonoidalClosed

section Constructions

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (T : C ⥤ C) [T.Monoidal] [T.IsEquivalence]

/-- The diagonal tensor fixed pair, with structure `μ⁻¹ ≫ (θ_M ⊗ θ_L)`.
Source: diagonal-tower-system.proof.md, Step (2), auxiliary fixed-pair tensor structure
(blueprint: lem-pur-fixed-pair-internal-hom-currying). -/
noncomputable def diagonalTensorPair (M L : IsoAlgebra T) : IsoAlgebra T :=
  IsoAlgebra.mk (M.carrier ⊗ L.carrier)
    ((Functor.Monoidal.μIso T M.carrier L.carrier).symm ≪≫ tensorIso M.str L.str)

/-- The structure `h = γ ≫ [θ_M⁻¹, θ_N]` on the ordinary internal Hom. The comparison
is the canonical evaluation transpose, and precomposition uses the inverse of `θ_M`.
Source: diagonal-tower-system.proof.md, Step (2), auxiliary fixed-pair internal Hom
(blueprint: lem-pur-fixed-pair-internal-hom-currying). -/
noncomputable def conjugatedIhomStr (M N : IsoAlgebra T) :
    T.obj ((ihom M.carrier).obj N.carrier) ≅ (ihom M.carrier).obj N.carrier :=
  Functor.Monoidal.ihomObjIso T M.carrier N.carrier ≪≫
    ihomIsoOfIsoLeft M.str (T.obj N.carrier) ≪≫ (ihom M.carrier).mapIso N.str

/-- The internal-Hom fixed pair with its canonical conjugated structure.
Source: diagonal-tower-system.proof.md, Step (2), auxiliary fixed-pair internal Hom
(blueprint: lem-pur-fixed-pair-internal-hom-currying). -/
noncomputable def conjugatedIhomPair (M N : IsoAlgebra T) : IsoAlgebra T :=
  IsoAlgebra.mk ((ihom M.carrier).obj N.carrier) (conjugatedIhomStr T M N)

end Constructions

private theorem conjugated_uncurry
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (T : C ⥤ C) [T.Monoidal] [T.IsEquivalence]
    (M N : IsoAlgebra T) {Z : C} (g : Z ⟶ (ihom M.carrier).obj N.carrier) :
    uncurry (T.map g ≫ (conjugatedIhomStr T M N).hom) =
      M.str.inv ▷ T.obj Z ≫ Functor.LaxMonoidal.μ T M.carrier Z ≫
        T.map (uncurry g) ≫ N.str.hom := by
  simp only [conjugatedIhomStr, Iso.trans_hom, ihomIsoOfIsoLeft_hom,
    Functor.mapIso_hom, ← Category.assoc]
  rw [uncurry_natural_right, uncurry_pre_app, uncurry_natural_left, uncurry_eq,
    Functor.Monoidal.ihomObjIso_hom]
  simp only [Functor.Monoidal.commIhom, asIso_hom]
  rw [Functor.LaxMonoidal.ihomComparison_ev]
  simp only [Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
    ← T.map_comp, ← uncurry_eq]

private theorem curry_natural_all
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {X X' Y Y' Z Z' : C} (a : X' ⟶ X) (c : Y' ⟶ Y)
    (f : X ⊗ Y ⟶ Z) (b : Z ⟶ Z') :
    curry ((a ⊗ₘ c) ≫ f ≫ b) =
      c ≫ curry f ≫ (pre a).app Z ≫ (ihom X').map b := by
  apply uncurry_injective
  simp only [← Category.assoc]
  rw [uncurry_curry, uncurry_natural_right, uncurry_pre_app, uncurry_natural_left,
    uncurry_curry]
  simp only [tensorHom_def, Category.assoc]

private theorem curry_equivariant_iff
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (T : C ⥤ C) [T.Monoidal] [T.IsEquivalence]
    (M N L : IsoAlgebra T) (f : M.carrier ⊗ L.carrier ⟶ N.carrier) :
    ((M.str.hom ⊗ₘ L.str.hom) ≫ f =
      Functor.LaxMonoidal.μ T M.carrier L.carrier ≫ T.map f ≫ N.str.hom) ↔
    (L.str.hom ≫ curry f = T.map (curry f) ≫ (conjugatedIhomStr T M N).hom) := by
  rw [← uncurry_injective.eq_iff, uncurry_natural_left, conjugated_uncurry,
    uncurry_curry, ← cancel_epi (M.str.hom ▷ T.obj L.carrier)]
  simp only [← Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp, tensorHom_def]

/-- Equivariant currying for fixed pairs, including naturality in all three pairs.
Source: diagonal-tower-system.proof.md, Step (2), auxiliary fixed-pair closed structure
(blueprint: lem-pur-fixed-pair-internal-hom-currying).

Proof plan, following the six steps of the node:
1. The diagonal structure is `δ = μ⁻¹ ≫ (θ_M ⊗ θ_L)`. Precomposing its morphism
   equation with `μ` gives the displayed tensor equivariance equation. Tensorator
   naturality shows that tensor products of fixed-pair morphisms respect `δ`.
2. By `lem-pod-closed-uncurry-laws`, uncurrying `[a,b]` gives evaluation precomposed
   with `a` and postcomposed with `b`. Uncurrying twice proves bifunctoriality;
   hence `[θ_M⁻¹,θ_N]` has inverse `[θ_M,θ_N⁻¹]`.
3. Apply `lem-pur-monoidal-equivalence-hom-comparison` to `T`. Its canonical
   comparison is invertible and satisfies the tensorator evaluation identity.
   Composing with the isomorphism in Step 2 gives `conjugatedIhomStr`.
4. Write `g = curry f`. The evaluation identity for the comparison, the
   precomposition evaluation identity, and tensorator naturality identify
   `ev (θ_M ⊗ (T(g) ≫ h))` with `μ ≫ T(f) ≫ θ_N`.
5. Uncurry `θ_L ≫ g` and `T(g) ≫ h`, and precompose with the isomorphism
   `θ_M ⊗ 1`. Step 4 and injectivity of uncurrying prove the stated iff.
6. Restrict the inverse ordinary curry/uncurry bijections by Steps 1 and 5. The
   evaluation `M ⊗ H ⟶ N` of `H = conjugatedIhomPair T M N` is the restricted
   uncurry of `𝟙 H`, hence equivariant. For equivariant `a` and `b`, the restricted
   curry of `(a ⊗ 𝟙 H) ≫ ev ≫ b` is a fixed-pair morphism `q` whose carrier is
   `[a,b]` by ordinary currying naturality in all three variables; the same
   naturality gives the final identity for `a`, `b`, and `c`. -/
theorem fixedPair_internalHom_currying
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [SymmetricCategory C] (T : C ⥤ C) [T.Braided] [T.IsEquivalence] :
    (∀ X Y : C, IsIso ((Functor.LaxMonoidal.ihomComparison T X).natTrans.app Y)) ∧
    (∀ (M N L : IsoAlgebra T) (f : M.carrier ⊗ L.carrier ⟶ N.carrier),
      ((M.str.hom ⊗ₘ L.str.hom) ≫ f =
        Functor.LaxMonoidal.μ T M.carrier L.carrier ≫ T.map f ≫ N.str.hom) ↔
      (L.str.hom ≫ curry f = T.map (curry f) ≫ (conjugatedIhomStr T M N).hom)) ∧
    (∃ e : ∀ M L N : IsoAlgebra T,
        (diagonalTensorPair T M L ⟶ N) ≃ (L ⟶ conjugatedIhomPair T M N),
      (∀ (M L N : IsoAlgebra T) (f : diagonalTensorPair T M L ⟶ N),
        (e M L N f).hom.f = curry f.hom.f) ∧
      (∀ (M L N : IsoAlgebra T) (g : L ⟶ conjugatedIhomPair T M N),
        ((e M L N).symm g).hom.f = uncurry g.hom.f) ∧
      (∀ (M M' L L' N N' : IsoAlgebra T) (a : M' ⟶ M) (c : L' ⟶ L)
          (b : N ⟶ N'),
        ∃ (t : diagonalTensorPair T M' L' ⟶ diagonalTensorPair T M L)
          (q : conjugatedIhomPair T M N ⟶ conjugatedIhomPair T M' N'),
          t.hom.f = a.hom.f ⊗ₘ c.hom.f ∧
          q.hom.f = (pre a.hom.f).app N.carrier ≫ (ihom M'.carrier).map b.hom.f ∧
          ∀ f : diagonalTensorPair T M L ⟶ N,
            e M' L' N' (t ≫ f ≫ b) = c ≫ e M L N f ≫ q)) := by
  classical
  refine ⟨fun X Y ↦ inferInstance, curry_equivariant_iff T, ?_⟩
  have tensor_condition (M L N : IsoAlgebra T)
      (f : M.carrier ⊗ L.carrier ⟶ N.carrier) :
      T.map f ≫ N.str.hom = (diagonalTensorPair T M L).str.hom ≫ f ↔
        (M.str.hom ⊗ₘ L.str.hom) ≫ f =
          Functor.LaxMonoidal.μ T M.carrier L.carrier ≫ T.map f ≫ N.str.hom := by
    rw [← cancel_epi (Functor.Monoidal.μIso T M.carrier L.carrier).hom]
    simp [diagonalTensorPair, Category.assoc, eq_comm]
  let e : ∀ M L N : IsoAlgebra T,
      (diagonalTensorPair T M L ⟶ N) ≃ (L ⟶ conjugatedIhomPair T M N) := fun M L N ↦
    { toFun := fun f ↦ by
        refine ⟨{ f := curry f.hom.f, h := ?_ }⟩
        exact ((curry_equivariant_iff T M N L f.hom.f).mp
          ((tensor_condition M L N f.hom.f).mp f.hom.h)).symm
      invFun := fun g ↦ by
        refine ⟨{ f := uncurry g.hom.f, h := ?_ }⟩
        exact (tensor_condition M L N _).mpr
          ((curry_equivariant_iff T M N L _).mpr (by
            rw [curry_uncurry]
            exact g.hom.h.symm))
      left_inv := fun f ↦ by
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        exact uncurry_curry _
      right_inv := fun g ↦ by
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        exact curry_uncurry _ }
  have tensor_map (M M' L L' : IsoAlgebra T) (a : M' ⟶ M) (c : L' ⟶ L) :
      ∃ t : diagonalTensorPair T M' L' ⟶ diagonalTensorPair T M L,
        t.hom.f = a.hom.f ⊗ₘ c.hom.f := by
    refine ⟨⟨{ f := a.hom.f ⊗ₘ c.hom.f, h := ?_ }⟩, rfl⟩
    change T.map (a.hom.f ⊗ₘ c.hom.f) ≫
        (Functor.Monoidal.μIso T M.carrier L.carrier).inv ≫
          (M.str.hom ⊗ₘ L.str.hom) =
      ((Functor.Monoidal.μIso T M'.carrier L'.carrier).inv ≫
        (M'.str.hom ⊗ₘ L'.str.hom)) ≫ (a.hom.f ⊗ₘ c.hom.f)
    have ha : T.map a.hom.f ≫ M.str.hom = M'.str.hom ≫ a.hom.f := a.hom.h
    have hc : T.map c.hom.f ≫ L.str.hom = L'.str.hom ≫ c.hom.f := c.hom.h
    simp only [Functor.Monoidal.μIso_inv]
    rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural]
    simp only [Category.assoc, tensorHom_comp_tensorHom]
    rw [ha, hc]
  refine ⟨e, fun _ _ _ _ ↦ rfl, fun _ _ _ _ ↦ rfl, ?_⟩
  intro M M' L L' N N' a c b
  obtain ⟨t, ht⟩ := tensor_map M M' L L' a c
  let H := conjugatedIhomPair T M N
  let ev : diagonalTensorPair T M H ⟶ N := (e M H N).symm (𝟙 H)
  obtain ⟨s, hs⟩ := tensor_map M M' H H a (𝟙 H)
  let q : H ⟶ conjugatedIhomPair T M' N' := e M' H N' (s ≫ ev ≫ b)
  have hq : q.hom.f =
      (pre a.hom.f).app N.carrier ≫ (ihom M'.carrier).map b.hom.f := by
    change curry ((s ≫ ev ≫ b).hom.f) = _
    simp only [comp_hom_f, hs]
    change curry ((a.hom.f ⊗ₘ 𝟙 H.carrier) ≫ uncurry (𝟙 H.carrier) ≫ b.hom.f) = _
    simpa only [curry_uncurry, Category.id_comp] using
      (curry_natural_all a.hom.f (𝟙 H.carrier)
        (uncurry (𝟙 H.carrier)) b.hom.f)
  refine ⟨t, q, ht, hq, ?_⟩
  intro f
  apply ObjectProperty.hom_ext
  apply Algebra.Hom.ext
  change curry ((t ≫ f ≫ b).hom.f) = (c ≫ e M L N f ≫ q).hom.f
  simp only [comp_hom_f, ht, hq]
  change curry ((a.hom.f ⊗ₘ c.hom.f) ≫ f.hom.f ≫ b.hom.f) =
    c.hom.f ≫ curry f.hom.f ≫
      (pre a.hom.f).app N.carrier ≫ (ihom M'.carrier).map b.hom.f
  exact curry_natural_all a.hom.f c.hom.f f.hom.f b.hom.f

end CategoryTheory.Endofunctor.IsoAlgebra
