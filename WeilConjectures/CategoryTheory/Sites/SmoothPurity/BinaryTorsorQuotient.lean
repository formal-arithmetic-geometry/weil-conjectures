/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.Torsor
/-! # The universal property of binary contracted products of torsors
Source: Stacks Project, Tag 03AJ.
(blueprint: lem-pur-binary-torsor-quotient-universal). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Sheaf.Torsor
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J AddCommGrpCat.{w}}
/-- A natural map of two abelian torsors, equivariant in each variable, is the
sheaf quotient by the antidiagonal action.
Source: Stacks Project, Tag 03AJ, contracted-product construction.
(blueprint: lem-pur-binary-torsor-quotient-universal).
Proof: for an output z and local inputs x,y, translate x by the unique group element
carrying m(x,y) to z and apply the invariant map. Equivariance and antidiagonal
invariance make this independent of both inputs. The sheaf condition glues these
values over the intersection of the two nonempty covering sieves. The glued values
are natural, have the required factorization, and are unique on that covering. -/
theorem binaryTorsorQuotient_universal (P Q R : Torsor G)
    (m : ∀ U, P.sheaf.obj.obj U → Q.sheaf.obj.obj U → R.sheaf.obj.obj U)
    (hn : ∀ {U V} (f : U ⟶ V) x y, R.sheaf.obj.map f (m U x y) =
      m V (P.sheaf.obj.map f x) (Q.sheaf.obj.map f y))
    (h₁ : ∀ U g x y, m U (P.vadd U g x) y = R.vadd U g (m U x y))
    (h₂ : ∀ U g x y, m U x (Q.vadd U g y) = R.vadd U g (m U x y))
    (F : Sheaf J (Type w))
    (a : ∀ U, P.sheaf.obj.obj U → Q.sheaf.obj.obj U → F.obj.obj U)
    (ha : ∀ {U V} (f : U ⟶ V) x y, F.obj.map f (a U x y) =
      a V (P.sheaf.obj.map f x) (Q.sheaf.obj.map f y))
    (hi : ∀ U g x y, a U (P.vadd U g x) (Q.vadd U (-g) y) = a U x y) :
    ∃! l : R.sheaf ⟶ F, ∀ U x y, l.hom.app U (m U x y) = a U x y := by
  let b U x y z := a U (P.vadd U (R.sub (m U x y) z) x) y
  have bn {U V} (f : U ⟶ V) x y z : F.obj.map f (b U x y z) =
      b V (P.sheaf.obj.map f x) (Q.sheaf.obj.map f y) (R.sheaf.obj.map f z) := by
    dsimp only [b]
    rw [ha, P.map_vadd, R.map_sub_apply, hn]
  have bi₁ U g x y z : b U (P.vadd U g x) y z = b U x y z := by
    dsimp only [b]
    rw [h₁, R.sub_vadd_left, ← P.add_vadd]
    congr 2
    abel
  have bi₂ U g x y z : b U x (Q.vadd U g y) z = b U x y z := by
    dsimp only [b]
    rw [h₂, R.sub_vadd_left]
    have he : R.sub (m U x y) z - g = -g + R.sub (m U x y) z := by abel
    rw [he, P.add_vadd]
    simpa only [neg_neg] using hi U (-g) (P.vadd U (R.sub (m U x y) z) x) y
  have be U x y x' y' z : b U x y z = b U x' y' z := by
    obtain ⟨g, rfl⟩ := (P.bijective_vadd U x).surjective x'
    obtain ⟨g', rfl⟩ := (Q.bijective_vadd U y).surjective y'
    rw [bi₁, bi₂]
  have ex (U : C) (z : R.sheaf.obj.obj (op U)) :
      ∃ s : F.obj.obj (op U), ∀ (V : C) (f : V ⟶ U) x y,
        F.obj.map f.op s = b (op V) x y (R.sheaf.obj.map f.op z) := by
    let S := nonemptySieve P.sheaf.obj U ⊓ nonemptySieve Q.sheaf.obj U
    have hS : S ∈ J U := J.intersection_covering (P.nonemptySieve_mem U)
      (Q.nonemptySieve_mem U)
    have hF := (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property _ hS
    let t : Presieve.FamilyOfElements F.obj S.arrows :=
      fun V f hf ↦ b (op V) hf.1.some hf.2.some (R.sheaf.obj.map f.op z)
    have ht : t.Compatible := by
      intro V₁ V₂ W f₁ f₂ g₁ g₂ h₁ h₂ he
      dsimp only [t]
      rw [bn, bn]
      have hz : R.sheaf.obj.map f₁.op (R.sheaf.obj.map g₁.op z) =
          R.sheaf.obj.map f₂.op (R.sheaf.obj.map g₂.op z) := by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
          ← op_comp, ← op_comp, he]
      rw [hz]
      exact be _ _ _ _ _ _
    refine ⟨hF.amalgamate t ht, fun V f x y ↦ ?_⟩
    rw [hF.valid_glue ht f ⟨⟨x⟩, ⟨y⟩⟩]
    exact be _ _ _ _ _ _
  choose l hl using ex
  have le (U : C) (s t : F.obj.obj (op U))
      (h : ∀ V (f : V ⟶ U) (_x : P.sheaf.obj.obj (op V))
        (_y : Q.sheaf.obj.obj (op V)),
        F.obj.map f.op s = F.obj.map f.op t) : s = t := by
    apply P.ext_of_nonempty F
    intro V f hx
    apply Q.ext_of_nonempty F
    intro W g hy
    obtain ⟨x⟩ := hx
    obtain ⟨y⟩ := hy
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp]
    exact h W (g ≫ f) (P.sheaf.obj.map g.op x) y
  let L : R.sheaf ⟶ F := ⟨{
    app := fun U ↦ TypeCat.ofHom (l U.unop)
    naturality := by
      intro U V f
      ext z
      apply le V.unop
      intro W g x y
      change F.obj.map g.op (l V.unop (R.sheaf.obj.map f z)) =
        F.obj.map g.op (F.obj.map f (l U.unop z))
      rw [hl _ _ _ _ x y, ← Functor.map_comp_apply F.obj f g.op]
      change _ = F.obj.map (g ≫ f.unop).op (l U.unop z)
      rw [hl _ _ _ _ x y, op_comp, Functor.map_comp_apply]
      rfl
  }⟩
  have hL U x y : L.hom.app U (m U x y) = a U x y := by
    change l U.unop (m U x y) = _
    have h := hl U.unop (m U x y) U.unop (𝟙 _) x y
    simpa only [op_id, Functor.map_id, types_id_apply, b, R.sub_self, P.zero_vadd] using h
  refine ⟨L, hL, fun L' hL' ↦ ?_⟩
  ext U z
  apply le U.unop
  intro V f x y
  have hz := R.sub_vadd (m (op V) x y) (R.sheaf.obj.map f.op z)
  have hm : m (op V) (P.vadd _ (R.sub (m (op V) x y)
      (R.sheaf.obj.map f.op z)) x) y = R.sheaf.obj.map f.op z :=
    (h₁ _ _ _ _).trans hz
  have hn' := ConcreteCategory.congr_hom (L'.hom.naturality f.op) z
  change L'.hom.app (op V) (R.sheaf.obj.map f.op z) =
    F.obj.map f.op (L'.hom.app U z) at hn'
  change F.obj.map f.op (L'.hom.app U z) = F.obj.map f.op (l U.unop z)
  rw [← hn', ← hm, hL']
  exact (hl U.unop z V f x y).symm

private theorem binary_factor_equivariant (P Q R S : Torsor G)
    (m : ∀ U, P.sheaf.obj.obj U → Q.sheaf.obj.obj U → R.sheaf.obj.obj U)
    (h₁ : ∀ U g x y, m U (P.vadd U g x) y = R.vadd U g (m U x y))
    (a : ∀ U, P.sheaf.obj.obj U → Q.sheaf.obj.obj U → S.sheaf.obj.obj U)
    (ha₁ : ∀ U g x y, a U (P.vadd U g x) y = S.vadd U g (a U x y))
    (l : R.sheaf ⟶ S.sheaf) (hl : ∀ U x y, l.hom.app U (m U x y) = a U x y) :
    ∀ U g z, l.hom.app U (R.vadd U g z) = S.vadd U g (l.hom.app U z) := by
  intro U g z
  apply P.ext_of_nonempty S.sheaf
  intro V f hx
  apply Q.ext_of_nonempty S.sheaf
  intro W h hy
  obtain ⟨x⟩ := hx
  obtain ⟨y⟩ := hy
  let v := h ≫ f
  let x' := P.vadd (op W) (R.sub
    (m (op W) (P.sheaf.obj.map h.op x) y) (R.sheaf.obj.map v.op z))
    (P.sheaf.obj.map h.op x)
  have he : m (op W) x' y = R.sheaf.obj.map v.op z :=
    (h₁ _ _ _ _).trans (R.sub_vadd _ _)
  have ln (z : R.sheaf.obj.obj U) :
      S.sheaf.obj.map v.op (l.hom.app U z) =
        l.hom.app (op W) (R.sheaf.obj.map v.op z) :=
    (ConcreteCategory.congr_hom (l.hom.naturality v.op) z).symm
  change S.sheaf.obj.map h.op (S.sheaf.obj.map f.op _) =
    S.sheaf.obj.map h.op (S.sheaf.obj.map f.op _)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
  rw [ln, S.map_vadd, ln, R.map_vadd, ← he, ← h₁, hl, hl, ha₁]

end CategoryTheory.Sheaf.Torsor
