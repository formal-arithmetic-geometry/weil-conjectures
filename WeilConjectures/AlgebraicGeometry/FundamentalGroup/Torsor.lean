/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Torsors under a finite abelian group and the étale fundamental group

Let `Y` be a connected scheme with geometric point `s` and let `M` be a finite abelian group.
An `M`-torsor `P` over `Y` (`AlgebraicGeometry.Scheme.EtaleTorsor`) is a finite étale
`Y`-scheme, and `M` acts simply transitively on its geometric fibre `P_s`, commuting with
the action of the étale fundamental group `π₁(Y, s)`. Choosing `p ∈ P_s`, the element `g` of
`π₁(Y, s)` moves `p` to `f_P(g) +ᵥ p`; this defines a continuous homomorphism
`f_P : π₁(Y, s) → M`, independent of `p` because `M` is abelian, and depending only on the
isomorphism class of `P` (`AlgebraicGeometry.Scheme.EtaleTorsor.monodromy`). Through the
Galois correspondence `AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction` the
construction `P ↦ f_P` is a bijection between isomorphism classes of `M`-torsors and
continuous homomorphisms `π₁(Y, s) → M`, and together with the torsor description of `H¹`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`) this identifies
`H¹(Y_ét, M)` with `Hom_cont(π₁(Y, s), M)`.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.toFiniteEtale`: a torsor as a finite étale scheme.
- `AlgebraicGeometry.Scheme.EtaleTorsor.monodromy`: the continuous homomorphism
  `f_P : π₁(Y, s) → M` attached to a torsor.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.existsUnique_fiber_map_vaddHom`: `M` acts simply
  transitively on the geometric fibre of a torsor.
- `AlgebraicGeometry.Scheme.EtaleTorsor.bijective_monodromy`: the bijection between
  isomorphism classes of torsors and continuous homomorphisms.
- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_equiv_sheafH_continuousMonoidHom`: the
  identification `H¹(Y_ét, M) ≃ Hom_cont(π₁(Y, s), M)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

/-- The total space of an `M`-torsor over `Y`, as a finite étale `Y`-scheme. -/
def toFiniteEtale (t : EtaleTorsor M Y) : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ t.π t.etale, t.isFinite⟩

@[simp]
lemma toFiniteEtale_obj_left (t : EtaleTorsor M Y) : t.toFiniteEtale.obj.left = t.P := rfl

@[simp]
lemma toFiniteEtale_obj_hom (t : EtaleTorsor M Y) : t.toFiniteEtale.obj.hom = t.π := rfl

/-- The action of `m : M` on the total space of a torsor, as an endomorphism of finite étale
`Y`-schemes. -/
def vaddHom (t : EtaleTorsor M Y) (m : M) : t.toFiniteEtale ⟶ t.toFiniteEtale :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m))

@[simp]
lemma vaddHom_hom_left (t : EtaleTorsor M Y) (m : M) : (t.vaddHom m).hom.left = t.vadd m := rfl

lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.hom_ext {P Q : Y.FiniteEtale} {f g : P ⟶ Q}
    (h : f.hom.left = g.hom.left) : f = g :=
  ObjectProperty.hom_ext _ (MorphismProperty.Over.Hom.ext h)

lemma vaddHom_zero (t : EtaleTorsor M Y) : t.vaddHom 0 = 𝟙 _ :=
  FiniteEtale.hom_ext t.zero_vadd

lemma vaddHom_add (t : EtaleTorsor M Y) (m n : M) :
    t.vaddHom (m + n) = t.vaddHom m ≫ t.vaddHom n :=
  FiniteEtale.hom_ext (t.add_vadd m n)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

section Fiber

open FiniteEtale

lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.fiber_map_left {P Q : Y.FiniteEtale}
    (f : P ⟶ Q) (x : (fiber s).obj P) : ((fiber s).map f x).left = x.left ≫ f.hom.left := rfl

lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.fiber_ext {P : Y.FiniteEtale}
    {x y : (fiber s).obj P} (h : x.left = y.left) : x = y :=
  Over.OverMorphism.ext h

lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.fiber_left_comp {P : Y.FiniteEtale}
    (x : (fiber s).obj P) : x.left ≫ P.obj.hom = s :=
  Over.w x

variable (t : EtaleTorsor M Y)

/-- Applying `m` and then `n` to a point of the geometric fibre is applying `m + n`. -/
lemma fiber_map_vaddHom_vaddHom (m n : M) (x : (fiber s).obj t.toFiniteEtale) :
    (fiber s).map (t.vaddHom n) ((fiber s).map (t.vaddHom m) x) =
      (fiber s).map (t.vaddHom (m + n)) x := by
  rw [vaddHom_add, Functor.map_comp, FintypeCat.comp_apply]

lemma fiber_map_vaddHom_zero (x : (fiber s).obj t.toFiniteEtale) :
    (fiber s).map (t.vaddHom 0) x = x := by
  rw [vaddHom_zero, CategoryTheory.Functor.map_id, FintypeCat.id_apply]

/-- `M` acts transitively on the geometric fibre of an `M`-torsor: the point `(y, x)` of
`P ×_Y P` comes from a unique summand of `∐_{m ∈ M} P ≅ P ×_Y P`, and a morphism from the
spectrum of a field into a coproduct factors through one summand. -/
lemma exists_fiber_map_vaddHom (x y : (fiber s).obj t.toFiniteEtale) :
    ∃ m, (fiber s).map (t.vaddHom m) x = y := by
  have := t.isIso_sigmaDesc
  let D := Sigma.desc fun m : M ↦
    pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P) (by rw [t.vadd_π, Category.id_comp])
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Spec (.of Ω) ⟶ pullback t.π t.π,
      z ≫ pullback.fst _ _ = y.left ∧ z ≫ pullback.snd _ _ = x.left :=
    ⟨pullback.lift y.left x.left ((fiber_left_comp s y).trans (fiber_left_comp s x).symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  let w := z ≫ inv D
  obtain ⟨m, p, hp⟩ : ∃ (m : M) (p : t.P), Sigma.ι (fun _ : M ↦ t.P) m p = w default :=
    (sigmaOpenCover fun _ : M ↦ t.P).exists_eq (w default)
  have hrange : Set.range w.base ⊆ Set.range (Sigma.ι (fun _ : M ↦ t.P) m).base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default]
    exact ⟨p, hp⟩
  have : IsOpenImmersion (Sigma.ι (fun _ : M ↦ t.P) m) :=
    (sigmaOpenCover fun _ : M ↦ t.P).map_prop (m : (sigmaOpenCover fun _ : M ↦ t.P).I₀)
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Sigma.ι (fun _ : M ↦ t.P) m = w :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have h1 : l ≫ pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
      (by rw [t.vadd_π, Category.id_comp]) = z := by
    rw [← Sigma.ι_desc (fun m : M ↦ pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
      (by rw [t.vadd_π, Category.id_comp])) m, ← Category.assoc, hl]
    simp [w, D]
  have hfst := congrArg (· ≫ pullback.fst t.π t.π) h1
  have hsnd := congrArg (· ≫ pullback.snd t.π t.π) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id, hz1, hz2]
    at hfst hsnd
  refine ⟨m, fiber_ext s ?_⟩
  change x.left ≫ t.vadd m = y.left
  exact hsnd ▸ hfst

/-- `M` acts freely on the geometric fibre of an `M`-torsor: the summands of
`∐_{m ∈ M} P ≅ P ×_Y P` are disjoint. -/
lemma eq_of_fiber_map_vaddHom_eq (x : (fiber s).obj t.toFiniteEtale) {m n : M}
    (h : (fiber s).map (t.vaddHom m) x = (fiber s).map (t.vaddHom n) x) : m = n := by
  have := t.isIso_sigmaDesc
  let x' : Spec (.of Ω) ⟶ t.P := x.left
  have h' : x' ≫ t.vadd m = x' ≫ t.vadd n := congrArg CommaMorphism.left h
  have h2 : x' ≫ Sigma.ι (fun _ : M ↦ t.P) m = x' ≫ Sigma.ι (fun _ : M ↦ t.P) n := by
    rw [← cancel_mono (Sigma.desc fun m : M ↦
      pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P) (by rw [t.vadd_π, Category.id_comp]))]
    apply pullback.hom_ext <;>
      simp only [Category.assoc, Sigma.ι_desc_assoc, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id, h']
  have h3 := congrArg (fun f ↦ f (default : Spec (.of Ω))) h2
  simp only [Scheme.Hom.comp_apply] at h3
  have := (sigmaι_eq_iff (fun _ : M ↦ t.P) m n _ _).mp h3
  exact congrArg Sigma.fst this

/-- Blueprint `cor-galois-abelian-h1`: Abelian case: torsors, characters and H^1.

`M` acts simply transitively on the geometric fibre `P_s` of an `M`-torsor `P`. -/
lemma existsUnique_fiber_map_vaddHom (x y : (fiber s).obj t.toFiniteEtale) :
    ∃! m, (fiber s).map (t.vaddHom m) x = y := by
  obtain ⟨m, hm⟩ := t.exists_fiber_map_vaddHom s x y
  exact ⟨m, hm, fun n hn ↦ t.eq_of_fiber_map_vaddHom_eq s x (hn.trans hm.symm)⟩

/-- The geometric fibre of an `M`-torsor is nonempty, as its structure morphism is
surjective. -/
lemma nonempty_fiber : Nonempty ((fiber s).obj t.toFiniteEtale) := by
  have := t.etale
  have := t.surjective
  obtain ⟨x, hx⟩ := t.π.surjective (s default)
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed t.π s x hx
  exact ⟨Over.homMk l hl⟩

end Fiber

end AlgebraicGeometry.Scheme.EtaleTorsor
