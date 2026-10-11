/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The directed cover by affine opens ordered by basic open inclusion

The affine opens of a scheme `X`, preordered by `U ≤ V` if and only if `U` is a basic open
`D(g)` of `V` for some `g ∈ Γ(X, V)`, index a locally directed open cover of `X`. Compared to
`AlgebraicGeometry.Scheme.directedAffineCover`, its transition maps are localizations
`Γ(X, V) → Γ(X, V)_g`, which makes it convenient for relative gluing of quasi-coherent data.

## Main definitions

- `AlgebraicGeometry.Scheme.BasicAffineOpens`: the affine opens of `X` with the basic open
  preorder.
- `AlgebraicGeometry.Scheme.directedBasicAffineCover`: the corresponding locally directed open
  cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The affine opens of `X`, preordered by `U ≤ V` if `U` is a basic open of `V`. -/
def BasicAffineOpens : Type u := X.affineOpens

variable {X}

namespace BasicAffineOpens

/-- The underlying affine open. -/
def toAffineOpens (U : X.BasicAffineOpens) : X.affineOpens := U

/-- An affine open, viewed in `BasicAffineOpens`. -/
def ofAffineOpens (U : X.affineOpens) : X.BasicAffineOpens := U

/-- The underlying open. -/
abbrev opens (U : X.BasicAffineOpens) : X.Opens := U.toAffineOpens.1

lemma isAffineOpen (U : X.BasicAffineOpens) : IsAffineOpen U.opens := U.toAffineOpens.2

@[simp]
lemma toAffineOpens_ofAffineOpens (U : X.affineOpens) :
    (ofAffineOpens U).toAffineOpens = U := rfl

/-- `U ≤ V` if `U` is a basic open of `V`. -/
instance : Preorder X.BasicAffineOpens where
  le U V := ∃ g : Γ(X, V.opens), X.basicOpen g = U.opens
  le_refl U := ⟨1, X.basicOpen_one⟩
  le_trans U V W := by
    rintro ⟨g, hg⟩ ⟨f, hf⟩
    obtain ⟨f', hf'⟩ := W.isAffineOpen.basicOpen_basicOpen_is_basicOpen f
      (X.presheaf.map (eqToHom hf).op g)
    refine ⟨f', hf'.trans ?_⟩
    rw [Scheme.basicOpen_res_eq, hg]

lemma le_iff {U V : X.BasicAffineOpens} :
    U ≤ V ↔ ∃ g : Γ(X, V.opens), X.basicOpen g = U.opens := Iff.rfl

lemma opens_le_opens {U V : X.BasicAffineOpens} (h : U ≤ V) : U.opens ≤ V.opens := by
  obtain ⟨g, hg⟩ := h
  exact hg ▸ X.basicOpen_le g

end BasicAffineOpens

variable (X) in
open TopologicalSpace.Opens in
/-- The locally directed affine open cover of `X` given by all affine opens, with transition
maps the inclusions of basic opens. -/
@[simps I₀ X f]
def directedBasicAffineCover : X.OpenCover where
  I₀ := X.BasicAffineOpens
  X U := U.opens
  f U := U.opens.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    use BasicAffineOpens.ofAffineOpens
      ⟨(isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose,
      (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.1⟩
    exact ⟨⟨x, (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.2.1⟩, rfl⟩

instance : Preorder X.directedBasicAffineCover.I₀ := inferInstanceAs <| Preorder X.BasicAffineOpens

noncomputable instance : Scheme.Cover.LocallyDirected X.directedBasicAffineCover where
  trans {U V} f := X.homOfLE (BasicAffineOpens.opens_le_opens (leOfHom f))
  trans_id U := by
    simp
    rfl
  trans_comp f g := by simp
  w f := by simp
  directed {U V} x := by
    set y := (pullback.fst U.opens.ι V.opens.ι ≫ U.opens.ι) x
    have hyU : y ∈ U.opens := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    have hyV : y ∈ V.opens := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      refine ⟨pullback.snd U.opens.ι V.opens.ι x, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
    obtain ⟨f, g, hfg, hy⟩ := exists_basicOpen_le_affine_inter U.isAffineOpen
      V.isAffineOpen y ⟨hyU, hyV⟩
    let W : X.BasicAffineOpens :=
      BasicAffineOpens.ofAffineOpens ⟨X.basicOpen f, U.isAffineOpen.basicOpen f⟩
    have hWU : W ≤ U := ⟨f, rfl⟩
    have hWV : W ≤ V := ⟨g, hfg.symm⟩
    refine ⟨W, homOfLE hWU, homOfLE hWV, ⟨y, hy⟩, ?_⟩
    apply (pullback.fst U.opens.ι V.opens.ι ≫ U.opens.ι).isOpenEmbedding.injective
    have h := Scheme.Hom.comp_apply (pullback.lift (X.homOfLE (BasicAffineOpens.opens_le_opens hWU))
      (X.homOfLE (BasicAffineOpens.opens_le_opens hWV)) (by simp))
      (pullback.fst U.opens.ι V.opens.ι ≫ U.opens.ι) ⟨y, hy⟩
    simp only [pullback.lift_fst_assoc, Scheme.Hom.comp_apply, Scheme.homOfLE_apply,
      Scheme.Opens.ι_apply] at h
    exact h.symm.trans rfl

@[simp]
lemma directedBasicAffineCover_trans {U V : X.directedBasicAffineCover.I₀} (f : U ⟶ V) :
    Cover.trans X.directedBasicAffineCover f =
      X.homOfLE (BasicAffineOpens.opens_le_opens (leOfHom f)) := rfl

end AlgebraicGeometry.Scheme
