/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The reduction of a group scheme over a perfect field

Let `G` be a group scheme over a field `k`. Its reduction `G_red`, the closed subscheme cut out
by the nilradical, is a subgroup scheme when `k` is perfect: the unit, multiplication and inverse
of `G` restricted to `G_red` factor through `G_red`, since their sources `Spec k`, `G_red` and
`G_red ×_k G_red` are reduced (the last one because `k` is perfect).

Over an algebraically closed field, `G_red` is therefore a reduced group scheme, hence smooth
when `G` is locally of finite type. Moreover, if `G` is of finite type, there is a surjective
affine morphism `G ⟶ G_red`: in characteristic `p` a power of the absolute Frobenius, in
characteristic zero the inverse of the isomorphism `G_red ≅ G` (Cartier's theorem).

## Main definitions

- `AlgebraicGeometry.GrpObj.reduction`: the reduction `G_red` of `G`, as a scheme over `k`.
- `AlgebraicGeometry.GrpObj.reductionι`: its inclusion into `G`.
- `AlgebraicGeometry.GrpObj.grpObjReduction`: the group structure on `G_red` over a perfect
  field.

## Main statements

- `AlgebraicGeometry.GrpObj.smooth_reduction_hom`: over an algebraically closed field, the
  reduction of a group scheme locally of finite type is smooth.
- `AlgebraicGeometry.GrpObj.exists_surjective_isAffineHom_reduction`: a group scheme of finite
  type over a field admits a surjective affine morphism onto its reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k]

/-- The reduction `G_red` of a scheme `G` over `k`: the closed subscheme cut out by the
nilradical, as a scheme over `k`. -/
noncomputable abbrev reduction (G : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk (G.left.nilradical.subschemeι ≫ G.hom)

/-- The inclusion `G_red ⟶ G` of the reduction, as a morphism over `k`. -/
noncomputable abbrev reductionι (G : Over (Spec (.of k))) : reduction G ⟶ G :=
  Over.homMk G.left.nilradical.subschemeι

instance (G : Over (Spec (.of k))) : IsReduced (reduction G).left :=
  inferInstanceAs (IsReduced G.left.nilradical.subscheme)

instance (G : Over (Spec (.of k))) : Mono (reductionι G) :=
  (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono G.left.nilradical.subschemeι))

/-- A morphism over `k` from a reduced scheme to `G` factors through the reduction of `G`. -/
lemma exists_comp_reductionι_eq {G Y : Over (Spec (.of k))} [IsReduced Y.left] (g : Y ⟶ G) :
    ∃ l : Y ⟶ reduction G, l ≫ reductionι G = g :=
  ⟨Over.homMk g.left.liftNilradical (by simp), by ext; simp⟩

/-- Over a perfect field the reduction of a group scheme is a subgroup scheme. -/
noncomputable instance grpObjReduction [PerfectField k] (G : Over (Spec (.of k))) [GrpObj G] :
    GrpObj (reduction G) := by
  have : IsReduced (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (.of k)))
  have : IsReduced (reduction G ⊗ reduction G).left :=
    isReduced_pullback_of_perfectField (reduction G).hom (reduction G).hom
  exact GrpObj.ofMono (reductionι G) (exists_comp_reductionι_eq _)
    (exists_comp_reductionι_eq _) (exists_comp_reductionι_eq _)

/-- Over an algebraically closed field, the reduction of a group scheme locally of finite type is
smooth. -/
instance smooth_reduction_hom [IsAlgClosed k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] : Smooth (reduction G).hom :=
  smooth_of_grpObj_of_isReduced_of_isAlgClosed (G.left.nilradical.subschemeι ≫ G.hom)

/-- A group scheme of finite type over a field admits a surjective affine morphism onto its
reduction: in characteristic `p` a power of the absolute Frobenius
(`AlgebraicGeometry.Scheme.exists_surjective_isAffineHom_nilradical_subscheme`), in
characteristic zero the inverse of the inclusion, which is an isomorphism by Cartier's theorem
(`AlgebraicGeometry.GrpObj.isReduced_of_charZero`). -/
theorem exists_surjective_isAffineHom_reduction (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ f : G.left ⟶ (reduction G).left, Surjective f ∧ IsAffineHom f := by
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := LocallyOfFiniteType.isLocallyNoetherian G.hom
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
  · refine Scheme.exists_surjective_isAffineHom_nilradical_subscheme G.left hp ?_
    rw [← map_natCast G.hom.appTop.hom, ← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom,
      ringChar.Nat.cast_ringChar, map_zero, map_zero]
  · have := ringChar.charP k
    rw [h0] at this
    have : CharZero k := CharP.charP_to_charZero k
    have := GrpObj.isReduced_of_charZero G
    have : IsIso G.left.nilradical.subschemeι :=
      (Scheme.isIso_subschemeι_iff_eq_bot _).mpr Scheme.nilradical_eq_bot
    exact ⟨inv G.left.nilradical.subschemeι, inferInstance, inferInstance⟩

end AlgebraicGeometry.GrpObj
