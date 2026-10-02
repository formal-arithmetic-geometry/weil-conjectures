/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# The general linear group scheme

The general linear group `GL_n` over a commutative ring `k` is the affine group scheme
`Spec k[x_ij, det⁻¹]` over `Spec k`, the spectrum of the Hopf algebra
`Matrix.GeneralLinearGroup.CoordinateRing n k`. Mathlib's `instGrpObjSpecAsOverSpec` makes it a
group object in `Over (Spec k)`. Its points with values in a `k`-algebra `R` are the invertible
`n × n` matrices over `R`, as groups.

## Main definitions

- `Matrix.GeneralLinearGroup.scheme`: `GL_n` as an affine group scheme of finite type over `k`.
- `Matrix.GeneralLinearGroup.homMulEquiv`: the `R`-points of the group scheme `GL_n` are the
  group `GL n R`.

## Blueprint

- `sk-d-geometry`: the ambient group `GL(V)` of the algebraic groups block, as a group scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv
open scoped MonObj

namespace Matrix.GeneralLinearGroup

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [CommRing k]

/-- The general linear group `GL_n` as an affine group scheme over `k`: the spectrum of the Hopf
algebra `k[x_ij, det⁻¹]`. It is a group object by `instGrpObjSpecAsOverSpec`.
(blueprint: `sk-d-geometry`) -/
noncomputable abbrev scheme : Over (Spec (.of k)) :=
  (Spec (.of (CoordinateRing n k))).asOver (Spec (.of k))

noncomputable example : GrpObj (scheme n k) := inferInstance

instance : IsAffine (scheme n k).left :=
  inferInstanceAs (IsAffine (Spec (.of (CoordinateRing n k))))

instance : LocallyOfFiniteType (scheme n k).hom :=
  locallyOfFiniteType_specOverSpec

/-- The `R`-points of the group scheme `GL_n` are the invertible `n × n` matrices over `R`, as
groups. (blueprint: `sk-d-geometry`) -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ scheme n k) ≃* GL n R :=
  Spec.mapMulEquiv.symm.trans (algHomMulEquiv n k R)

variable {n k} {R S : Type u} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-- The identification `homMulEquiv` of the points of `GL_n` with invertible matrices is natural
in the algebra of values: precomposing with `Spec S ⟶ Spec R` maps the entries along `R → S`. -/
theorem homMulEquiv_specMap_comp (φ : R →ₐ[k] S)
    (f : (Spec (.of R)).asOver (Spec (.of k)) ⟶ scheme n k) :
    homMulEquiv n k S ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of k)) ≫ f) =
      map φ.toRingHom (homMulEquiv n k R f) := by
  obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective f
  simp only [Spec.map_asOver_comp_mapMulEquiv, homMulEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  rw [← toConv_ofConv χ, map_algHomMulEquiv, ofConv_toConv]

end Matrix.GeneralLinearGroup
