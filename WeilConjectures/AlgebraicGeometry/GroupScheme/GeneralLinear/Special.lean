/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Multiplicative
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.Determinant

/-!
# The special linear group scheme and the determinant

The special linear group `SL_n` over a commutative ring `k` is the closed subgroup scheme of
`𝔾𝕃(n; k)` cut out by the Hopf ideal `(det - 1)`; its `R`-points are the special linear group
`SL(n, R)`. The determinant is a homomorphism of group schemes `det : 𝔾𝕃(n; k) ⟶ 𝔾ₘ`, dual to
`t ↦ det`, which on `R`-points is the determinant `GL n R →* Rˣ`.

## Main definitions

- `AlgebraicGeometry.SpecialLinearGroup`, notation `𝕊𝕃(n; k)`: the special linear group scheme,
  with its closed immersion `GeneralLinearGroup.subgroupSchemeι` into `𝔾𝕃(n; k)`.
- `AlgebraicGeometry.SpecialLinearGroup.homMulEquiv`: the `R`-points of `𝕊𝕃(n; k)` are `SL(n, R)`.
- `AlgebraicGeometry.GeneralLinearGroup.det`: the determinant `𝔾𝕃(n; k) ⟶ 𝔾ₘ`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.homMulEquiv_comp_det`: on `R`-points, `det` is the
  determinant of invertible matrices.

## Blueprint

- `def-sc-general-linear-group`: the special linear group scheme `SL_{c,k} ⊆ GL_{c,k}` and the
  determinant homomorphism `GL_{c,k} → 𝐆_m`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv LaurentPolynomial
open scoped MonObj

namespace AlgebraicGeometry

open Matrix.GeneralLinearGroup (CoordinateRing specialLinearIdeal detBialgHom)

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [CommRing k]

/-- Blueprint `def-sc-general-linear-group`: The special linear group scheme
`SL_n = Spec k[x_ij] ⧸ (det - 1)` over a commutative ring `k`.

It is the closed subgroup scheme `V(det - 1)` of `𝔾𝕃(n; k)` cut out by the Hopf ideal `(det - 1)`
(`Matrix.GeneralLinearGroup.specialLinearIdeal`), with closed immersion
`GeneralLinearGroup.subgroupSchemeι` into `𝔾𝕃(n; k)`. Since `det` is invertible modulo
`det - 1`, its coordinate ring `k[x_ij, det⁻¹] ⧸ (det - 1)` is `k[x_ij] ⧸ (det - 1)`. Its
`R`-points are the special linear group `SL(n, R)`
(`AlgebraicGeometry.SpecialLinearGroup.homMulEquiv`). -/
noncomputable abbrev SpecialLinearGroup : Over (Spec (.of k)) :=
  GeneralLinearGroup.subgroupScheme (specialLinearIdeal n k)

@[inherit_doc] scoped notation "𝕊𝕃(" n "; " k ")" => SpecialLinearGroup n k

namespace SpecialLinearGroup

/-- Over a field, `𝕊𝕃(n; K) ⟶ 𝔾𝕃(n; K)` is a closed subgroup scheme.
(blueprint: `def-sc-general-linear-group`) -/
instance {K : Type u} [Field K] :
    IsClosedSubgroupScheme (GeneralLinearGroup.subgroupSchemeι (specialLinearIdeal n K)) where
  toIsSubgroupScheme := .of_mono _
  isClosedImmersion := inferInstance

/-- The `R`-points of `𝕊𝕃(n; k)` are the special linear group `SL(n, R)`.
(blueprint: `def-sc-general-linear-group`) -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝕊𝕃(n; k)) ≃* Matrix.SpecialLinearGroup n R :=
  (GeneralLinearGroup.zeroLocusMulEquiv (specialLinearIdeal n k) R).symm.trans
    (Matrix.GeneralLinearGroup.specialLinearGroupMulEquiv n k R).symm

variable {n k}

/-- The matrix of the point `φ ≫ ι` of `GL_n`, for `ι : SL_n ⟶ GL_n` the closed immersion, is the
matrix of the point `φ` of `SL_n`. -/
theorem coe_homMulEquiv {R : Type u} [CommRing R] [Algebra k R]
    (φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝕊𝕃(n; k)) :
    ((homMulEquiv n k R φ : Matrix n n R)) =
      (GeneralLinearGroup.homMulEquiv n k R (φ ≫ GeneralLinearGroup.subgroupSchemeι _) :
        Matrix n n R) := by
  obtain ⟨g, rfl⟩ := (GeneralLinearGroup.zeroLocusMulEquiv (specialLinearIdeal n k) R).surjective φ
  rw [GeneralLinearGroup.homMulEquiv_zeroLocusMulEquiv_comp]
  obtain ⟨A, rfl⟩ := (Matrix.GeneralLinearGroup.specialLinearGroupMulEquiv n k R).surjective g
  simp [homMulEquiv]

end SpecialLinearGroup

namespace GeneralLinearGroup

/-- Blueprint `def-sc-general-linear-group`: The determinant homomorphism `det : GL_n ⟶ 𝔾ₘ`, the
morphism of affine group schemes dual to the bialgebra homomorphism `k[t, t⁻¹] → k[x_ij, det⁻¹]`,
`t ↦ det` (`Matrix.GeneralLinearGroup.detBialgHom`). On `R`-points it is the determinant of
invertible matrices (`AlgebraicGeometry.GeneralLinearGroup.homMulEquiv_comp_det`). -/
noncomputable def det : 𝔾𝕃(n; k) ⟶ 𝔾ₘ[k] :=
  (Spec.map (CommRingCat.ofHom
    (detBialgHom n k : k[T;T⁻¹] →ₐ[k] CoordinateRing n k).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (det n k) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (detBialgHom n k)).op).hom)

variable {n k}

/-- On `R`-points, the determinant homomorphism `𝔾𝕃(n; k) ⟶ 𝔾ₘ` is the determinant
`GL n R →* Rˣ`. (blueprint: `def-sc-general-linear-group`) -/
theorem homMulEquiv_comp_det {R : Type u} [CommRing R] [Algebra k R]
    (f : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) :
    MultiplicativeGroup.homMulEquiv k R (f ≫ det n k) =
      Matrix.GeneralLinearGroup.det (homMulEquiv n k R f) := by
  unfold GeneralLinearGroup at f
  obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective f
  have hcomp : Spec.mapMulEquiv χ ≫ det n k = Spec.mapMulEquiv
      (toConv (χ.ofConv.comp (detBialgHom n k : k[T;T⁻¹] →ₐ[k] CoordinateRing n k))) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [hcomp, MultiplicativeGroup.homMulEquiv_mapMulEquiv, homMulEquiv_mapMulEquiv]
  ext
  simp [Matrix.GeneralLinearGroup.detCoord, AlgHom.map_det, AlgHom.mapMatrix_apply]

end GeneralLinearGroup

end AlgebraicGeometry
