/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Multiplicative
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.SpecialLinear

/-!
# The determinant and the special linear group scheme

The general linear group scheme `GL_{n,k} = Spec k[x_ij, det⁻¹]` is
`AlgebraicGeometry.GeneralLinearGroup`, notation `𝔾𝕃(n; k)`. The determinant is a homomorphism of
group schemes `det : 𝔾𝕃(n; k) ⟶ 𝔾ₘ(k)`, the spectrum of the Hopf algebra homomorphism
`k[t, t⁻¹] → k[x_ij, det⁻¹]`, `t ↦ det (x_ij)`. On `R`-points it is the determinant
`GL n R → Rˣ`.

The special linear group scheme `SL_{n,k} = Spec k[x_ij] ⧸ (det - 1)` is the closed subgroup
scheme of `𝔾𝕃(n; k)` cut out by the Hopf ideal `(det - 1)`; its `R`-points are the matrices of
determinant `1`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.det`: the determinant `𝔾𝕃(n; k) ⟶ 𝔾ₘ(k)`.
- `AlgebraicGeometry.SpecialLinearGroup`, notation `𝕊𝕃(n; k)`: the special linear group scheme,
  with its closed immersion `SpecialLinearGroup.ι` into `𝔾𝕃(n; k)`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.homMulEquiv_comp_det`: on points, `det` is the
  determinant of invertible matrices.
- `AlgebraicGeometry.SpecialLinearGroup.range_homMulEquiv_comp_ι`: the `R`-points of `𝕊𝕃(n; k)`
  are the invertible matrices of determinant `1`.

## Blueprint

- `def-sc-general-linear-group`: the general and special linear group schemes and the
  determinant.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv LaurentPolynomial
open scoped MonObj
open Matrix.GeneralLinearGroup (CoordinateRing detUnit detAlgHom detBialgHom specialLinearIdeal
  evalAlgHom evalAlgHom_detUnit algHomMulEquiv zeroLocus mem_zeroLocus)

namespace AlgebraicGeometry

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [CommRing k]

namespace GeneralLinearGroup

/-- The determinant `det : 𝔾𝕃(n; k) ⟶ 𝔾ₘ(k)`, a homomorphism of group schemes: the spectrum of
the Hopf algebra homomorphism `k[t, t⁻¹] → k[x_ij, det⁻¹]`, `t ↦ det (x_ij)`.
(blueprint: `def-sc-general-linear-group`) -/
noncomputable def det : 𝔾𝕃(n; k) ⟶ 𝔾ₘ(k) :=
  (Spec.map (CommRingCat.ofHom (detAlgHom n k).toRingHom)).asOver (Spec (.of k))

instance : IsMonHom (det n k) :=
  inferInstanceAs (IsMonHom ((bialgSpec (.of k)).map
    (CommBialgCat.ofHom (detBialgHom n k)).op).hom)

variable {n k}

/-- On `R`-points, the homomorphism `det : 𝔾𝕃(n; k) ⟶ 𝔾ₘ(k)` is the determinant
`GL n R → Rˣ`. -/
theorem homMulEquiv_comp_det {R : Type u} [CommRing R] [Algebra k R]
    (φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) :
    MultiplicativeGroup.homMulEquiv k R (φ ≫ det n k) =
      Matrix.GeneralLinearGroup.det (GeneralLinearGroup.homMulEquiv n k R φ) := by
  unfold GeneralLinearGroup at φ
  obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective φ
  have h : Spec.mapMulEquiv χ ≫ det n k =
      Spec.mapMulEquiv (toConv (χ.ofConv.comp (detAlgHom n k))) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [h, homMulEquiv_mapMulEquiv]
  ext
  rw [MultiplicativeGroup.val_homMulEquiv_mapMulEquiv, ofConv_toConv, AlgHom.comp_apply,
    Matrix.GeneralLinearGroup.detAlgHom_T_one, Matrix.GeneralLinearGroup.algHomMulEquiv_apply,
    Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  rfl

end GeneralLinearGroup

/-- Blueprint `def-sc-general-linear-group`: the special linear group scheme
`SL_{n,k} = Spec k[x_ij] ⧸ (det - 1)`, the closed subgroup scheme of the general linear group
scheme `GL_{n,k} = Spec k[x_ij, det⁻¹]` (which is `AlgebraicGeometry.GeneralLinearGroup`,
notation `𝔾𝕃(n; k)`) cut out by the Hopf ideal `(det - 1)`. The determinant homomorphism
`GL_{n,k} ⟶ 𝔾ₘ`, dual to `t ↦ det`, is `AlgebraicGeometry.GeneralLinearGroup.det`. -/
noncomputable abbrev SpecialLinearGroup : Over (Spec (.of k)) :=
  GeneralLinearGroup.subgroupScheme (specialLinearIdeal n k)

@[inherit_doc] scoped notation "𝕊𝕃(" n "; " k ")" => SpecialLinearGroup n k

namespace SpecialLinearGroup

/-- The closed immersion `𝕊𝕃(n; k) ⟶ 𝔾𝕃(n; k)`, the spectrum of the quotient map
`k[x_ij, det⁻¹] → k[x_ij, det⁻¹] ⧸ (det - 1)`. It is a homomorphism of group schemes.
(blueprint: `def-sc-general-linear-group`) -/
noncomputable def ι : 𝕊𝕃(n; k) ⟶ 𝔾𝕃(n; k) :=
  GeneralLinearGroup.subgroupSchemeι (specialLinearIdeal n k)

instance : IsMonHom (ι n k) :=
  inferInstanceAs (IsMonHom (GeneralLinearGroup.subgroupSchemeι (specialLinearIdeal n k)))

instance : IsClosedImmersion (ι n k).left :=
  inferInstanceAs (IsClosedImmersion
    (GeneralLinearGroup.subgroupSchemeι (specialLinearIdeal n k)).left)

instance : Mono (ι n k) :=
  inferInstanceAs (Mono (GeneralLinearGroup.subgroupSchemeι (specialLinearIdeal n k)))

variable {n k}

/-- An invertible matrix satisfies the equations of `SL_n` if and only if its determinant is
`1`. -/
theorem mem_zeroLocus_specialLinearIdeal_iff {R : Type u} [CommRing R] [Algebra k R]
    {g : GL n R} : g ∈ zeroLocus (specialLinearIdeal n k) R ↔
      Matrix.GeneralLinearGroup.det g = 1 := by
  rw [mem_zeroLocus]
  constructor
  · intro h
    have := h _ (Matrix.GeneralLinearGroup.detUnit_sub_one_mem_specialLinearIdeal n k)
    rw [map_sub, map_one, evalAlgHom_detUnit, sub_eq_zero] at this
    exact Units.ext this
  · intro h a ha
    have hle : specialLinearIdeal n k ≤ RingHom.ker (evalAlgHom (k := k) g) := by
      refine Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)
      change evalAlgHom g _ = 0
      rw [map_sub, map_one, evalAlgHom_detUnit, h, Units.val_one, sub_self]
    exact hle ha

/-- The `R`-points of `𝕊𝕃(n; k)` are the invertible `n × n` matrices over `R` of determinant
`1`. -/
theorem range_homMulEquiv_comp_ι (R : Type u) [CommRing R] [Algebra k R] :
    Set.range (fun φ : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝕊𝕃(n; k) ↦
      GeneralLinearGroup.homMulEquiv n k R (φ ≫ ι n k)) =
        {g | Matrix.GeneralLinearGroup.det g = 1} := by
  ext g
  rw [Set.mem_setOf_eq, ← mem_zeroLocus_specialLinearIdeal_iff,
    ← GeneralLinearGroup.range_homMulEquiv_comp]
  rfl

end SpecialLinearGroup

end AlgebraicGeometry
