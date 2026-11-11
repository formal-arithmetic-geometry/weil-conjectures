/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.JacobianKummer
public import WeilConjectures.GroupTheory.TorsionInverseLimit

/-!
# The inverse limit of `H¹(C, μ_{lⁿ})` and the Tate module of the Jacobian

Let `C₀` be a proper smooth geometrically integral curve over a finite field `K`, `C` its
geometric fiber and `l` a prime invertible in `K`. The isomorphisms
`H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` of a Jacobian torsion datum
(`AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv`) match the transition maps
`μ_{lⁿ⁺¹} ⟶ μ_{lⁿ}`, `z ↦ z ^ l`, with multiplication by `l`, so they pass to the limit: they
identify `lim_n H¹(C, μ_{lⁿ})` with the Tate module `T_l J₀`, as `ℤ_l`-modules with Galois
action.

## Main definitions

- `AlgebraicGeometry.Scheme.h1RootsOfUnityLimit`: the inverse limit `lim_n H¹(X, μ_{lⁿ})`.
- `AlgebraicGeometry.JacobianTorsionDatum.kummerTateEquiv`: `lim_n H¹(C, μ_{lⁿ}) ≅ T_l J₀`.

## Main statements

- `AlgebraicGeometry.JacobianTorsionDatum.kummerTateEquiv_restrictMuH`: Galois equivariance.
-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

namespace Scheme

/-- The inverse limit `lim_n H¹(X, μ_{lⁿ})` along the maps induced by the transition maps
`μ_{lⁿ⁺¹} ⟶ μ_{lⁿ}`, `z ↦ z ^ l`, as a `ℤ_l`-module
(`AddCommGroup.torsionInverseLimit`). It consists of the compatible families whose `n`-th
term is killed by `lⁿ`; this torsion condition holds for every compatible family, since
`H¹(X, μ_{lⁿ})` is killed by `lⁿ`. -/
noncomputable abbrev h1RootsOfUnityLimit (X : Scheme.{u}) (l : ℕ) :
    AddSubgroup (∀ n : ℕ, Sheaf.H (X.rootsOfUnitySheaf (l ^ n)) 1) :=
  AddCommGroup.torsionInverseLimit l fun n ↦
    Sheaf.H.map (X.rootsOfUnityPowMap l (pow_succ l n).symm) 1

end Scheme

namespace JacobianTorsionDatum

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [Smooth p] [IsProper p] [GeometricallyIntegral p] {l : ℕ} [Fact l.Prime]

/-- Blueprint `proposition-h-1-curve-tate-module--2`: the isomorphisms
`H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` of a Jacobian torsion datum
(`AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv`) induce a `ℤ_l`-linear isomorphism

`lim_n H¹(C, μ_{lⁿ}) ≃ T_l J₀`

between the inverse limit of the cohomology groups along `z ↦ z ^ l` and the Tate module of the
Jacobian, acting coordinatewise. It is Galois-equivariant
(`AlgebraicGeometry.JacobianTorsionDatum.kummerTateEquiv_restrictMuH`). -/
noncomputable def kummerTateEquiv (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0) :
    p.geometricFiber.h1RootsOfUnityLimit l ≃ₗ[ℤ_[l]] d.tateModule l where
  toFun x := ⟨fun n ↦ (d.kummerEquiv hl n (x.1 n) :
      Additive (Scheme.specAlgebraicClosure K ⟶ d.J)),
    fun n ↦ (d.kummerEquiv hl n _).2, fun n ↦ by
      rw [← kummerEquiv_map_rootsOfUnityPowMap,
        AddCommGroup.torsionInverseLimit.map_coe_succ x n]⟩
  invFun t := ⟨fun n ↦ (d.kummerEquiv hl n).symm
      ⟨_, AddCommGroup.tateModule.pow_zsmul_coe t n⟩, fun n ↦ by
      rw [← map_zsmul]
      refine ((d.kummerEquiv hl n).symm.map_eq_zero_iff).2 (Subtype.ext ?_)
      exact AddCommGroup.tateModule.pow_zsmul_coe t n, fun n ↦ by
      apply (d.kummerEquiv hl n).injective
      apply Subtype.ext
      dsimp only
      rw [kummerEquiv_map_rootsOfUnityPowMap, AddEquiv.apply_symm_apply,
        AddEquiv.apply_symm_apply]
      exact AddCommGroup.tateModule.zsmul_coe_succ t n⟩
  left_inv x := Subtype.ext <| funext fun n ↦ by
    simp
  right_inv t := Subtype.ext <| funext fun n ↦ by
    simp
  map_add' x y := Subtype.ext <| funext fun n ↦ by
    simp
  map_smul' a x := Subtype.ext <| funext fun n ↦ by
    change (d.kummerEquiv hl n ((a.appr n : ℤ) • x.1 n) :
      Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) = (a.appr n : ℤ) • _
    rw [map_zsmul]
    rfl

lemma coe_kummerTateEquiv_apply (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0)
    (x : p.geometricFiber.h1RootsOfUnityLimit l) (n : ℕ) :
    ((d.kummerTateEquiv hl x : d.tateModule l) :
        ∀ _ : ℕ, Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) n =
      d.kummerEquiv hl n (x.1 n) :=
  rfl

/-- The Galois action on `lim_n H¹(C, μ_{lⁿ})`: restricting a compatible family levelwise
along the automorphism `σ_C = 𝟙 × Spec σ` of `C` gives a compatible family. -/
lemma restrictMuH_mem_h1RootsOfUnityLimit (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0)
    (σ : Gal(AlgebraicClosure K/K)) (x : p.geometricFiber.h1RootsOfUnityLimit l) :
    (fun n ↦ Scheme.restrictMuH (p.geometricFiberGaloisMap σ.toAlgHom) (l ^ n) 1 (x.1 n))
      ∈ p.geometricFiber.h1RootsOfUnityLimit l := by
  refine ⟨fun n ↦ ?_, fun n ↦ ?_⟩
  · rw [← map_zsmul, AddCommGroup.torsionInverseLimit.pow_zsmul_coe x n, map_zero]
  · apply (d.kummerEquiv hl n).injective
    apply Subtype.ext
    rw [kummerEquiv_map_rootsOfUnityPowMap, kummerEquiv_restrictMuH, kummerEquiv_restrictMuH,
      ← map_zsmul, ← kummerEquiv_map_rootsOfUnityPowMap,
      AddCommGroup.torsionInverseLimit.map_coe_succ x n]

/-- Blueprint `proposition-h-1-curve-tate-module--2`: the isomorphism
`lim_n H¹(C, μ_{lⁿ}) ≃ T_l J₀` (`AlgebraicGeometry.JacobianTorsionDatum.kummerTateEquiv`) is
Galois-equivariant: if the family `y` is obtained from `x` by restriction along the automorphism
`σ_C = 𝟙 × Spec σ` of `C` in each level (which yields a compatible family by
`AlgebraicGeometry.JacobianTorsionDatum.restrictMuH_mem_h1RootsOfUnityLimit`), then the image
of `y` is the image of `x` under the Galois representation of `σ` on `T_l J₀`. -/
theorem kummerTateEquiv_restrictMuH (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0)
    (σ : Gal(AlgebraicClosure K/K)) (x y : p.geometricFiber.h1RootsOfUnityLimit l)
    (hxy : ∀ n, y.1 n =
      Scheme.restrictMuH (p.geometricFiberGaloisMap σ.toAlgHom) (l ^ n) 1 (x.1 n)) :
    d.kummerTateEquiv hl y =
      IsAbelianVariety.galoisRepresentation l d.J σ (d.kummerTateEquiv hl x) :=
  Subtype.ext <| funext fun n ↦ by
    rw [coe_kummerTateEquiv_apply, IsAbelianVariety.coe_galoisRepresentation_apply,
      coe_kummerTateEquiv_apply, hxy n, kummerEquiv_restrictMuH]

end JacobianTorsionDatum

end AlgebraicGeometry
