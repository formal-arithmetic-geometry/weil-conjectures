/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.GroupTheory.TateModule
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic

/-!
# Jacobian torsion data

Let `C₀` be a proper smooth geometrically integral curve over a finite field `K = 𝔽_q` and let
`C = C₀ ×_K K̄` be its geometric fiber (`AlgebraicGeometry.Scheme.Hom.geometricFiber`), with
`Γ = Gal(K̄ / K)` acting on the Picard group `Pic(C)` by pulling back line bundles along the
automorphisms `𝟙 × Spec σ` of `C` (`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap`).

A *Jacobian torsion datum* records the outcome of the theory of the Jacobian in exactly the
amount needed by the purity argument for real lisse sheaves: an abelian variety `J₀` over `K`
(`AlgebraicGeometry.IsAbelianVariety`, which by `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`
is automatically commutative) representing the degree-zero Picard functor `Pic⁰_{C₀/K}`,
together with `Γ`-equivariant isomorphisms `J₀(K̄)[ℓⁿ] ≃ Pic(C)[ℓⁿ]` matching multiplication by
`ℓ` on the torsion of `J₀` with the `ℓ`-th tensor power of line bundles. Here `J₀(K̄)` is the
group `Additive (Spec K̄ ⟶ J₀)` of geometric points of `J₀`, with `Γ` acting by coordinates
(`AlgebraicGeometry.IsAbelianVariety.geometricPointsAddEquiv`), and `Pic(C)` is
`AlgebraicGeometry.Scheme.Pic` with the tensor product as group law, written additively. From
the datum one reads off the Tate module `T_ℓ J = lim_n J[ℓⁿ]`
(`AlgebraicGeometry.IsAbelianVariety.tateModule`) and its identification with the Tate module of
`Pic(C)` (`AlgebraicGeometry.JacobianTorsionDatum.nonempty_tateModuleEquiv`).

The Kummer half of blueprint `sk-d-real-jacobian` — the system `(μ_{lⁿ}, z ↦ z ^ l)` defining
`ℤ_l(1)` — is not here: the sheaf of roots of unity and the Kummer sequence belong to the
`sec-kummer` block. The Tate twist itself is `AlgebraicGeometry.WeilGroup.tateLine`.

## Main definitions

- `AlgebraicGeometry.JacobianTorsionDatum`
- `AlgebraicGeometry.JacobianTorsionDatum.tateModule`

## Main statements

- `AlgebraicGeometry.JacobianTorsionDatum.nonempty_tateModuleEquiv`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `sk-d-real-jacobian`: Jacobian torsion data and Kummer coefficients.

A Jacobian torsion datum for a proper smooth geometrically integral curve `p : C₀ ⟶ Spec K`
over a finite field and a prime `l` consists of an abelian variety `J₀` over `K` representing the
degree-zero relative Picard functor `Pic⁰_{C₀/K}` (blueprint `sk-def-av-jacobian`), together with
a compatible system of isomorphisms

`J₀(K̄)[lⁿ] ≃ Pic(C)[lⁿ]`

between the `lⁿ`-torsion of the group of geometric points of `J₀` and that of the Picard group of
the geometric curve `C = C₀ ×_K K̄`, which are equivariant for `Gal(K̄ / K)` (acting on points
by coordinates and on line bundles by pullback along `𝟙 × Spec σ`) and carry multiplication by
`l` on `J₀(K̄)[l ^ (n + 1)] → J₀(K̄)[lⁿ]` to the `l`-th tensor power of line bundles. -/
structure JacobianTorsionDatum [Finite K] (p : C ⟶ Spec (.of K)) [IsCurve p] [Smooth p]
    [IsProper p] [GeometricallyIntegral p] (l : ℕ) [Fact l.Prime] where
  /-- The abelian variety `J₀`, as a scheme over `Spec K`. -/
  J : Over (Spec (.of K))
  /-- `J₀` is a group scheme over `K`. -/
  [grpObj : GrpObj J]
  /-- `J₀` is an abelian variety over `K`; commutativity of its group law is then automatic
  by `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`. -/
  [isAbelianVariety : IsAbelianVariety J]
  /-- `J₀` represents the degree-zero Picard functor `Pic⁰_{C₀/K}`: it is the Jacobian of
  `C₀`. -/
  representableBy : (picardFunctorDegree p 0).obj.RepresentableBy J
  /-- The comparison isomorphism `J₀(K̄)[lⁿ] ≃ Pic(C)[lⁿ]` with the `lⁿ`-torsion of the Picard
  group of the geometric curve. -/
  equivTorsion (n : ℕ) :
    AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J)) ((l : ℤ) ^ n) ≃+
      AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ n)
  /-- The comparison isomorphisms are Galois-equivariant: `σ ∈ Gal(K̄ / K)` acts on geometric
  points by coordinates and on line bundles by pullback along `𝟙 × Spec σ`. -/
  equivTorsion_galois (n : ℕ) (σ : Gal(AlgebraicClosure K/K))
    (x : AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J)) ((l : ℤ) ^ n)) :
    (equivTorsion n ⟨IsAbelianVariety.geometricPointsAddEquiv σ x,
        AddSubgroup.apply_mem_torsionBy (IsAbelianVariety.geometricPointsAddEquiv σ) x.2⟩ :
          Additive p.geometricFiber.Pic) =
      Additive.ofMul (Scheme.Pic.map (p.geometricFiberGaloisMap σ.toAlgHom)
        (equivTorsion n x : Additive p.geometricFiber.Pic).toMul)
  /-- The comparison isomorphisms match multiplication by `l` on the torsion of `J₀` with the
  `l`-th tensor power of line bundles, i.e. the square

  ```
      J[lⁿ⁺¹] ──equivTorsion (n+1)──▶ Pic[lⁿ⁺¹]
         │                                │
       l • ─                            l • ─
         ▼                                ▼
       J[lⁿ] ───equivTorsion n───────▶ Pic[lⁿ]
  ```

  commutes. -/
  equivTorsion_zsmul (n : ℕ)
    (x : AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J)) ((l : ℤ) ^ (n + 1))) :
    (equivTorsion n ⟨(l : ℤ) • (x : Additive (Scheme.specAlgebraicClosure K ⟶ J)),
        AddSubgroup.zsmul_mem_torsionBy_pow x.2⟩ : Additive p.geometricFiber.Pic) =
      (l : ℤ) • (equivTorsion (n + 1) x : Additive p.geometricFiber.Pic)

attribute [instance] JacobianTorsionDatum.grpObj JacobianTorsionDatum.isAbelianVariety

namespace JacobianTorsionDatum

variable [Finite K] {p : C ⟶ Spec (.of K)} [IsCurve p] [Smooth p] [IsProper p]
  [GeometricallyIntegral p] {l : ℕ} [Fact l.Prime]

variable (l) in
/-- Blueprint `sk-d-real-jacobian`: Jacobian torsion data and Kummer coefficients.

The Tate module `T_l J = lim_n J₀(K̄)[lⁿ]` of the abelian variety of a Jacobian torsion datum,
the compatible systems of `lⁿ`-torsion geometric points under multiplication by `l`
(`AlgebraicGeometry.IsAbelianVariety.tateModule`).

Inverting `l` gives `V_l J = T_l J ⊗ ℚ_l`, the `l`-adic homology of the curve. -/
noncomputable abbrev tateModule (d : JacobianTorsionDatum p l) :
    AddSubgroup (∀ _ : ℕ, Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) :=
  IsAbelianVariety.tateModule l d.J

/-- The comparison isomorphisms of a Jacobian torsion datum, inverted, are also compatible with
multiplication by `l`. -/
theorem equivTorsion_symm_zsmul (d : JacobianTorsionDatum p l) (n : ℕ)
    (y : AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ (n + 1))) :
    ((d.equivTorsion n).symm ⟨(l : ℤ) • (y : Additive p.geometricFiber.Pic),
        AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ :
          Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) =
      (l : ℤ) • ((d.equivTorsion (n + 1)).symm y :
        Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) := by
  set x := (d.equivTorsion (n + 1)).symm y
  have h := d.equivTorsion_zsmul n x
  rw [show d.equivTorsion (n + 1) x = y from (d.equivTorsion (n + 1)).apply_symm_apply y] at h
  have h' : (⟨(l : ℤ) • (y : Additive p.geometricFiber.Pic),
      AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ :
        AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ n)) =
      d.equivTorsion n ⟨_, AddSubgroup.zsmul_mem_torsionBy_pow x.2⟩ :=
    Subtype.ext h.symm
  rw [h', AddEquiv.symm_apply_apply]

/-- Blueprint `sk-d-real-jacobian`: Jacobian torsion data and Kummer coefficients.

The comparison isomorphisms `J₀(K̄)[lⁿ] ≃ Pic(C)[lⁿ]` are compatible with the transition maps,
so they identify the Tate module `T_l J` of the datum with the Tate module
`AddCommGroup.tateModule` of the Picard group of the geometric curve. This is the form in which
`T_l J` enters `sk-p-real-rankone`. -/
theorem nonempty_tateModuleEquiv (d : JacobianTorsionDatum p l) :
    Nonempty (d.tateModule l ≃+ AddCommGroup.tateModule l (Additive p.geometricFiber.Pic)) := by
  let M := Additive (Scheme.specAlgebraicClosure K ⟶ d.J)
  let N := Additive p.geometricFiber.Pic
  have hM (t : AddCommGroup.tateModule l M) (n : ℕ) :
      (t : ∀ _ : ℕ, M) n ∈ AddSubgroup.torsionBy M ((l : ℤ) ^ n) :=
    AddCommGroup.tateModule.pow_zsmul_coe t n
  have hN (t : AddCommGroup.tateModule l N) (n : ℕ) :
      (t : ∀ _ : ℕ, N) n ∈ AddSubgroup.torsionBy N ((l : ℤ) ^ n) :=
    AddCommGroup.tateModule.pow_zsmul_coe t n
  refine ⟨
    { toFun t := ⟨fun n ↦ (d.equivTorsion n ⟨_, hM t n⟩ : N),
        fun n ↦ (d.equivTorsion n _).2, fun n ↦ ?_⟩
      invFun t := ⟨fun n ↦ ((d.equivTorsion n).symm ⟨_, hN t n⟩ : M),
        fun n ↦ ((d.equivTorsion n).symm _).2, fun n ↦ ?_⟩
      left_inv t := Subtype.ext <| funext fun n ↦ by simp
      right_inv t := Subtype.ext <| funext fun n ↦ by simp
      map_add' s t := Subtype.ext <| funext fun n ↦ by
        change (d.equivTorsion n ⟨_, hM (s + t) n⟩ : N) =
          (d.equivTorsion n ⟨_, hM s n⟩ : N) + (d.equivTorsion n ⟨_, hM t n⟩ : N)
        rw [← AddSubgroup.coe_add, ← map_add]
        rfl }⟩
  · rw [← d.equivTorsion_zsmul n ⟨_, hM t (n + 1)⟩]
    congr 2
    exact Subtype.ext (AddCommGroup.tateModule.zsmul_coe_succ t n)
  · rw [← d.equivTorsion_symm_zsmul n ⟨_, hN t (n + 1)⟩]
    congr 2
    exact Subtype.ext (AddCommGroup.tateModule.zsmul_coe_succ t n)

variable (p l) in
/-- Blueprint `sk-prop-jacobian-descent`: The Jacobian over a general base field, by Galois
descent.

Every proper smooth geometrically connected curve over a finite field admits a Jacobian torsion
datum: the descended Jacobian `J₀` of `AlgebraicGeometry.exists_jacobian_descent` with its
Galois-equivariant identification `J₀(K̄) ≅ Pic⁰(C)`, restricted to `lⁿ`-torsion, which lies in
`Pic⁰(C)`. -/
theorem nonempty [SmoothOfRelativeDimension 1 p] : Nonempty (JacobianTorsionDatum p l) := by
  sorry

end JacobianTorsionDatum

end AlgebraicGeometry
