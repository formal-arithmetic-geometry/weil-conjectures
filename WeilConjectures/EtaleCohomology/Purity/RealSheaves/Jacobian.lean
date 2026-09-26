/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

/-!
# Jacobian torsion data

Let `C₀` be a proper smooth geometrically connected curve over a finite field `K = 𝔽_q` and let
`C = C₀ ×_K k` be its geometric base change, with `Γ = Gal(k / K)` acting on the Picard group
`Pic(C)` of line bundles up to isomorphism, written additively (tensor product of line bundles
is the addition).

A *Jacobian torsion datum* records the outcome of the theory of the Jacobian in exactly the
amount needed by the purity argument for real lisse sheaves: an abelian variety `J₀` over `K`
— a smooth proper geometrically connected commutative group scheme — together with
`Γ`-equivariant isomorphisms `J[ℓⁿ] ≃ Pic(C)[ℓⁿ]` matching multiplication by `ℓ` on the
torsion of `J` with the `ℓ`-th tensor power on line bundles. From the datum one reads off the
Tate module `T_ℓ J = lim_n J[ℓⁿ]`, and `V_ℓ J = T_ℓ J ⊗ ℚ_ℓ`.

Neither the Picard group of a scheme nor the Jacobian of a curve exists in Mathlib or in this
repository; both are owned by other blueprint blocks (`sk-def-av-pic`, `sk-def-av-jacobian`,
`sk-prop-jacobian-descent`). Accordingly `Pic` and the Galois group `Γ` are *parameters* of the
definition below: `Pic` is an arbitrary additive commutative group with a `Γ`-action, and its
`ℓⁿ`-torsion subgroup is the kernel of multiplication by `ℓⁿ`. Once the Jacobian is available
this definition becomes a theorem about it.

The abelian variety is packaged as a `CategoryTheory.GrpObj` on `Over (Spec K)`, commutative by
`CategoryTheory.IsCommMonObj`, as in `Mathlib/AlgebraicGeometry/Group/Abelian.lean`.

## Main definitions

- `AlgebraicGeometry.JacobianTorsionDatum`
- `AlgebraicGeometry.JacobianTorsionDatum.tateModule`
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint `sk-d-real-jacobian`: Jacobian torsion data and Kummer coefficients.

A Jacobian torsion datum for a proper smooth geometrically connected curve `p : C ⟶ Spec K`
over a finite field, a prime `l`, a group `Γ` (the Galois group of `k / K`) and a `Γ`-module
`Pic` (the Picard group of the geometric curve `C`, written additively) consists of an abelian
variety `J₀ = J` over `K`, that is a smooth proper geometrically connected commutative group
scheme, together with a compatible system of `Γ`-equivariant isomorphisms

`J[lⁿ] ≃ Pic[lⁿ] = ker (l ^ n • · : Pic → Pic)`

carrying multiplication by `l` on `J[l ^ (n + 1)] → J[lⁿ]` to the `l`-th tensor power on line
bundles, i.e. to multiplication by `l` on the additively written `Pic`.

The `lⁿ`-torsion of `J` is recorded as abstract `Γ`-modules `torsion n` rather than as
`ker (l ^ n : J(k) → J(k))`, because `k`-points of a group scheme carry no group structure in
Mathlib yet; `nsmul_torsion_eq_zero` records that `torsion n` is indeed killed by `lⁿ`. -/
structure JacobianTorsionDatum {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of K)) [IsProper p] [Smooth p] [GeometricallyConnected p]
    (l : ℕ) [Fact l.Prime] (Γ : Type u) [Group Γ]
    (Pic : Type u) [AddCommGroup Pic] [DistribMulAction Γ Pic] where
  /-- The underlying scheme of the abelian variety `J₀`. -/
  J : Scheme.{u}
  /-- The structure morphism `J₀ ⟶ Spec K` of the abelian variety. -/
  hom : J ⟶ Spec (.of K)
  /-- `J₀` is proper over `K`. -/
  [isProper : IsProper hom]
  /-- `J₀` is smooth over `K`. -/
  [smooth : Smooth hom]
  /-- `J₀` is geometrically connected over `K`. -/
  [geometricallyConnected : GeometricallyConnected hom]
  /-- `J₀` is a group scheme over `K`. -/
  [grpObj : GrpObj (Over.mk hom)]
  /-- The group law of `J₀` is commutative. -/
  [isCommMonObj : IsCommMonObj (Over.mk hom)]
  /-- The `lⁿ`-torsion `J[lⁿ] = ker (lⁿ : J₀(k) → J₀(k))` of the abelian variety. -/
  torsion : ℕ → Type u
  /-- Each `J[lⁿ]` is an abelian group. -/
  [addCommGroup (n : ℕ) : AddCommGroup (torsion n)]
  /-- Each `J[lⁿ]` carries an action of the Galois group `Γ`. -/
  [distribMulAction (n : ℕ) : DistribMulAction Γ (torsion n)]
  /-- `J[lⁿ]` is killed by `lⁿ`. -/
  nsmul_torsion_eq_zero (n : ℕ) (x : torsion n) : (l ^ n) • x = 0
  /-- Multiplication by `l`, viewed as the transition map `J[l ^ (n + 1)] → J[lⁿ]` of the
  inverse system defining the Tate module. -/
  transition (n : ℕ) : torsion (n + 1) →+ torsion n
  /-- The transition maps are Galois-equivariant. -/
  transition_smul (n : ℕ) (g : Γ) (x : torsion (n + 1)) :
    transition n (g • x) = g • transition n x
  /-- The comparison isomorphism `J[lⁿ] ≃ Pic(C)[lⁿ]` with the `lⁿ`-torsion of the Picard
  group of the geometric curve. -/
  equivTorsion (n : ℕ) : torsion n ≃+ (nsmulAddMonoidHom (α := Pic) (l ^ n)).ker
  /-- The comparison isomorphisms are Galois-equivariant. -/
  equivTorsion_smul (n : ℕ) (g : Γ) (x : torsion n) :
    (equivTorsion n (g • x) : Pic) = g • (equivTorsion n x : Pic)
  /-- The comparison isomorphisms match multiplication by `l` on the torsion of `J₀` with the
  `l`-th tensor power of line bundles. -/
  equivTorsion_transition (n : ℕ) (x : torsion (n + 1)) :
    (equivTorsion n (transition n x) : Pic) = l • (equivTorsion (n + 1) x : Pic)

attribute [instance] JacobianTorsionDatum.isProper JacobianTorsionDatum.smooth
  JacobianTorsionDatum.geometricallyConnected JacobianTorsionDatum.grpObj
  JacobianTorsionDatum.isCommMonObj JacobianTorsionDatum.addCommGroup
  JacobianTorsionDatum.distribMulAction

namespace JacobianTorsionDatum

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)}
  [IsProper p] [Smooth p] [GeometricallyConnected p] {l : ℕ} [Fact l.Prime] {Γ : Type u}
  [Group Γ] {Pic : Type u} [AddCommGroup Pic] [DistribMulAction Γ Pic]

/-- Blueprint `sk-d-real-jacobian`: Jacobian torsion data and Kummer coefficients.

The Tate module `T_l J = lim_n J[lⁿ]` of a Jacobian torsion datum, realised concretely as the
subgroup of the product `∀ n, J[lⁿ]` consisting of the compatible systems, i.e. those families
`f` with `transition n (f (n + 1)) = f n` for all `n`.

Inverting `l` gives `V_l J = T_l J ⊗ ℚ_l`, the `l`-adic homology of the curve. -/
def tateModule (d : JacobianTorsionDatum p l Γ Pic) : AddSubgroup (∀ n, d.torsion n) where
  carrier := {f | ∀ n, d.transition n (f (n + 1)) = f n}
  zero_mem' n := by simp
  add_mem' ha hb n := by simp [ha n, hb n]
  neg_mem' ha n := by simp [ha n]

end JacobianTorsionDatum

end AlgebraicGeometry
