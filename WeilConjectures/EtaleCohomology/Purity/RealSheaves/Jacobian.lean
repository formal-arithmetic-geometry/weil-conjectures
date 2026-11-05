/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Set.Finite.Basic
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
`ℤ_l(1)` — consists of the transition maps `AlgebraicGeometry.Scheme.rootsOfUnityPowMap`; the
resulting identification `H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` is
`AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv`. The Tate twist itself is
`AlgebraicGeometry.WeilGroup.tateLine`.

## Main definitions

- `AlgebraicGeometry.JacobianTorsionDatum`
- `AlgebraicGeometry.JacobianTorsionDatum.tateModule`

## Main statements

- `AlgebraicGeometry.JacobianTorsionDatum.nonempty_tateModuleEquiv`
- `AlgebraicGeometry.exists_jacobian_galoisAction`: the semilinear Galois action on the geometric
  Jacobian, preserving the group law (blueprint `lem-wf-geometric-jacobian-galois-action`).
- `AlgebraicGeometry.JacobianTorsionDatum.exists_equivTorsion_eq_restrict`: a Jacobian torsion
  datum whose comparison isomorphisms are induced by the representing isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `sk-d-real-jacobian`: Jacobian torsion data and Kummer coefficients.

A Jacobian torsion datum for a proper smooth geometrically integral curve `p : C₀ ⟶ Spec K`
over a finite field and a prime `l` consists of an abelian variety `J₀` over `K` representing the
degree-zero relative Picard functor `Pic⁰_{C₀/K}` (blueprint `def-sc-jacobian`), together with
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

variable (p l) in
/-- Blueprint `sk-prop-jacobian-descent`: The Jacobian over a general base field, by Galois
descent.

Every proper smooth geometrically connected curve over a finite field admits a Jacobian torsion
datum: the descended Jacobian `J₀` of `AlgebraicGeometry.exists_jacobian_descent` with its
Galois-equivariant identification `J₀(K̄) ≅ Pic⁰(C)`, restricted to `lⁿ`-torsion, which lies in
`Pic⁰(C)`. -/
theorem nonempty [SmoothOfRelativeDimension 1 p] : Nonempty (JacobianTorsionDatum p l) := by
  let _ : C.Over (Spec (.of K)) := ⟨p⟩
  let _ : p.geometricFiber.Over (Spec (.of (AlgebraicClosure K))) :=
    ⟨p.geometricFiberToAlgebraicClosure⟩
  have : SmoothOfRelativeDimension 1 (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd p _))
  have : IsProper (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (IsProper (pullback.snd p _))
  have : GeometricallyConnected (C ↘ Spec (.of K)) := .of_geometricallyIrreducible p
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of K)) := ‹SmoothOfRelativeDimension 1 p›
  have : IsProper (C ↘ Spec (.of K)) := ‹IsProper p›
  obtain ⟨J₀, _, r, hP, hS, hG, -, -, e₀, -, he⟩ := exists_jacobian_descent K (AlgebraicClosure K)
    (AlgebraicClosure K) C _ rfl p.geometricFiber p.geometricFiberProj
    (IsPullback.of_hasPullback _ _)
  have : Smooth J₀.hom := SmoothOfRelativeDimension.smooth (Scheme.arithmeticGenus K C) _
  have : IrreducibleSpace J₀.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    (f := J₀.hom)
  have hJ : IsAbelianVariety J₀ := ⟨⟩
  let e : picardZero (AlgebraicClosure K) p.geometricFiber ≃*
      (Scheme.specAlgebraicClosure K ⟶ J₀) := e₀
  -- the torsion of `Pic(C)` lies in `Pic⁰(C)`
  have hdeg (n : ℕ) (y : Additive p.geometricFiber.Pic) (hy : ((l : ℤ) ^ n) • y = 0) :
      y.toMul ∈ picardZero (AlgebraicClosure K) p.geometricFiber := by
    rw [MonoidHom.mem_ker]
    have h := congrArg
      (fun z ↦ (Scheme.picDegreeHom (AlgebraicClosure K) p.geometricFiber z.toMul).toAdd) hy
    simp only [toMul_zsmul, map_zpow, toAdd_zpow, toMul_zero, map_one, toAdd_one] at h
    rw [← ofAdd_toAdd (Scheme.picDegreeHom _ _ _), ofAdd_eq_one]
    exact (mul_eq_zero.1 h).resolve_left
      (pow_ne_zero n (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  -- `e⁻¹ : J₀(K̄) ≃ Pic⁰(C) ⊆ Pic(C)` commutes with integer multiples
  have hzsmul (x : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) (k : ℤ) :
      (k • Additive.ofMul ((e.symm (Additive.toMul x) :
        picardZero (AlgebraicClosure K) p.geometricFiber) : p.geometricFiber.Pic)) =
      Additive.ofMul ((e.symm (Additive.toMul (k • x)) :
        picardZero (AlgebraicClosure K) p.geometricFiber) : p.geometricFiber.Pic) := by
    simp [toMul_zsmul, map_zpow]
  let eT (n : ℕ) :
      AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) ((l : ℤ) ^ n) ≃+
        AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ n) :=
    { toFun x := ⟨.ofMul (e.symm x.1.toMul : p.geometricFiber.Pic), by
        change ((l : ℤ) ^ n) • (Additive.ofMul _ : Additive p.geometricFiber.Pic) = 0
        rw [hzsmul,
          show ((l : ℤ) ^ n) • (x : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) = 0 from x.2]
        simp⟩
      invFun y := ⟨.ofMul (e ⟨y.1.toMul, hdeg n y.1 y.2⟩), by
        change ((l : ℤ) ^ n) •
          (Additive.ofMul _ : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) = 0
        rw [← ofMul_zpow, ← map_zpow]
        have : (⟨y.1.toMul, hdeg n y.1 y.2⟩ :
            picardZero (AlgebraicClosure K) p.geometricFiber) ^ ((l : ℤ) ^ n) = 1 :=
          Subtype.ext (by
            have h := congrArg Additive.toMul
              (show ((l : ℤ) ^ n) • (y : Additive p.geometricFiber.Pic) = 0 from y.2)
            rw [toMul_zsmul, toMul_zero] at h
            simpa only [SubgroupClass.coe_zpow, OneMemClass.coe_one] using h)
        rw [this, map_one, ofMul_one]⟩
      left_inv x := Subtype.ext (by simp)
      right_inv y := Subtype.ext (by simp)
      map_add' x y := Subtype.ext (by simp) }
  refine ⟨@JacobianTorsionDatum.mk _ _ _ _ p _ _ _ _ l _ J₀ _ hJ r eT ?_ ?_⟩
  · intro n σ x
    obtain ⟨γ, hγ₁, hγ₂, act, hact₁, hact₂⟩ := he σ
    have hγ : γ = p.geometricFiberGaloisMap σ.toAlgHom :=
      Scheme.Hom.geometricFiber_hom_ext p (by simpa using hγ₁) (by
        rw [Scheme.Hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure]
        exact hγ₂)
    have hx : e (act (e.symm x.1.toMul)) = specAlgEquivOver σ ≫ e (e.symm x.1.toMul) :=
      hact₂ (e.symm x.1.toMul)
    rw [MulEquiv.apply_symm_apply, ← MulEquiv.eq_symm_apply] at hx
    change Additive.ofMul (e.symm (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x.1.toMul) :
      p.geometricFiber.Pic) = _
    rw [show Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x.1.toMul =
      specAlgEquivOver σ ≫ x.1.toMul from rfl, ← hx, hact₁, hγ]
    rfl
  · intro n x
    change Additive.ofMul (e.symm (Additive.toMul ((l : ℤ) •
        (x : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)))) : p.geometricFiber.Pic) =
      (l : ℤ) • Additive.ofMul (e.symm x.1.toMul : p.geometricFiber.Pic)
    rw [hzsmul]

end JacobianTorsionDatum

/-! ### The Galois action on the geometric Jacobian -/

namespace Scheme.Hom

variable {Y₀ : Scheme.{u}} (g : Y₀ ⟶ Spec (.of K))

@[simp]
lemma geometricFiberGaloisMap_id :
    g.geometricFiberGaloisMap (AlgHom.id K (AlgebraicClosure K)) = 𝟙 _ :=
  geometricFiber_hom_ext g (by simp) (by
    rw [geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure,
      Scheme.specAlgebraicClosureMap_id, Over.id_left]
    exact Category.comp_id _)

end Scheme.Hom

namespace Scheme

variable (A : Over (Spec (.of K))) [GrpObj A]

end Scheme

namespace JacobianTorsionDatum

variable [Finite K] {p : C ⟶ Spec (.of K)} [IsCurve p] [Smooth p] [IsProper p]
  [GeometricallyIntegral p] {l : ℕ} [Fact l.Prime]

end JacobianTorsionDatum

end AlgebraicGeometry
