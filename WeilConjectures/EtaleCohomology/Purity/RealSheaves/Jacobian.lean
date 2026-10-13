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


/-- Blueprint `lem-wf-finite-field-tate-no-fixed`: arithmetic Frobenius has no fixed vector on
the Jacobian Tate module, on the rational Tate module.

Let `d` be a Jacobian torsion datum of a proper smooth geometrically integral curve `C₀` over a
finite field `K`, with abelian variety `J₀`. The arithmetic Frobenius `σ : z ↦ z ^ q` of
`Gal(K̄ / K)`, acting on `J₀(K̄)` by coordinates, fixes no nonzero vector of `V_l J`: its fixed
points on `J₀(K̄)` are the finitely many rational points `J₀(K)`
(`AlgebraicGeometry.IsAbelianVariety.finite_setOf_frobenius_fixed`), so this is
`AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self`. In other words `σ - 1` is injective
on `V_l J`. -/
theorem eq_zero_of_map_frobenius_eq_self [Fintype K] (d : JacobianTorsionDatum p l)
    {v : IsAbelianVariety.rationalTateModule l d.J}
    (hv : AddCommGroup.rationalTateModule.map (IsAbelianVariety.geometricPointsAddEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))).toAddMonoidHom v = v) :
    v = 0 :=
  AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self _
    (IsAbelianVariety.finite_setOf_frobenius_fixed d.J) hv

/-- Blueprint `lem-wf-finite-field-tate-no-fixed`: arithmetic Frobenius has no fixed vector on
the Jacobian Tate module.

Let `C₀` be a proper smooth geometrically integral curve over a finite field `K`, `C` its
geometric fibre and `l` a prime. The arithmetic Frobenius `σ : z ↦ z ^ q` of `Gal(K̄ / K)` acts
on `Pic(C)` by pullback of line bundles along `𝟙 × Spec σ`; on the Tate module
`T_l Pic(C) = T_l J` it has no nonzero fixed vector. Indeed a Jacobian torsion datum
(`AlgebraicGeometry.JacobianTorsionDatum.nonempty`) identifies `Pic(C)[lⁿ]` with `J₀(K̄)[lⁿ]`
compatibly with `σ` (`AlgebraicGeometry.JacobianTorsionDatum.equivTorsion_galois`) and with the
transition maps, and `σ` has only the finitely many fixed points `J₀(K)` on `J₀(K̄)`
(`AlgebraicGeometry.IsAbelianVariety.finite_setOf_frobenius_fixed`), so this is
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.eq_zero_of_mem_tateModule_pic_of_forall_frobenius
    [Fintype K] [SmoothOfRelativeDimension 1 p] {t : ℕ → Additive p.geometricFiber.Pic}
    (ht : t ∈ AddCommGroup.tateModule l (Additive p.geometricFiber.Pic))
    (hfix : ∀ n, Additive.ofMul (Scheme.Pic.map (p.geometricFiberGaloisMap
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toAlgHom)
        (t n).toMul) = t n) :
    t = 0 := by
  obtain ⟨d⟩ := JacobianTorsionDatum.nonempty p l
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)
  let M := Additive (Scheme.specAlgebraicClosure K ⟶ d.J)
  let N := Additive p.geometricFiber.Pic
  let t' : AddCommGroup.tateModule l N := ⟨t, ht⟩
  have hN (n : ℕ) : t n ∈ AddSubgroup.torsionBy N ((l : ℤ) ^ n) :=
    AddCommGroup.tateModule.pow_zsmul_coe t' n
  let s (n : ℕ) : M := (d.equivTorsion n).symm ⟨t n, hN n⟩
  have hs (n : ℕ) : s n ∈ AddSubgroup.torsionBy M ((l : ℤ) ^ n) :=
    ((d.equivTorsion n).symm ⟨t n, hN n⟩).2
  have hsT : s ∈ AddCommGroup.tateModule l M := ⟨hs, fun n ↦ by
    have h := d.equivTorsion_symm_zsmul n ⟨t (n + 1), hN (n + 1)⟩
    rw [show (⟨(l : ℤ) • t (n + 1), AddSubgroup.zsmul_mem_torsionBy_pow (hN (n + 1))⟩ :
        AddSubgroup.torsionBy N ((l : ℤ) ^ n)) = ⟨t n, hN n⟩ from
      Subtype.ext (AddCommGroup.tateModule.zsmul_coe_succ t' n)] at h
    exact h.symm⟩
  have hsfix (n : ℕ) : IsAbelianVariety.geometricPointsAddEquiv σ (s n) = s n := by
    have h := d.equivTorsion_galois n σ ⟨s n, hs n⟩
    have h' : d.equivTorsion n ⟨IsAbelianVariety.geometricPointsAddEquiv σ (s n),
        AddSubgroup.apply_mem_torsionBy (IsAbelianVariety.geometricPointsAddEquiv σ) (hs n)⟩ =
          d.equivTorsion n ⟨s n, hs n⟩ := by
      have hst : d.equivTorsion n ⟨s n, hs n⟩ = ⟨t n, hN n⟩ :=
        (d.equivTorsion n).apply_symm_apply ⟨t n, hN n⟩
      refine Subtype.ext ?_
      rw [h, hst]
      exact hfix n
    exact congrArg Subtype.val ((d.equivTorsion n).injective h')
  have h0 := AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed _
    (IsAbelianVariety.finite_setOf_frobenius_fixed d.J) hsT hsfix
  funext n
  have hsn : s n = 0 := congrFun h0 n
  have := (d.equivTorsion n).apply_symm_apply ⟨t n, hN n⟩
  rw [show (d.equivTorsion n).symm ⟨t n, hN n⟩ = 0 from Subtype.ext hsn, map_zero] at this
  exact (congrArg Subtype.val this).symm
end JacobianTorsionDatum

/-! ### The Galois action on the geometric Jacobian -/

namespace Scheme.Hom

variable {Y₀ : Scheme.{u}} (g : Y₀ ⟶ Spec (.of K))

/-- The Galois action `σ ↦ 𝟙 × Spec σ` on a geometric fiber is contravariant, like
`σ ↦ Spec σ`. -/
lemma geometricFiberGaloisMap_comp (σ τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    g.geometricFiberGaloisMap (σ.comp τ) =
      g.geometricFiberGaloisMap σ ≫ g.geometricFiberGaloisMap τ :=
  geometricFiber_hom_ext g (by simp) (by simp [Scheme.specAlgebraicClosureMap_comp])

@[simp]
lemma geometricFiberGaloisMap_id :
    g.geometricFiberGaloisMap (AlgHom.id K (AlgebraicClosure K)) = 𝟙 _ :=
  geometricFiber_hom_ext g (by simp) (by
    rw [geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure,
      Scheme.specAlgebraicClosureMap_id, Over.id_left]
    exact Category.comp_id _)

end Scheme.Hom

variable (K) in
/-- Blueprint `lem-wf-geometric-jacobian-galois-action`: Canonical semilinear Galois action on
the geometric Jacobian.

Let `C₀` be a smooth proper geometrically connected curve over a perfect field `K` (given by
`p : C₀ ⟶ Spec K`) and `C = C₀ ×_K K̄` its geometric fiber. There is an abelian variety
(a commutative group scheme) `J₀` over `K` representing `Pic⁰_{C₀/K}` whose base change
`J = J₀ ×_K K̄` (`J₀.hom.geometricFiber`) represents `Pic⁰_{C/K̄}`, i.e. is the Jacobian of `C`.
For `σ ∈ Gal(K̄ / K)` the automorphism `σ_J = 𝟙 × Spec σ` of `J`
(`J₀.hom.geometricFiberGaloisMap σ`) lies over `Spec σ`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure`),
is compatible with the group law (it is a base change of the identity of `J₀`), and
`σ ↦ σ_J` is an action (`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap_comp`,
`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap_id`). On the geometric points
`J(K̄) = J₀(K̄) = (Spec K̄ ⟶ J₀)` it acts by coordinates, `x ↦ Spec σ ≫ x`.

The statement records the content used later: the identification `φ : J₀(K̄) ≅ Pic⁰(C)` is an
injective group homomorphism into `Pic(C)` whose image contains all torsion (torsion line bundles
have degree zero), and it is Galois equivariant: `φ (Spec σ ≫ x) = σ_C^* (φ x)` for the action
`σ_C = 𝟙 × Spec σ` of `σ` on `C`. In particular `J₀[ℓⁿ](K̄) ≅ Pic⁰(C)[ℓⁿ]` is equivariant for
every `ℓ` and `n`. -/
theorem exists_jacobian_galoisAction [PerfectField K] (p : C ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 p]
    [IsProper p] [GeometricallyConnected p] :
    ∃ (J₀ : Over (Spec (.of K))) (_ : CommGrpObj J₀)
      (_ : (picardFunctorDegree p 0).obj.RepresentableBy J₀)
      (φ : (Scheme.specAlgebraicClosure K ⟶ J₀) →* p.geometricFiber.Pic),
      Nonempty ((picardFunctorDegree p.geometricFiberToAlgebraicClosure 0).obj.RepresentableBy
        (Over.mk J₀.hom.geometricFiberToAlgebraicClosure)) ∧
      Function.Injective φ ∧
      (∀ (n : ℕ) (L : p.geometricFiber.Pic), n ≠ 0 → L ^ n = 1 → L ∈ φ.range) ∧
      ∀ (σ : Gal(AlgebraicClosure K/K)) (x : Scheme.specAlgebraicClosure K ⟶ J₀),
        φ (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x) =
          Scheme.Pic.map (p.geometricFiberGaloisMap σ.toAlgHom) (φ x) := by
  let _ : C.Over (Spec (.of K)) := ⟨p⟩
  let _ : p.geometricFiber.Over (Spec (.of (AlgebraicClosure K))) :=
    ⟨p.geometricFiberToAlgebraicClosure⟩
  have : SmoothOfRelativeDimension 1 (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd p _))
  have : IsProper (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (IsProper (pullback.snd p _))
  have : GeometricallyConnected (C ↘ Spec (.of K)) := ‹GeometricallyConnected p›
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of K)) := ‹SmoothOfRelativeDimension 1 p›
  have : IsProper (C ↘ Spec (.of K)) := ‹IsProper p›
  obtain ⟨J₀, _, r, -, -, -, -, ⟨rK⟩, e, he⟩ := exists_jacobian_descent K (AlgebraicClosure K)
    (AlgebraicClosure K) C _ rfl p.geometricFiber p.geometricFiberProj
    (IsPullback.of_hasPullback _ _)
  let φ : (Scheme.specAlgebraicClosure K ⟶ J₀) →* p.geometricFiber.Pic :=
    (picardZero (AlgebraicClosure K) p.geometricFiber).subtype.comp e.symm.toMonoidHom
  refine ⟨J₀, inferInstance, r, φ, ⟨rK⟩, ?_, fun n L hn hL ↦ ?_, fun σ x ↦ ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · -- a torsion line bundle has degree zero
    have hL0 : L ∈ picardZero (AlgebraicClosure K) p.geometricFiber := by
      rw [MonoidHom.mem_ker]
      have h := congrArg (fun z ↦ (Scheme.picDegreeHom (AlgebraicClosure K)
        p.geometricFiber z).toAdd) hL
      simp only [map_pow, toAdd_pow, map_one, toAdd_one] at h
      rw [← ofAdd_toAdd (Scheme.picDegreeHom _ _ _), ofAdd_eq_one]
      exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hn)
    exact ⟨e ⟨L, hL0⟩, by
      change ((e.symm (e ⟨L, hL0⟩) : picardZero (AlgebraicClosure K) p.geometricFiber) :
        p.geometricFiber.Pic) = L
      rw [MulEquiv.symm_apply_apply]⟩
  · obtain ⟨γ, hγ₁, hγ₂, act, hact₁, hact₂⟩ := he σ
    have hγ : γ = p.geometricFiberGaloisMap σ.toAlgHom :=
      Scheme.Hom.geometricFiber_hom_ext p (by simpa using hγ₁) (by
        rw [Scheme.Hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure]
        exact hγ₂)
    have hx : e (act (e.symm x)) = specAlgEquivOver σ ≫ e (e.symm x) := hact₂ (e.symm x)
    rw [MulEquiv.apply_symm_apply, ← MulEquiv.eq_symm_apply] at hx
    change ((e.symm (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x) :
      picardZero (AlgebraicClosure K) p.geometricFiber) : p.geometricFiber.Pic) = _
    rw [show Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x = specAlgEquivOver σ ≫ x from rfl,
      ← hx, hact₁, hγ]
    rfl

end AlgebraicGeometry
