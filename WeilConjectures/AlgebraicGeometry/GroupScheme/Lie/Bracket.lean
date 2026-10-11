/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.LocalPoints
public import WeilConjectures.Mathlib.Algebra.DualNumber

/-!
# The bracket on the Lie algebra of a group scheme over a field

Let `G` be a group scheme over a field `k`. Its tangent vectors are the points `v` of `G` with
values in the dual numbers `k[ε]` reducing to the identity; such a point is determined by the
homomorphism `v^♯ : 𝒪_{G,1} → k[ε]`, `a ↦ a(1) + ε D_v(a)` on the local ring at the identity
(`AlgebraicGeometry.GrpObj.kerHom`). For an element `m` of square zero in the maximal ideal of a
local `k`-algebra `A` with residue field `k`, substituting `ε ↦ m` gives the point `v^{(m)}` of `G`
with values in `A`, with `(v^{(m)})^♯(a) = a(1) + m D_v(a)`.

All computations go through these points, using only that `G(A)` is a group functorially in `A`:

* the product `v^{(m)} w^{(n)}` has `(v^{(m)} w^{(n)})^♯ = a(1) + m D_v + n D_w + mn C(v, w)` for a
  fixed `C(v, w)`, the `εδ`-coefficient of `v_ε w_δ` over `k[ε][δ] = k[ε, δ]/(ε², δ²)`
  (`kerHom_tangentMap_mul_tangentMap`); in particular the group law on tangent vectors is the
  addition of the `D_v`;
* if `m` kills the maximal ideal, `u^{(m)}` is central and `(u^{(m)} q)^♯ = q^♯ + m D_u`
  (`kerHom_tangentMap_mul`);
* the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` is `[v, w]^{(εδ)}` for a unique tangent vector `[v, w]`, the
  *bracket* (`tangentBracket`), with `D_{[v, w]} = C(v, w) - C(w, v)`.

Substituting into the bracket gives `[v^{(m)}, w^{(n)}] = [v, w]^{(mn)}`. From this the bracket is
biadditive and alternating, and the Hall–Witt identity over `k[α][β][γ]` gives the Jacobi
identity.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt IsLocalRing
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k]

/-! ### Test rings -/

section TestRings

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The residue map `A[τ] → k`, `x + yτ ↦ π(x)`, of the dual numbers over a `k`-algebra with a
residue map `π`. -/
def dualAug (π : A →ₐ[k] k) : DualNumber A →ₐ[k] k :=
  π.comp (fstHom k A A)

instance (π : A →ₐ[k] k) [IsLocalHom π.toRingHom] : IsLocalHom (dualAug π).toRingHom := by
  have : IsLocalHom (fstHom k A A).toRingHom := ⟨fun _ ↦ isUnit_iff_isUnit_fst.mpr⟩
  exact RingHom.isLocalHom_comp π.toRingHom (fstHom k A A).toRingHom

@[simp]
theorem dualAug_apply (π : A →ₐ[k] k) (x : DualNumber A) : dualAug π x = π x.fst :=
  rfl

end TestRings

/-- The residue map of `k[ε]`. -/
abbrev aug₁ : DualNumber k →ₐ[k] k :=
  fstHom k k k

/-- The residue map of `k[ε][δ] = k[ε, δ]/(ε², δ²)`. -/
abbrev aug₂ : DualNumber (DualNumber k) →ₐ[k] k :=
  dualAug aug₁

/-- The element `ε` of `k[ε][δ]`. -/
abbrev eps₂ : DualNumber (DualNumber k) :=
  inl (inr 1)

/-- The element `δ` of `k[ε][δ]`. -/
abbrev del₂ : DualNumber (DualNumber k) :=
  inr 1

theorem eps₂_mul_self : (eps₂ : DualNumber (DualNumber k)) * eps₂ = 0 := by
  ext <;> simp

theorem del₂_mul_self : (del₂ : DualNumber (DualNumber k)) * del₂ = 0 := by
  ext <;> simp

theorem eps₂_mul_del₂_mul_self :
    (eps₂ * del₂ : DualNumber (DualNumber k)) * (eps₂ * del₂) = 0 := by
  ext <;> simp

@[simp]
theorem aug₂_eps₂ : aug₂ (eps₂ : DualNumber (DualNumber k)) = 0 := by
  simp

@[simp]
theorem aug₂_del₂ : aug₂ (del₂ : DualNumber (DualNumber k)) = 0 := by
  simp

/-- The `k`-algebra homomorphism `k[ε][δ] → A`, `ε ↦ m`, `δ ↦ n`, for elements of square zero. -/
def lift₂ {A : Type u} [CommRing A] [Algebra k A] (m n : A) (hm : m * m = 0) (hn : n * n = 0) :
    DualNumber (DualNumber k) →ₐ[k] A :=
  DualNumber.lift ⟨(DualNumber.liftElem m hm, n), hn, fun _ ↦ Commute.all _ _⟩

theorem lift₂_apply {A : Type u} [CommRing A] [Algebra k A] (m n : A) (hm : m * m = 0)
    (hn : n * n = 0) (x : DualNumber (DualNumber k)) :
    lift₂ m n hm hn x = DualNumber.liftElem m hm x.fst + DualNumber.liftElem m hm x.snd * n :=
  rfl

variable (G : Over (Spec (.of k))) [GrpObj G]

/-! ### Tangent vectors and their substitutions -/

variable {G}

/-- The `ε`-coefficient `D_v : 𝒪_{G,1} → k` of a tangent vector `v`, so that
`v^♯(a) = a(1) + ε D_v(a)`. -/
noncomputable def tangentCoeff (v : pointsKer G aug₁) (a : stalkOne G) : k :=
  (kerHom v a).snd

theorem kerHom_tangent (v : pointsKer G aug₁) (a : stalkOne G) :
    kerHom v a = inl (counit G a) + inr (tangentCoeff v a) := by
  ext
  · simpa using kerHom_apply_of_mem_ker v a
  · simp [tangentCoeff]

theorem tangent_ext {v w : pointsKer G aug₁} (h : ∀ a, tangentCoeff v a = tangentCoeff w a) :
    v = w :=
  kerHom_injective (RingHom.ext fun a ↦ by rw [kerHom_tangent, kerHom_tangent, h])

variable {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A] {π : A →ₐ[k] k}
  [IsLocalHom π.toRingHom]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem aug_comp_liftElem (m : A) (hm : m * m = 0) (hπ : π m = 0) :
    π.comp (DualNumber.liftElem m hm) = aug₁ := by
  ext
  simp [DualNumber.liftElem_apply, hπ]

/-- The point `v^{(m)}` of `G` with values in `A` obtained from a tangent vector `v` by the
substitution `ε ↦ m`, for `m` of square zero in the maximal ideal. -/
noncomputable def tangentMap (m : A) (hm : m * m = 0) (hπ : π m = 0) :
    pointsKer G aug₁ →* pointsKer G π :=
  kerMap (DualNumber.liftElem m hm) (aug_comp_liftElem m hm hπ)

theorem kerHom_tangentMap (m : A) (hm : m * m = 0) (hπ : π m = 0) (v : pointsKer G aug₁)
    (a : stalkOne G) :
    kerHom (tangentMap m hm hπ v) a =
      algebraMap k A (counit G a) + algebraMap k A (tangentCoeff v a) * m := by
  rw [tangentMap, kerHom_kerMap]
  simp [kerHom_tangent, DualNumber.liftElem_apply]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem liftElem_comp_eq {B : Type u} [CommRing B] [Algebra k B] (ψ : A →ₐ[k] B) (m : A)
    (hm : m * m = 0) (m' : B) (hm' : m' * m' = 0) (h : ψ m = m') :
    ψ.comp (DualNumber.liftElem m hm) = DualNumber.liftElem (R := k) m' hm' := by
  ext
  simp [DualNumber.liftElem_apply, h]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
/-- Base change of a substituted tangent vector is the substitution of the image. -/
theorem kerMap_tangentMap {B : Type u} [CommRing B] [Algebra k B] [IsLocalRing B]
    {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = π) (m : A) (hm : m * m = 0)
    (hπ : π m = 0) (m' : B) (hm' : m' * m' = 0) (hπ' : πB m' = 0) (h : ψ m = m')
    (v : pointsKer G aug₁) :
    kerMap ψ hψ (tangentMap m hm hπ v) = tangentMap m' hm' hπ' v := by
  rw [tangentMap, tangentMap, kerMap_kerMap]
  exact congrArg (· v) (kerMap_congr (liftElem_comp_eq ψ m hm m' hm' h)
    (by rw [← AlgHom.comp_assoc, hψ]; exact aug_comp_liftElem m hm hπ)
    (aug_comp_liftElem m' hm' hπ'))

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
/-- Substituting `ε ↦ 0` gives the identity point. -/
theorem tangentMap_zero (v : pointsKer G aug₁) :
    tangentMap (π := π) (0 : A) (mul_zero 0) (map_zero π) v = 1 :=
  kerMap_eq_one _ (by ext; simp [DualNumber.liftElem_apply]) _ v

theorem inr_one_mul_self : (inr 1 : DualNumber k) * inr 1 = 0 := by
  ext <;> simp

/-- Substituting `ε ↦ ε` is the identity. -/
theorem tangentMap_inr_one (v : pointsKer G aug₁) :
    tangentMap (A := DualNumber k) (π := aug₁) (inr 1) inr_one_mul_self (by simp) v = v := by
  rw [tangentMap, kerMap_congr (ψ' := AlgHom.id k (DualNumber k)) (by
      ext <;> simp [DualNumber.liftElem_apply, DualNumber.fst_eps, DualNumber.snd_eps,
        algebraMap_eq_inl]) _ (AlgHom.comp_id _), kerMap_id]

/-- The point `v_ε` of `G` over `k[ε][δ]` of a tangent vector `v`. -/
noncomputable abbrev tangentEps (v : pointsKer G aug₁) : pointsKer G (aug₂ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber k)) (π := aug₂) eps₂ eps₂_mul_self aug₂_eps₂ v

/-- The point `v_δ` of `G` over `k[ε][δ]` of a tangent vector `v`. -/
noncomputable abbrev tangentDel (v : pointsKer G aug₁) : pointsKer G (aug₂ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber k)) (π := aug₂) del₂ del₂_mul_self aug₂_del₂ v

/-- The `εδ`-coefficient `C(v, w)` of `v_ε w_δ` over `k[ε][δ]`. -/
noncomputable def mulCoeff (v w : pointsKer G aug₁) (a : stalkOne G) : k :=
  (kerHom (tangentEps v * tangentDel w) a).snd.snd

/-- `δ ↦ 0`: the map `k[ε][δ] → k[ε]`. -/
abbrev fst₂ : DualNumber (DualNumber k) →ₐ[k] DualNumber k :=
  fstHom k (DualNumber k) (DualNumber k)

/-- `ε ↦ 0, δ ↦ ε`: the map `k[ε][δ] → k[ε]`. -/
abbrev rho₂ : DualNumber (DualNumber k) →ₐ[k] DualNumber k :=
  lift₂ 0 (inr 1) (mul_zero 0) inr_one_mul_self

theorem aug₁_comp_fst₂ : aug₁.comp fst₂ = (aug₂ : DualNumber (DualNumber k) →ₐ[k] k) :=
  rfl

theorem aug₁_comp_rho₂ : aug₁.comp rho₂ = (aug₂ : DualNumber (DualNumber k) →ₐ[k] k) := by
  refine AlgHom.ext fun x ↦ ?_
  simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem aug_comp_lift₂ (m n : A) (hm : m * m = 0) (hn : n * n = 0) (hπm : π m = 0)
    (hπn : π n = 0) : π.comp (lift₂ m n hm hn) = aug₂ := by
  refine AlgHom.ext fun x ↦ ?_
  simp [lift₂_apply, DualNumber.liftElem_apply, hπm, hπn]

theorem kerMap_fst₂_tangentEps_mul (v w : pointsKer G aug₁) :
    kerMap fst₂ aug₁_comp_fst₂ (tangentEps v * tangentDel w) = v := by
  rw [map_mul, kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp) (by simp),
    kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _) (by simp), tangentMap_zero,
    mul_one, tangentMap_inr_one]

theorem kerMap_rho₂_tangentEps_mul (v w : pointsKer G aug₁) :
    kerMap rho₂ aug₁_comp_rho₂ (tangentEps v * tangentDel w) = w := by
  rw [map_mul, kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _)
      (by simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]),
    kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp)
      (by simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]), tangentMap_zero,
    one_mul, tangentMap_inr_one]

theorem kerHom_mul_fst (v w : pointsKer G aug₁) (a : stalkOne G) :
    (kerHom (tangentEps v * tangentDel w) a).fst = kerHom v a := by
  have h := kerHom_kerMap fst₂ aug₁_comp_fst₂ (tangentEps v * tangentDel w)
  rw [kerMap_fst₂_tangentEps_mul] at h
  exact (congrArg (· a) h).symm

theorem kerHom_mul_snd_fst (v w : pointsKer G aug₁) (a : stalkOne G) :
    (kerHom (tangentEps v * tangentDel w) a).snd.fst = tangentCoeff w a := by
  have h := kerHom_kerMap rho₂ aug₁_comp_rho₂ (tangentEps v * tangentDel w)
  rw [kerMap_rho₂_tangentEps_mul] at h
  have h' := congrArg (fun f ↦ (f a).snd) h
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl] at h'
  rw [tangentCoeff, h']
  simp

/-- **The product formula.** For `m, n` of square zero in the maximal ideal of `A`,
`(v^{(m)} w^{(n)})^♯ = a(1) + m D_v + n D_w + mn C(v, w)`. -/
theorem kerHom_tangentMap_mul_tangentMap (m n : A) (hm : m * m = 0) (hn : n * n = 0)
    (hπm : π m = 0) (hπn : π n = 0) (v w : pointsKer G aug₁) (a : stalkOne G) :
    kerHom (tangentMap m hm hπm v * tangentMap n hn hπn w) a =
      algebraMap k A (counit G a) + algebraMap k A (tangentCoeff v a) * m +
        algebraMap k A (tangentCoeff w a) * n + algebraMap k A (mulCoeff v w a) * (m * n) := by
  have e : tangentMap m hm hπm v * tangentMap n hn hπn w =
      kerMap (A := DualNumber (DualNumber k)) (πA := aug₂) (πB := π) (lift₂ m n hm hn)
        (aug_comp_lift₂ m n hm hn hπm hπn) (tangentEps v * tangentDel w) := by
    rw [map_mul, kerMap_tangentMap _ _ _ _ _ m hm hπm (by simp [lift₂_apply,
      DualNumber.liftElem_apply]), kerMap_tangentMap _ _ _ _ _ n hn hπn (by simp [lift₂_apply,
      DualNumber.liftElem_apply])]
  rw [e, kerHom_kerMap, RingHom.comp_apply]
  have h1 := kerHom_mul_fst v w a
  have h2 := kerHom_mul_snd_fst v w a
  have h3 : (kerHom (tangentEps v * tangentDel w) a).snd.snd = mulCoeff v w a := rfl
  generalize kerHom (tangentEps v * tangentDel w) a = X at h1 h2 h3
  change (lift₂ m n hm hn) X = _
  rw [lift₂_apply, DualNumber.liftElem_apply, DualNumber.liftElem_apply, h1, h2, h3,
    kerHom_tangent]
  simp only [fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr, zero_add]
  ring
end AlgebraicGeometry.GrpObj
