/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ImmersiveSystemSourceLocalFractions
import WeilConjectures.AlgebraicGeometry.ClosedPointResidueField

/-! # First jets of an immersive linear system at the source

Source: the finite-cover Bertini proof, paragraph 3; Stacks Tags 01NE and 01NF.
(blueprint: lem-zl-immersive-system-source-first-jets).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private theorem linear_image_firstOrder
    {k R W : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    [AddCommGroup W] [Module k W] (f : W →ₗ[k] R)
    (hres : ∀ a : R, ∃ c : k, a - algebraMap k R c ∈ IsLocalRing.maximalIdeal R)
    (u : Rˣ) (w : W) (hw : f w = (u : R))
    {I : Type*} (s : I → W)
    (hfrac : ∀ a : R, ∃ p q : MvPolynomial I k,
      IsUnit (MvPolynomial.aeval (fun i ↦ (↑u⁻¹ : R) * f (s i)) q) ∧
      a * MvPolynomial.aeval (fun i ↦ (↑u⁻¹ : R) * f (s i)) q =
        MvPolynomial.aeval (fun i ↦ (↑u⁻¹ : R) * f (s i)) p) :
    ∀ a : R, ∃ v : W, f v - a ∈ IsLocalRing.maximalIdeal R ^ 2 := by
  classical
  let m := IsLocalRing.maximalIdeal R
  let J : Ideal R := m ^ 2
  let g : W →ₗ[k] R :=
    { toFun := fun v ↦ (↑u⁻¹ : R) * f v
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp [Algebra.smul_def, mul_left_comm] }
  let M : Submodule k R := LinearMap.range g ⊔ J.restrictScalars k
  have hJ {a : R} (ha : a ∈ J) : a ∈ M :=
    (show J.restrictScalars k ≤ M from le_sup_right) ha
  have hone : (1 : R) ∈ M := by
    apply (show LinearMap.range g ≤ M from le_sup_left)
    exact ⟨w, by simp [g, hw]⟩
  have hscalar (c : k) : algebraMap k R c ∈ M := by
    simpa only [Algebra.smul_def, mul_one] using M.smul_mem c hone
  -- Products are linear modulo J because both factors have scalar residues.
  have hmul {a b : R} (ha : a ∈ M) (hb : b ∈ M) : a * b ∈ M := by
    obtain ⟨c, hc⟩ := hres a
    obtain ⟨d, hd⟩ := hres b
    have hprod : (a - algebraMap k R c) * (b - algebraMap k R d) ∈ M := by
      apply hJ
      change _ ∈ m ^ 2
      rw [pow_two]
      exact Ideal.mul_mem_mul hc hd
    have h := M.add_mem (M.sub_mem (M.add_mem hprod (M.smul_mem c hb))
      (hscalar (c * d))) (M.smul_mem d ha)
    convert h using 1
    simp only [Algebra.smul_def, map_mul]
    ring
  -- The same expansion, applied to z and its inverse, handles denominators.
  have hinv (z : Rˣ) (hz : (z : R) ∈ M) : (↑z⁻¹ : R) ∈ M := by
    obtain ⟨c, hc⟩ := hres (z : R)
    obtain ⟨d, hd⟩ := hres (↑z⁻¹ : R)
    have hc0 : c ≠ 0 := by
      intro hc0
      have hzmem : (z : R) ∈ m := by
        rw [hc0, map_zero, sub_zero] at hc
        exact hc
      exact (IsLocalRing.notMem_maximalIdeal.mpr z.isUnit) hzmem
    have hprod : ((z : R) - algebraMap k R c) *
        ((↑z⁻¹ : R) - algebraMap k R d) ∈ M := by
      apply hJ
      change _ ∈ m ^ 2
      rw [pow_two]
      exact Ideal.mul_mem_mul hc hd
    have h : c • (↑z⁻¹ : R) ∈ M := by
      have h := M.sub_mem (M.add_mem (M.sub_mem hone (M.smul_mem d hz))
        (hscalar (c * d))) hprod
      convert h using 1
      simp only [Algebra.smul_def, map_mul]
      have hzprod : (z : R) * (↑z⁻¹ : R) = 1 := z.mul_inv
      linear_combination hzprod
    have h := M.smul_mem c⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using h
  have hpoly (p : MvPolynomial I k) : MvPolynomial.aeval (fun i ↦ g (s i)) p ∈ M := by
    induction p using MvPolynomial.induction_on with
    | C c => simpa using hscalar c
    | add p q hp hq => simpa only [map_add] using M.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact hmul hp ((show LinearMap.range g ≤ M from le_sup_left)
        (LinearMap.mem_range_self g (s i)))
  intro a
  have htop (a : R) : a ∈ M := by
    obtain ⟨p, q, hq, hpq⟩ := hfrac a
    obtain ⟨z, hz⟩ := hq
    have hzM : (z : R) ∈ M := hz ▸ hpoly q
    have h := hmul (hpoly p) (hinv z hzM)
    change MvPolynomial.aeval (fun i ↦ (↑u⁻¹ : R) * f (s i)) p * (↑z⁻¹ : R) ∈ M at h
    rw [← hpq, ← hz, mul_assoc, z.mul_inv, mul_one] at h
    exact h
  -- Undo normalization by the chosen unit in the original frame.
  obtain ⟨y, hy, t, ht, hyt⟩ := Submodule.mem_sup.mp (htop ((↑u⁻¹ : R) * a))
  obtain ⟨v, rfl⟩ := hy
  refine ⟨v, ?_⟩
  have hdiff : g v - (↑u⁻¹ : R) * a ∈ J := by
    rw [← hyt, sub_add_cancel_left]
    exact J.neg_mem ht
  have h := J.mul_mem_left (u : R) hdiff
  convert h using 1
  dsimp [g]
  rw [mul_sub, ← mul_assoc, u.mul_inv, one_mul, ← mul_assoc, u.mul_inv, one_mul]

/-- Coefficients of an immersive system realize every first jet at a closed source point.
There is no etale pullback, choice of an independent pair, or dimension hypothesis here.

Source: latest blueprint,
`sk-lem-wgen-bertini-cover/lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 3;
Stacks Tags 01NE and 01NF, standard affine charts and their coordinate ratios.
(blueprint: lem-zl-immersive-system-source-first-jets).

Proof: Choose a generating basis section nonzero at x. The corresponding projective chart
has polynomial coordinates given by the ratios of the other sections to this section.
The image point is rational over k, since x is closed in a scheme locally of finite type
over the algebraically closed field. Its maximal ideal is generated by the coordinate
ratios minus their k-values. An immersion induces a surjection on local rings, so these
differences span the cotangent space at x. Modulo the maximal-ideal square, every local
function is its k-value plus a k-linear combination of these differences. These constants
and linear combinations are coefficients of vectors in V: use the nonzero basis section
for the constant and subtract scalar multiples of it for the differences. This proves
surjectivity in the frame supplied by that basis section. Changing to the given frame e
multiplies all coefficient jets by a unit of the local ring modulo its maximal-ideal
square, which preserves surjectivity. The statement is vacuous if X is empty; a zero
coordinate family cannot generate an invertible module at x. No smoothness is used. -/
theorem immersiveSystem_source_first_jets
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (U₀ : X.Opens)
    (L : X.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down)))))))
    [IsImmersion (@ProjectiveSpace.homOfGeneratingSections
      (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
      (U₀.ι ≫ (X ↘ Spec (.of k))) ((Scheme.Modules.tensorPullback U₀.ι).obj L)
      (Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction U₀.ι)).app L).symm)
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down))))) hgen)]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxU₀ : x ∈ U₀)
    (U : X.Opens) (hxU : x ∈ U) (e : Γ(L, U))
    (he : Scheme.Modules.IsFreeGenerator e) :
    ∀ a : X.presheaf.stalk x, ∃ v : V,
      X.presheaf.germ U x hxU
          (he.coeff (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (ψ v))) - a ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  classical
  let p := X ↘ Spec (.of k)
  let R := X.presheaf.stalk x
  let ρ : k →+* R :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp p.appTop.hom).comp
      (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k R := ρ.toAlgebra
  let f : V →ₗ[k] R :=
    { toFun := fun v ↦ X.presheaf.germ U x hxU
        (he.coeff (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (ψ v)))
      map_add' := by intros; simp
      map_smul' := by
        intro c v
        change X.presheaf.germ U x hxU
            (he.coeff (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (ψ (c • v)))) =
          ρ c * X.presheaf.germ U x hxU
            (he.coeff (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (ψ v)))
        rw [hlinear, Scheme.Modules.map_smul, he.coeff_smul_left, map_mul]
        congr 1
        exact X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hxU
          (p.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) }
  have hres : ∀ a : R, ∃ c : k, a - algebraMap k R c ∈ IsLocalRing.maximalIdeal R := by
    let := (p.residueFieldAlgebraMap x).toAlgebra
    have := p.finite_residueField_of_isClosed x hx
    have hsur : Function.Surjective (p.residueFieldAlgebraMap x) :=
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    have hcompat (c : k) : p.residueFieldAlgebraMap x c = X.residue x (ρ c) := by
      have h : CommRingCat.ofHom (algebraMap (CommRingCat.of k)
          (p.base x).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of k) (p.base x)).inv ≫ p.residueFieldMap x =
          (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
            X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
        rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc, Scheme.residue_residueFieldMap,
          Scheme.Hom.germ_stalkMap_assoc]
        rfl
      exact congrArg (fun φ ↦ φ.hom c) h
    intro a
    obtain ⟨c, hc⟩ := hsur (X.residue x a)
    refine ⟨c, ?_⟩
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    change X.residue x (a - ρ c) = 0
    rw [map_sub, ← hcompat, hc, sub_self]
  obtain ⟨i, u, hu, hfrac⟩ := immersiveSystem_source_local_fractions k X U₀ L r
    (fun j ↦ ψ (b j)) hgen x hxU₀ U hxU e he
  apply linear_image_firstOrder f hres u (b i) hu.symm (fun j ↦ b j)
  exact hfrac

end AlgebraicGeometry
