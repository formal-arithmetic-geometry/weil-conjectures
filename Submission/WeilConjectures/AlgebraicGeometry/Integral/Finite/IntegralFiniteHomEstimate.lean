/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHomField

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # A finite-level estimate for internal Hom of integral reductions -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

open Scheme

set_option hygiene false in
local notation "D(" X ", " R ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} R))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- **The internal hom commutes with reduction modulo a power of a nonzerodivisor** in its second
variable: `RHom(K, L) ⊗ᴸ R ⧸ (vⁿ) ≅ RHom(K, L ⊗ᴸ R ⧸ (vⁿ))`. Both are cones of the multiplication
by `vⁿ` on `RHom(K, L)`, the functor `RHom(K, -)` being triangulated and `R`-linear (the right
adjoint of `K ⊗ᴸ -`). -/
theorem nonempty_iso_reductionModIdeal_spanSingletonPow_derivedHom {R : Type (u + 1)}
    [CommRing R] {X : Scheme.{u}} {v : R} (hv : v ∈ nonZeroDivisors R) (n : ℕ) (K L : D(X, R)) :
    Nonempty ((reductionModIdeal R X (Ideal.span {v} ^ n)).obj
        (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L) ≅
      ((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj
        ((reductionModIdeal R X (Ideal.span {v} ^ n)).obj L)) := by
  let Φ := (derivedHom (ModuleCat.{u + 1} R) X).obj (op K)
  let adj := derivedTensorHomAdjunction (ModuleCat.{u + 1} R) K
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have := adj.isTriangulated_rightAdjoint
  have := adj.right_adjoint_linear (R := R)
  let FX := (derivedTensor (ModuleCat.{u + 1} R) X).obj L
  let FY := (derivedTensor (ModuleCat.{u + 1} R) X).obj (Φ.obj L)
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hv rfl n
  have h₁ : Φ.mapTriangle.obj (FX.mapTriangle.obj T) ∈ distTriang _ :=
    Φ.map_distinguished _ (FX.map_distinguished _
      (_root_.DerivedCategory.quotPowTriangle_distinguished _ hv rfl n))
  have h₂ : FY.mapTriangle.obj T ∈ distTriang _ :=
    FY.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hv rfl n)
  have hX : (Φ.mapTriangle.obj (FX.mapTriangle.obj T)).mor₁ =
      v ^ n • 𝟙 (Φ.obj (FX.obj T.obj₁)) := by
    change Φ.map (FX.map T.mor₁) = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  have hY : (FY.mapTriangle.obj T).mor₁ = v ^ n • 𝟙 (FY.obj T.obj₁) := by
    change FY.map T.mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  let w : Φ.obj (FX.obj T.obj₁) ≅ FY.obj T.obj₁ :=
    Φ.mapIso (derivedTensorSingleUnitIso L) ≪≫ (derivedTensorSingleUnitIso (Φ.obj L)).symm
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ h₁ h₂
    (Arrow.isoMk w w (by
      change w.hom ≫ (FY.mapTriangle.obj T).mor₁ =
        (Φ.mapTriangle.obj (FX.mapTriangle.obj T)).mor₁ ≫ w.hom
      rw [hX, hY, Linear.comp_smul, Category.comp_id]
      erw [Linear.smul_comp, Category.id_comp]))
  exact ⟨(Pretriangulated.Triangle.π₃.mapIso e).symm⟩

/-- The finite-level part of integral constructible internal Hom, for a single reduction,
before derived completeness and uniform tower bounds. The Tor bounds are measured after
restriction to `R`.

Source: blueprint `cor-coef-integral-internal-hom.proof.md`, sentences 2--4, specialized to
constant coefficients on the small etale site, with the regular coefficient sequence of
`lem-coef-integral-hom-reduction.proof.md`.
(blueprint: lem-coef-small-etale-integral-finite-hom-estimate)

Proof: every R/I^(m+1) is finite, by its finite filtration with subquotients of R/I.
For a residue field F of this finite ring, the regular two-term resolution of R/I^(m+1)
tensored over R with F has zero differential and is F[1] direct-sum F. By associativity,
testing the underlying R-reduction of K against the constant F-sheaf therefore tests the
direct sum of K tensor_R F and its shift by 1. The interval [a,b] forces K tensor_R F
to have support in [a+1,b]. Construct universal derived reductions Kn,Ln by a K-flat quotient model.
Universality and derived scalar associativity identify this with Kn tensor_(R/I^(n+1)) F.
Similarly the residue tests for Ln have support [c+1,e].
The finite-length filtration of any module over each local Artinian factor, or equivalently
the nilpotent-ideal residue criterion, gives quotient Tor intervals [a+1,b] and [c+1,e].
Constructibility of Kn and Ln follows from that of their restrictions to R. The case where
v is a unit has zero quotient categories. Constructibility transports through exact scalar
restriction. On affine opens over an algebraic closure of the base field, the finite-Tor
constructible Hom estimate, by dual-tensor-dual, gives quotient Tor interval
[c+1-b-2d,e-a-1+2d]. It applies to arbitrary finite coefficient rings on finite-Tor inputs;
no self-injectivity of R or its quotients is asserted. Descent under the field extension and
gluing over affine opens preserve constructibility and the bounds. Restricting scalars to R
adds the degree -1 term of the regular coefficient resolution, giving
[c-b-2d,e-a-1+2d], contained in the claimed interval. Exact restriction commutes with homology.
The scalar adjunction and the regular coefficient triangle identify the restricted finite Hom
with the displayed reduction of the ambient Hom. Completeness and uniform tower bounds are
separate steps. This estimate assumes only one finite-level reduction of K and L.
If an input interval is reversed, its tensor-unit test makes that reduction zero, so its finite
Hom is zero. The empty scheme is handled by the same vanishing argument. At a point with
K=L=R, the restricted reductions have amplitude [-1,0] and the asserted interval is [-1,1],
which contains the actual output. For K=R/v and L=R over a DVR, retaining the degree -1
coefficient term gives input intervals [-2,0] and [-1,0] and output contained in [-1,2]. -/
theorem integralFiniteHomEstimate
    {R : Type (u + 1)} [CommRing R] (I : Ideal R)
    [Finite (R ⧸ I)]
    {v : R} (hv : v ∈ nonZeroDivisors R) (hI : I = Ideal.span {v})
    {k : Type u} [Field k] [HasInvertibleExponent (R ⧸ I) (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (n : ℕ)
    {K L : D(X, R)}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
      ((reductionModIdeal R X (I ^ (n + 1))).obj K))
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
      ((reductionModIdeal R X (I ^ (n + 1))).obj L))
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b c e : ℤ)
    (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X a b
      ((reductionModIdeal R X (I ^ (n + 1))).obj K))
    (hLt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X c e
      ((reductionModIdeal R X (I ^ (n + 1))).obj L))
    : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
        ((reductionModIdeal R X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
        ((reductionModIdeal R X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L)) := by
  subst hI
  have hφ : Function.Surjective (Ideal.Quotient.mk (Ideal.span {v} ^ (n + 1))) :=
    Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {v} ^ (n + 1))) =
      Ideal.span {v ^ (n + 1)} := by
    rw [Ideal.mk_ker, Ideal.span_singleton_pow]
  have hv' : v ^ (n + 1) ∈ nonZeroDivisors R := pow_mem hv _
  have : Finite (R ⧸ Ideal.span {v} ^ (n + 1)) :=
    Ideal.finite_quotient_pow ⟨{v}, by simp⟩ _
  have : HasInvertibleExponent (R ⧸ Ideal.span {v} ^ (n + 1)) (Spec (.of k)) := by
    obtain ⟨N, hN, hNR, hNk⟩ :=
      HasInvertibleExponent.exists_isUnit_natCast (Λ := R ⧸ Ideal.span {v}) (X := Spec (.of k))
    refine ⟨N ^ (n + 1), pow_pos hN _, ?_, by simpa using hNk.pow (n + 1)⟩
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    refine Ideal.pow_mem_pow ?_ _
    rwa [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem] at hNR
  let Kn := (derivedExtendScalars hφ hker X).obj K
  let Ln := (derivedExtendScalars hφ hker X).obj L
  -- the reductions are the restrictions of scalars of the derived base changes
  obtain ⟨eK⟩ := nonempty_iso_derivedRestrictScalars_derivedExtendScalars hφ hker X K
  obtain ⟨eL⟩ := nonempty_iso_derivedRestrictScalars_derivedExtendScalars hφ hker X L
  rw [Ideal.mk_ker] at eK eL
  have hKn : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X Kn :=
    (boundedConstructible_derivedRestrictScalars_iff _ Kn).1
      ((DerivedCategory.boundedConstructible _ X).prop_of_iso eK.symm hK)
  have hLn : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X Ln :=
    (boundedConstructible_derivedRestrictScalars_iff _ Ln).1
      ((DerivedCategory.boundedConstructible _ X).prop_of_iso eL.symm hL)
  -- the Tor amplitude of the derived base changes, over `R ⧸ (vⁿ⁺¹)`
  have hKnt : DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X (a + 1) b Kn := by
    refine torAmplitudeIn_derivedExtendScalars hφ hker hv' ?_
    rw [quotientSingle, Ideal.mk_ker]
    exact hKt
  have hLnt : DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (R ⧸ Ideal.span {v} ^ (n + 1))) X (c + 1) e Ln := by
    refine torAmplitudeIn_derivedExtendScalars hφ hker hv' ?_
    rw [quotientSingle, Ideal.mk_ker]
    exact hLt
  obtain ⟨hHc, hHt⟩ := boundedConstructible_and_torAmplitudeIn_derivedHom_of_field _ aX d hd
    hKn hKnt hLn hLnt
  -- the reduction of the internal hom is the restriction of scalars of the finite internal hom
  obtain ⟨e₁⟩ := nonempty_iso_reductionModIdeal_spanSingletonPow_derivedHom hv (n + 1) K L
  obtain ⟨e₂⟩ := nonempty_iso_derivedHom_derivedTensor_of_isDerivedBaseChange hφ hker X
    (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hφ hker X K)
    (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hφ hker X L)
  rw [Ideal.mk_ker] at e₂
  let e := e₁ ≪≫ e₂
  refine ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e.symm
    ((boundedConstructible_derivedRestrictScalars_iff _ _).2 hHc),
    (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso e.symm ?_⟩
  exact (torAmplitudeIn_derivedRestrictScalars hφ hker hv' hHt).mono (by lia) (by lia)

end AlgebraicGeometry.Etale
