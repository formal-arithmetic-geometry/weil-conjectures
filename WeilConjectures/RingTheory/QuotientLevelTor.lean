/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Consecutive-quotient Tor and split universal coefficients

`levelTor I n M` is the degree `-1` homology of a projective resolution of an
`A/I^{n+2}`-module `M`, reduced to `A/I^{n+1}`. Over a principal ideal domain, a direct summand
of `H^q(P)` killed by `I^m` is a retract of `H^q(P ⊗ A/I^m)` for a complex `P` of finite
projective modules.

Source: Bhatt--Scholze, Proposition 6.6.11; step 5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Extension of scalars between rings of the same universe is additive. -/
instance extendScalars_additive_succ {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) :
    (extendScalars.{u + 1, u + 1, u + 1} f).Additive :=
  (extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).left_adjoint_additive

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ)

/-- The module-level consecutive-quotient Tor: the degree `-1` homology of a projective
resolution of an `A/I^{n+2}`-module, reduced to `A/I^{n+1}`. -/
def levelTor (M : ModuleCat.{u + 1} (A ⧸ I ^ (n + 1 + 1))) :
    ModuleCat.{u + 1} (A ⧸ I ^ (n + 1)) :=
  (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.factorPowSucc I (n + 1))).mapHomologicalComplex (.up ℤ)).obj
      (projectiveResolution M).cochainComplex).homology (-1)


/-- If `I^m` kills `N₀`, the unit `N₀ → A/I^m ⊗ N₀` has a retraction. -/
theorem exists_unit_retraction (m : ℕ) (N₀ : ModuleCat.{u + 1} A)
    (hk : ∀ a ∈ I ^ m, ∀ x : N₀, a • x = 0) :
    ∃ μ : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk (I ^ m))).obj N₀) ⟶ N₀,
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (I ^ m))).unit.app N₀ ≫ μ = 𝟙 N₀ := by
  let f := Ideal.Quotient.mk (I ^ m)
  let L : A ⧸ I ^ m →+* Module.End A N₀ :=
    Ideal.Quotient.lift (I ^ m) (algebraMap A (Module.End A N₀)) (fun a ha ↦ by
      ext x
      simp [hk a ha x])
  let L' : (ModuleCat.restrictScalars f).obj (ModuleCat.of (A ⧸ I ^ m) (A ⧸ I ^ m)) →ₗ[A]
      Module.End A N₀ :=
    { toFun := fun s ↦ L s
      map_add' := fun s t ↦ L.map_add s t
      map_smul' := fun a s ↦ by
        change L (f a * (show A ⧸ I ^ m from s)) = algebraMap A (Module.End A N₀) a * L s
        rw [map_mul]
        rfl }
  let T := TensorProduct.lift L'
  let E := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj N₀
  have key (s : A ⧸ I ^ m) (t : E) : T (s • t) = L s (T t) := by
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | tmul s' x =>
      rw [TensorProduct.smul_tmul']
      simp only [T, TensorProduct.lift.tmul]
      change L (s * (show A ⧸ I ^ m from s')) x = L s (L s' x)
      rw [map_mul]
      rfl
    | add t₁ t₂ h₁ h₂ =>
      rw [smul_add, map_add, map_add, h₁, h₂, map_add]
  refine ⟨ModuleCat.ofHom (X := (ModuleCat.restrictScalars f).obj E) (Y := N₀)
    { toFun := fun t ↦ T t
      map_add' := fun s t ↦ map_add T s t
      map_smul' := fun a t ↦ key (f a) t }, ?_⟩
  ext x
  change T ((1 : A ⧸ I ^ m) ⊗ₜ x) = x
  simp [T, L', L]

/-- Over a principal ideal domain, the cycles of a complex of finite projective modules are a
direct summand of each term. -/
theorem exists_cycles_retraction [IsDomain A] [IsPrincipalIdealRing A]
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) (q : ℤ) :
    ∃ ρ : P.X q ⟶ P.cycles q, P.iCycles q ≫ ρ = 𝟙 _ := by
  let d := (P.d q (q + 1)).hom
  have := (hP (q + 1)).1
  have := (hP (q + 1)).2
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  let τ : P.X q ⟶ P.X q := ModuleCat.ofHom (LinearMap.id - σ.comp d.rangeRestrict)
  have hdσ (y : LinearMap.range d) : d (σ y) = y := by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  have hτ : τ ≫ P.d q (q + 1) = 0 := by
    ext x
    change d (x - σ (d.rangeRestrict x)) = 0
    rw [map_sub, hdσ]
    simp
  refine ⟨P.liftCycles τ (q + 1) (by simp) hτ, ?_⟩
  rw [← cancel_mono (P.iCycles q), Category.assoc, HomologicalComplex.liftCycles_i,
    Category.id_comp]
  ext x
  change P.iCycles q x - σ (d.rangeRestrict (P.iCycles q x)) = P.iCycles q x
  have h0 : d.rangeRestrict (P.iCycles q x) = 0 := by
    apply Subtype.ext
    change (P.iCycles q ≫ P.d q (q + 1)) x = 0
    simp
  rw [h0, map_zero, sub_zero]


/-- Universal coefficients over a principal ideal domain, split form: a direct summand `N₀`
of `H^q(P)` killed by `I^m` is a retract of `H^q(P ⊗ A/I^m)`, for a bounded complex of
finite projective modules `P`. -/
theorem exists_homology_reduction_retraction [IsDomain A] [IsPrincipalIdealRing A] (m : ℕ)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) (q : ℤ)
    (F N₀ : ModuleCat.{u + 1} A) (ε : P.homology q ≅ F ⊞ N₀)
    (hk : ∀ a ∈ I ^ m, ∀ x : N₀, a • x = 0) :
    ∃ (s : N₀ →ₗ[A] (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (Ideal.Quotient.mk (I ^ m))).mapHomologicalComplex (.up ℤ)).obj P).homology q))
      (r : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ m))).obj
        ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (Ideal.Quotient.mk (I ^ m))).mapHomologicalComplex (.up ℤ)).obj P).homology q) →ₗ[A]
          N₀), ∀ x, r (s x) = x := by
  let f := Ideal.Quotient.mk (I ^ m)
  let Ext := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f
  let Res := ModuleCat.restrictScalars.{u + 1} f
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f
  have : Ext.Additive := adj.left_adjoint_additive
  have : Res.Additive := adj.right_adjoint_additive
  have : PreservesLimitsOfSize.{0, 0} Res := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits Res := PreservesLimitsOfSize.preservesFiniteLimits Res
  have : PreservesColimitsOfSize.{0, 0} Res :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits Res := PreservesColimitsOfSize.preservesFiniteColimits Res
  let Pb := (Ext.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨ρ, hρ⟩ := exists_cycles_retraction P hP q
  obtain ⟨μ, hμ⟩ := exists_unit_retraction I m N₀ hk
  let ψ : P.X q ⟶ N₀ := ρ ≫ P.homologyπ q ≫ ε.hom ≫ biprod.snd
  let u : P ⟶ (Res.mapHomologicalComplex (.up ℤ)).obj Pb :=
    { f i := adj.unit.app (P.X i)
      comm' i j _ := (adj.unit.naturality (P.d i j)) }
  let g : Pb ⟶ (HomologicalComplex.single _ (.up ℤ) q).obj (Ext.obj N₀) :=
    HomologicalComplex.mkHomToSingle (Ext.map ψ) (by
      intro i _
      change Ext.map (P.d i q) ≫ Ext.map ψ = 0
      rw [← Ext.map_comp]
      have : P.d i q ≫ ρ = P.toCycles i q := by
        rw [← P.toCycles_i i q, Category.assoc, hρ, Category.comp_id]
      simp only [ψ, ← Category.assoc, this, HomologicalComplex.toCycles_comp_homologyπ,
        zero_comp, Ext.map_zero])
  let g' : (Res.mapHomologicalComplex (.up ℤ)).obj Pb ⟶
      (HomologicalComplex.single _ (.up ℤ) q).obj (Res.obj (Ext.obj N₀)) :=
    (Res.mapHomologicalComplex (.up ℤ)).map g ≫
    (HomologicalComplex.singleMapHomologicalComplex Res (.up ℤ) q).hom.app (Ext.obj N₀)
  let eH := (Res.mapHomologicalComplexHomologyIso (.up ℤ) q).app Pb
  let s : N₀ ⟶ Res.obj (Pb.homology q) :=
    biprod.inr ≫ ε.inv ≫ HomologicalComplex.homologyMap u q ≫ eH.hom
  let r : Res.obj (Pb.homology q) ⟶ N₀ := eH.inv ≫ HomologicalComplex.homologyMap g' q ≫
    (HomologicalComplex.singleObjHomologySelfIso _ q _).hom ≫ μ
  have hug : u ≫ g' = HomologicalComplex.mkHomToSingle (ψ ≫ adj.unit.app N₀) (by
      intro i _
      have : P.d i q ≫ ρ = P.toCycles i q := by
        rw [← P.toCycles_i i q, Category.assoc, hρ, Category.comp_id]
      simp only [ψ, ← Category.assoc, this, HomologicalComplex.toCycles_comp_homologyπ,
        zero_comp]) := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.mkHomToSingle_f, Functor.map_comp,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
      Iso.map_inv_hom_id_assoc, Functor.comp_obj, u, g', g]
    exact adj.unit_naturality_assoc ψ _
  have hπ : HomologicalComplex.homologyMap (u ≫ g') q ≫
      (HomologicalComplex.singleObjHomologySelfIso _ q _).hom =
        ε.hom ≫ biprod.snd ≫ adj.unit.app N₀ := by
    rw [← cancel_epi (P.homologyπ q), hug, HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
      HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc,
      HomologicalComplex.mkHomToSingle_f]
    simp [ψ, reassoc_of% hρ, Res, Ext]
  have key : s ≫ r = 𝟙 N₀ := by
    simp only [s, r, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← HomologicalComplex.homologyMap_comp_assoc, reassoc_of% hπ, ε.inv_hom_id_assoc,
      biprod.inr_snd_assoc, hμ]
  exact ⟨s.hom, r.hom, fun x ↦ congrArg (fun φ ↦ φ.hom x) key⟩

/-- The module-level consecutive-quotient Tor of a module containing a retract `N₀` killed
by `π^{n+1}` surjects onto `N₀/πN₀`.

Proof sketch: tensor `0 → A/π --π^{n+1}--> A/π^{n+2} → A/π^{n+1} → 0` with the projective
resolution `R → M`; the connecting map sends `H^{-1}(R ⊗ A/π^{n+1})` onto the kernel of
`π^{n+1} : M/πM → M`. For `x : N₀`, `s x` is killed by `π^{n+1}`, so its class lies in that
kernel, and `r` sends it to `x` modulo `π`. -/
theorem exists_levelTor_epi [IsDomain A] (π : A) (hπ : π ≠ 0) (hI : I = Ideal.span {π})
    (M : ModuleCat.{u + 1} (A ⧸ I ^ (n + 1 + 1))) (N₀ : ModuleCat.{u + 1} A)
    (s : N₀ →ₗ[A] (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).obj M)
    (r : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).obj M →ₗ[A] N₀)
    (hrs : ∀ x, r (s x) = x) (hk : ∀ x : N₀, π ^ (n + 1) • x = 0) :
    ∃ t : levelTor I n M ⟶ (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (I ^ (n + 1)))).obj
          (cokernel (ModuleCat.ofHom (π • LinearMap.id : N₀ →ₗ[A] N₀))), Epi t := by
  sorry

end ModuleCat
