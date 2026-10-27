/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Finite reduced points and their first infinitesimal neighbourhood

Source: blueprint, finite-cover-curve proof, paragraph 2; Stacks Project, Tag 01IN.
(blueprint: lem-zl-prescribed-point-infinitesimal-model).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry ChangeOfRings TensorProduct

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback Scheme.Modules.pullback
  tensorSectionsUnit prescribedPointJet

private theorem frame_mem_ideal {R P : Type u} [CommRing R] [AddCommGroup P]
    [Module R P] (e : P ≃ₗ[R] R) (I : Ideal R) (m : P) :
    m ∈ I • (⊤ : Submodule R P) ↔ e m ∈ I := by
  have hmap : (I • (⊤ : Submodule R P)).map e.toLinearMap = I := by
    rw [Submodule.map_smul'', Submodule.map_top, e.range,
      Ideal.smul_eq_mul, Ideal.mul_top]
  calc
    m ∈ I • (⊤ : Submodule R P) ↔
        e m ∈ (I • (⊤ : Submodule R P)).map e.toLinearMap := by
      simp only [Submodule.mem_map_equiv, e.symm_apply_apply]
    _ ↔ e m ∈ I := by rw [hmap]

/-- Rank-one frames give explicit representatives of cotangent tensors. -/
private theorem exists_cotangent_frame_representative
    {T P : Type u} [CommRing T] [IsLocalRing T] [AddCommGroup P] [Module T P]
    (e : P ≃ₗ[T] T) (b : IsLocalRing.CotangentSpace T ⊗[T] P) :
    ∃ a : IsLocalRing.maximalIdeal T,
      (IsLocalRing.maximalIdeal T).toCotangent a ⊗ₜ[T] e.symm 1 = b := by
  let B := (TensorProduct.congr
    (LinearEquiv.refl T (IsLocalRing.CotangentSpace T)) e).trans
      (TensorProduct.rid T (IsLocalRing.CotangentSpace T))
  obtain ⟨a, ha⟩ := (IsLocalRing.maximalIdeal T).toCotangent_surjective (B b)
  refine ⟨a, B.injective ?_⟩
  simpa only [B, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, e.apply_symm_apply, TensorProduct.rid_tmul, one_smul] using ha

private theorem tensor_unit_eq {A B : Scheme.{u}} (f : A ⟶ B) (M : B.Modules) :
    tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : A.Opens)) := rfl
  erw [hi, ((tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

private theorem exists_tensor_stalk_frame {A B : Scheme.{u}} (f : A ⟶ B)
    (M : B.Modules) (x : A)
    (e : M.presheaf.stalk (f x) ≃ₗ[B.presheaf.stalk (f x)] B.presheaf.stalk (f x)) :
    ∃ E : ((tensorPullback f).obj M).presheaf.stalk x ≃ₗ[A.presheaf.stalk x]
        A.presheaf.stalk x,
      ∀ v : Γ(M, ⊤),
        E (((tensorPullback f).obj M).presheaf.germ ⊤ x trivial
          (tensorSectionsUnit f M v)) =
        f.stalkMap x (e (M.presheaf.germ ⊤ (f x) trivial v)) := by
  let R := B.presheaf.stalk (f x)
  let T := A.presheaf.stalk x
  let : Algebra R T := (f.stalkMap x).hom.toAlgebra
  obtain ⟨δ, hδ⟩ := exists_tensorPullback_stalk_iso f x
  let E₀ := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) e
  let E := ((δ.app M).toLinearEquiv.trans E₀).trans (TensorProduct.AlgebraTensorModule.rid R T T)
  refine ⟨E, fun v ↦ ?_⟩
  change TensorProduct.AlgebraTensorModule.rid R T T
    (E₀ ((δ.hom.app M) (((tensorPullback f).obj M).presheaf.germ ⊤ x trivial
      (tensorSectionsUnit f M v)))) = _
  rw [tensor_unit_eq]
  erw [hδ M ⊤ trivial v]
  simp only [E₀, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  erw [TensorProduct.AlgebraTensorModule.rid_tmul]
  change (f.stalkMap x).hom _ * 1 = _
  exact mul_one _

private theorem ordinary_germ_zero_iff_tensor {A B : Scheme.{u}} (f : A ⟶ B)
    (M : B.Modules) (x : A) (v : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.germ ⊤ x trivial (pullbackΓ f M v) = 0 ↔
      ((tensorPullback f).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit f M v) = 0 := by
  let α := ((Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)).app M
  let ε := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
    ((Scheme.Modules.toPresheaf A).mapIso α)
  have hu : α.hom.app ⊤ (tensorSectionsUnit f M v) = pullbackΓ f M v := by
    rw [tensor_unit_eq, pullbackΓ_def]
    exact congrArg (fun h ↦ h.app ⊤ v)
      ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_leftAdjointUniq_hom_app
        (pullbackPushforwardAdjunction f) M)
  have hg : ε.hom
      (((tensorPullback f).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit f M v)) =
      ((Scheme.Modules.pullback f).obj M).presheaf.germ ⊤ x trivial (pullbackΓ f M v) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α.hom.mapPresheaf _ = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change ((Scheme.Modules.pullback f).obj M).presheaf.germ ⊤ x trivial
      (α.hom.app ⊤ (tensorSectionsUnit f M v)) = _
    rw [hu]
  rw [← hg]
  exact ε.addCommGroupIsoToAddEquiv.map_eq_zero_iff

private theorem tensor_residue_germ_iff {A B : Scheme.{u}} (f : A ⟶ B)
    (M : B.Modules) [M.IsInvertible] (x : A) (v : Γ(M, ⊤)) :
    ((tensorPullback f).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit f M v) ∈
        (IsLocalRing.maximalIdeal (A.presheaf.stalk x)) •
          (⊤ : Submodule (A.presheaf.stalk x) (((tensorPullback f).obj M).presheaf.stalk x)) ↔
      M.presheaf.germ ⊤ (f x) trivial v ∈
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (f x))) •
          (⊤ : Submodule (B.presheaf.stalk (f x)) (M.presheaf.stalk (f x))) := by
  let e := Classical.choice (invertible_stalk_linearEquiv B M (f x))
  obtain ⟨E, hE⟩ := exists_tensor_stalk_frame f M x e
  rw [frame_mem_ideal E, hE, frame_mem_ideal e]
  change e (M.presheaf.germ ⊤ (f x) trivial v) ∈
    (IsLocalRing.maximalIdeal (A.presheaf.stalk x)).comap (f.stalkMap x).hom ↔ _
  rw [IsLocalRing.maximalIdeal_comap]

/-- At a point of a finite reduced closed subscheme, restriction kills a section's germ
exactly when its restriction to an open subscheme has zero residue at the corresponding point.

Source: blueprint, finite-cover-curve proof, paragraph 2 (reduced prescribed points);
Stacks Project, Tag 01J3, Lemma `lemma-reduced-closed-subscheme`, and Tag 0098.
(blueprint: lem-zl-prescribed-point-infinitesimal-model).

Proof: The reduced closed subscheme has a finite T1 underlying space, hence is discrete.
Each point is an irreducible component, so its reduced local ring is a field. Surjectivity
of the closed-immersion stalk map identifies its kernel with the maximal ideal. Pullback
on module stalks is extension of scalars, and its unit is m ↦ 1 tensor m. Extension to the
residue field has kernel the maximal ideal times M_(Y,j(x)). The open immersion identifies
O_(Y,j(x)) with O_(X,x) and identifies the tensor-pullback module stalks and the germs of
pulled-back sections. These isomorphisms preserve the maximal ideals and their products
with modules, giving the equivalence. No other points or global section gluing enter.
The hypotheses include every point used, so the assertion is vacuous for empty C.
-/
private theorem finiteReducedPoint_residue_germ_iff
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : TopologicalSpace.Closeds Y) (hfinite : (C : Set Y).Finite)
    (hclosed : ∀ y ∈ C, IsClosed ({y} : Set Y))
    (M : Y.Modules) [M.IsInvertible]
    (x : X) (z : (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
    (hz : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι z = j x)
    (v : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback
      (Scheme.IdealSheafData.vanishingIdeal C).subschemeι).obj M).presheaf.germ ⊤ z trivial
        (pullbackΓ (Scheme.IdealSheafData.vanishingIdeal C).subschemeι M v) = 0 ↔
      ((tensorPullback j).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit j M v) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (((tensorPullback j).obj M).presheaf.stalk x)) := by
  classical
  let J := Scheme.IdealSheafData.vanishingIdeal C
  let Z := J.subscheme
  let i : Z ⟶ Y := J.subschemeι
  have hrange : Set.range i = (C : Set Y) := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι = (C : Set Y)
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : Finite Z := by
    have : Finite (C : Set Y) := hfinite.to_subtype
    exact Finite.of_injective (fun z : Z ↦ (⟨i z, hrange.le ⟨z, rfl⟩⟩ : C))
      (fun z z' h ↦ i.isClosedEmbedding.injective (congrArg Subtype.val h))
  have : T1Space Z := ⟨fun z ↦ i.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
    (by simpa only [Set.image_singleton] using hclosed (i z) (hrange.le ⟨z, rfl⟩))⟩
  have hc : closure ({z} : Set Z) ∈ irreducibleComponents Z := by
    rw [isClosed_singleton.closure_eq]
    refine ⟨isIrreducible_singleton, fun T hT hzT ↦ ?_⟩
    obtain ⟨z', rfl⟩ := isIrreducible_iff_singleton.mp hT
    exact Set.singleton_subset_singleton.mpr
      (Set.singleton_subset_singleton.mp hzT).symm
  let : Field (Z.presheaf.stalk z) := (isField_stalk_of_closure_mem_irreducibleComponents
    (X := Z) z hc).toField
  have hkernel := IsLocalRing.ker_eq_maximalIdeal (i.stalkMap z).hom (i.stalkMap_surjective z)
  let e := Classical.choice (invertible_stalk_linearEquiv Y M (i z))
  obtain ⟨E, hE⟩ := exists_tensor_stalk_frame i M z e
  have hzero : ((Scheme.Modules.pullback i).obj M).presheaf.germ ⊤ z trivial (pullbackΓ i M v) = 0 ↔
      M.presheaf.germ ⊤ (i z) trivial v ∈
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (i z))) •
          (⊤ : Submodule (Y.presheaf.stalk (i z)) (M.presheaf.stalk (i z))) := by
    rw [ordinary_germ_zero_iff_tensor, ← E.map_eq_zero_iff, hE, frame_mem_ideal e]
    change e (M.presheaf.germ ⊤ (i z) trivial v) ∈ RingHom.ker (i.stalkMap z).hom ↔ _
    rw [hkernel]
  rw [hzero, tensor_residue_germ_iff]
  change _ ↔ M.presheaf.germ ⊤ (j x) trivial v ∈ _
  rw [← hz]


/-- The local kernel of the nth ideal-power neighbourhood at a finite closed point
is the nth power of the maximal ideal.

Source: Stacks Project, Tags 01IN and 01J3; blueprint, finite-cover-curve proof,
paragraph 2, first infinitesimal neighbourhoods.
(blueprint: lem-zl-prescribed-point-infinitesimal-model).

Proof: Remove the other finitely many closed points and take an affine neighbourhood
of the remaining point. On this neighbourhood the vanishing ideal of C is the prime
ideal of this point. The stalk is localization at that prime, so its image is the
maximal ideal. Localization commutes with ideal powers, and the kernel of the
closed-immersion stalk map is the extension of its defining affine ideal.
-/
private theorem finitePoint_ideal_stalk_kernel_pow
    {Y : Scheme.{u}} (C : TopologicalSpace.Closeds Y)
    (hfinite : (C : Set Y).Finite) (hclosed : ∀ y ∈ C, IsClosed ({y} : Set Y))
    (n : ℕ) (z : ((Scheme.IdealSheafData.vanishingIdeal C) ^ n).subscheme)
    (hz : ((Scheme.IdealSheafData.vanishingIdeal C) ^ n).subschemeι z ∈ C) :
    RingHom.ker (((Scheme.IdealSheafData.vanishingIdeal C) ^ n).subschemeι.stalkMap z).hom =
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk
        (((Scheme.IdealSheafData.vanishingIdeal C) ^ n).subschemeι z))) ^ n := by
  classical
  let J := Scheme.IdealSheafData.vanishingIdeal C
  let w := (J ^ n).subschemeι
  let y : Y := w z
  have hD : IsClosed ((C : Set Y) \ {y}) := by
    rw [← Set.biUnion_of_singleton ((C : Set Y) \ {y})]
    exact hfinite.sdiff.isClosed_biUnion
      (fun t ht ↦ hclosed t ht.1)
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUsub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ ((C : Set Y) \ {y})ᶜ from by simp) hD.isOpen_compl
  change IsAffineOpen U at hU
  have hJC : J.ideal ⟨U, hU⟩ = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    have hpre : hU.fromSpec ⁻¹' (C : Set Y) = {hU.primeIdealOf ⟨y, hyU⟩} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hp
        have hpU : hU.fromSpec p ∈ U := by
          exact hU.range_fromSpec.le ⟨p, rfl⟩
        have heq : hU.fromSpec p = y := by
          by_contra hne
          exact hUsub hpU ⟨hp, hne⟩
        apply hU.fromSpec.isOpenEmbedding.injective
        rw [heq, hU.fromSpec_primeIdealOf]
      · rintro rfl
        rw [hU.fromSpec_primeIdealOf]
        exact hz
    rw [hpre]
    exact PrimeSpectrum.vanishingIdeal_singleton _
  rw [w.ker_stalkMap ⟨U, hU⟩ z hyU, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Ideal.map_pow, hJC]
  let := Y.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  change ((hU.primeIdealOf ⟨y, hyU⟩).asIdeal.map
    (algebraMap Γ(Y, U) (Y.presheaf.stalk y))) ^ n =
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ^ n
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
    (Y.presheaf.stalk y)]


private theorem exists_ordinary_stalk_tensor_equiv {A B : Scheme.{u}} (f : A ⟶ B)
    (M : B.Modules) (x : A) :
    letI := (f.stalkMap x).hom.toAlgebra
    ∃ E : ((Scheme.Modules.pullback f).obj M).presheaf.stalk x ≃+
        TensorProduct (B.presheaf.stalk (f x)) (A.presheaf.stalk x)
          (M.presheaf.stalk (f x)),
      ∀ v : Γ(M, ⊤),
        E (((Scheme.Modules.pullback f).obj M).presheaf.germ ⊤ x trivial
          (pullbackΓ f M v)) =
        (1 : A.presheaf.stalk x) ⊗ₜ[B.presheaf.stalk (f x), (f.stalkMap x).hom]
          (M.presheaf.germ ⊤ (f x) trivial v) := by
  let α := ((Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)).app M
  let ε := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
    ((Scheme.Modules.toPresheaf A).mapIso α)
  obtain ⟨δ, hδ⟩ := exists_tensorPullback_stalk_iso f x
  let E := ε.addCommGroupIsoToAddEquiv.symm.trans (δ.app M).toLinearEquiv.toAddEquiv
  have hu (v : Γ(M, ⊤)) :
      α.hom.app ⊤ (tensorSectionsUnit f M v) = pullbackΓ f M v := by
    rw [tensor_unit_eq, pullbackΓ_def]
    exact congrArg (fun h ↦ h.app ⊤ v)
      ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_leftAdjointUniq_hom_app
        (pullbackPushforwardAdjunction f) M)
  have hg (v : Γ(M, ⊤)) : ε.hom
      (((tensorPullback f).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit f M v)) =
      ((Scheme.Modules.pullback f).obj M).presheaf.germ ⊤ x trivial
        (pullbackΓ f M v) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α.hom.mapPresheaf _ = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change ((Scheme.Modules.pullback f).obj M).presheaf.germ ⊤ x trivial
      (α.hom.app ⊤ (tensorSectionsUnit f M v)) = _
    rw [hu]
  refine ⟨E, fun v ↦ ?_⟩
  rw [← hg v]
  change (δ.hom.app M) (ε.addCommGroupIsoToAddEquiv.symm
    (ε.addCommGroupIsoToAddEquiv _)) = _
  rw [AddEquiv.symm_apply_apply, tensor_unit_eq]
  exact hδ M ⊤ trivial v

private theorem exists_tensor_stalk_unit {A B : Scheme.{u}} (f : A ⟶ B)
    (M : B.Modules) (x : A) :
    ∃ U : M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom]
        ((tensorPullback f).obj M).presheaf.stalk x,
      (∀ v : Γ(M, ⊤), U (M.presheaf.germ ⊤ (f x) trivial v) =
        ((tensorPullback f).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit f M v)) ∧
      (Function.Surjective (f.stalkMap x) → Function.Surjective U) := by
  let R := B.presheaf.stalk (f x)
  let T := A.presheaf.stalk x
  let P := M.presheaf.stalk (f x)
  let φ := (f.stalkMap x).hom
  let : Algebra R T := φ.toAlgebra
  obtain ⟨δ, hδ⟩ := exists_tensorPullback_stalk_iso f x
  let U₀ : P →ₛₗ[φ] T ⊗[R] P :=
    { toFun := fun m ↦ (1 : T) ⊗ₜ[R] m
      map_add' := fun _ _ ↦ TensorProduct.tmul_add _ _ _
      map_smul' := fun r m ↦ by
        simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
          mul_one]
        rfl }
  let U := (δ.app M).inv.hom.comp U₀
  refine ⟨U, ?_, ?_⟩
  · intro v
    apply (δ.app M).toLinearEquiv.injective
    change (δ.hom.app M) ((δ.inv.app M) _) = _
    simp only [← ConcreteCategory.comp_apply, δ.inv_hom_id_app, ModuleCat.id_apply]
    rw [tensor_unit_eq]
    exact (hδ M ⊤ trivial v).symm
  · intro hφ
    have hU₀ : Function.Surjective U₀ := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp [U₀]⟩
      | tmul r m =>
        obtain ⟨a, rfl⟩ := hφ r
        refine ⟨a • m, ?_⟩
        simp only [U₀, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_smul]
        change (φ a * 1) ⊗ₜ[R] m = φ a ⊗ₜ[R] m
        rw [mul_one]
      | add t t' ht ht' =>
        obtain ⟨m, rfl⟩ := ht
        obtain ⟨m', rfl⟩ := ht'
        exact ⟨m + m', U₀.map_add _ _⟩
    exact (δ.app M).toLinearEquiv.symm.surjective.comp hU₀

private theorem map_ideal_smul_top {R T P Q : Type u} [CommRing R] [CommRing T]
    [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module T Q]
    (φ : R →+* T) (U : P →ₛₗ[φ] Q) (I : Ideal R) (J : Ideal T)
    (hIJ : I ≤ J.comap φ) {m : P} (hm : m ∈ I • (⊤ : Submodule R P)) :
    U m ∈ J • (⊤ : Submodule T Q) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr m _
    rw [U.map_smulₛₗ]
    exact Submodule.smul_mem_smul (hIJ hr) (Submodule.mem_top : U m ∈ (⊤ : Submodule T Q))
  · intro m m' hm hm'
    simpa only [map_add] using add_mem hm hm'

private theorem ker_tensor_unit {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) (hφ : Function.Surjective φ) (P : ModuleCat.{u} R) :
    let := φ.toAlgebra
    LinearMap.ker (TensorProduct.mk R T P 1) =
      RingHom.ker φ • (⊤ : Submodule R P) := by
  let := φ.toAlgebra
  let g : R →ₗ[R] T := Algebra.linearMap R T
  have hg : Function.Surjective g := hφ
  have hk := (rTensor_exact P g.exact_subtype_ker_map hg).linearMap_ker_eq
  apply Submodule.comap_injective_of_surjective (TensorProduct.lid R P).surjective
  rw [← LinearMap.ker_comp]
  have heq : (TensorProduct.mk R T P 1).comp (TensorProduct.lid R P).toLinearMap =
      LinearMap.rTensor P g := by
    ext r
    simp [g]
  rw [heq, hk, Submodule.comap_equiv_eq_map_symm]
  symm
  rw [Submodule.map_symm_eq_iff, Submodule.map_range_rTensor_subtype_lid]
  rfl

/-- A single cotangent-valued jet is represented by a germ on the square-ideal
neighbourhood of a finite reduced closed subscheme. Any section with that germ has zero
residue and the specified jet at this one point. No simultaneous or global lifting is asserted.

Source: blueprint, finite-cover-curve proof, paragraph 2 (first infinitesimal neighbourhoods);
Stacks Project, Tags 01IN and 01J3, and Tag 0098 (stalks of module pullback).
(blueprint: lem-zl-prescribed-point-infinitesimal-model).

Proof: Excluding the other finitely many closed points makes the reduced ideal stalk the
maximal ideal m of O_(Y,j(x)). The square ideal has stalk m^2, so the thickened local ring
is O_(Y,j(x))/m^2. Its pulled-back module stalk is M_(Y,j(x))/m^2 M_(Y,j(x)). Use the
open-immersion stalk isomorphisms to transport the chosen invertible frame in
prescribedPointJet to this stalk. In that frame a cotangent tensor has the form c tensor e,
where c belongs to m/m^2: tensoring a free module of rank one identifies the tensor with
m/m^2. Choose a representative a in m of c and take the class of a*e in M/m^2 M as q.
If a global section restricts to q, its coefficient differs from a by an element of m^2.
It therefore belongs to m and has cotangent class c. The defining formula for
prescribedPointJet gives exactly the original tensor. The ordinary pullback unit and the
tensor-pullback unit agree through the unique adjunction comparison, which is used in
identifying these germ maps. This is local at z and makes no claim that q extends globally.
-/
private theorem exists_finiteSquarePoint_jet_germ
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : TopologicalSpace.Closeds Y) (hfinite : (C : Set Y).Finite)
    (hclosed : ∀ y ∈ C, IsClosed ({y} : Set Y))
    (M : Y.Modules) [M.IsInvertible]
    [((tensorPullback j).obj M).IsInvertible]
    (x : X) (z : ((Scheme.IdealSheafData.vanishingIdeal C) ^ 2).subscheme)
    (hz : ((Scheme.IdealSheafData.vanishingIdeal C) ^ 2).subschemeι z = j x)
    (b : PrescribedPointJet ((tensorPullback j).obj M) x) :
    ∃ q : ((Scheme.Modules.pullback
        ((Scheme.IdealSheafData.vanishingIdeal C) ^ 2).subschemeι).obj M).presheaf.stalk z,
      ∀ v : Γ(M, ⊤),
        ((Scheme.Modules.pullback
          ((Scheme.IdealSheafData.vanishingIdeal C) ^ 2).subschemeι).obj M).presheaf.germ
            ⊤ z trivial
            (pullbackΓ ((Scheme.IdealSheafData.vanishingIdeal C) ^ 2).subschemeι M v) = q →
        (((tensorPullback j).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit j M v) ∈
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x)
              (((tensorPullback j).obj M).presheaf.stalk x))) ∧
        prescribedPointJet ((tensorPullback j).obj M) x (tensorSectionsUnit j M v) = b := by
  classical
  let J := Scheme.IdealSheafData.vanishingIdeal C
  let W := (J ^ 2).subscheme
  let w : W ⟶ Y := (J ^ 2).subschemeι
  have hy : j x ∈ (J ^ 2).support := by
    exact (show (J ^ 2).subschemeι z ∈ (J ^ 2).support from z.property) |>
      fun h ↦ hz ▸ h
  let z' : W := ⟨j x, hy⟩
  suffices h : ∃ q : ((Scheme.Modules.pullback w).obj M).presheaf.stalk z',
      ∀ v : Γ(M, ⊤),
        ((Scheme.Modules.pullback w).obj M).presheaf.germ ⊤ z' trivial
          (pullbackΓ w M v) = q →
        (((tensorPullback j).obj M).presheaf.germ ⊤ x trivial (tensorSectionsUnit j M v) ∈
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x)
              (((tensorPullback j).obj M).presheaf.stalk x))) ∧
        prescribedPointJet ((tensorPullback j).obj M) x (tensorSectionsUnit j M v) = b by
    have hzz : z' = z := Subtype.ext hz.symm
    exact hzz ▸ h
  let R := Y.presheaf.stalk (j x)
  let T := X.presheaf.stalk x
  let L := (tensorPullback j).obj M
  let e := Classical.choice (invertible_stalk_linearEquiv X L x)
  obtain ⟨a, hb⟩ := exists_cotangent_frame_representative e b
  obtain ⟨U, hUgerm, hUsurj⟩ := exists_tensor_stalk_unit j M x
  obtain ⟨m, hm⟩ := hUsurj (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).surjective
    (e.symm a.val)
  obtain ⟨E₁, hE₁⟩ := exists_ordinary_stalk_tensor_equiv w M z'
  let φ := (w.stalkMap z').hom
  let T' := W.presheaf.stalk z'
  let : Algebra R T' := φ.toAlgebra
  let P : ModuleCat.{u} R := ModuleCat.of R (M.presheaf.stalk (j x))
  let E : ((Scheme.Modules.pullback w).obj M).presheaf.stalk z' ≃+
      TensorProduct R T' (M.presheaf.stalk (j x)) := E₁
  have hE (v : Γ(M, ⊤)) :
      E (((Scheme.Modules.pullback w).obj M).presheaf.germ ⊤ z' trivial
        (pullbackΓ w M v)) = (1 : T') ⊗ₜ[R] (M.presheaf.germ ⊤ (j x) trivial v) :=
    hE₁ v
  refine ⟨E.symm ((1 : T') ⊗ₜ[R] m), fun v hv ↦ ?_⟩
  have htensor : (1 : T') ⊗ₜ[R] (M.presheaf.germ ⊤ (j x) trivial v) =
      (1 : T') ⊗ₜ[R] m := by
    erw [← hE v, hv, E.apply_symm_apply]
  have hdiff : M.presheaf.germ ⊤ (j x) trivial v - m ∈
      (IsLocalRing.maximalIdeal R) ^ 2 • (⊤ : Submodule R P) := by
    have hr : Set.range w = (C : Set Y) := by
      change Set.range (J ^ 2).subschemeι = (C : Set Y)
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
    have hkernel : RingHom.ker φ = (IsLocalRing.maximalIdeal R) ^ 2 :=
      finitePoint_ideal_stalk_kernel_pow C hfinite hclosed 2 z' (hr.le ⟨z', rfl⟩)
    rw [← hkernel, ← ker_tensor_unit φ (w.stalkMap_surjective z') P]
    change (1 : T') ⊗ₜ[R] (M.presheaf.germ ⊤ (j x) trivial v - m) = 0
    rw [TensorProduct.tmul_sub, htensor, sub_self]
  have hIJ : (IsLocalRing.maximalIdeal R) ^ 2 ≤
      ((IsLocalRing.maximalIdeal T) ^ 2).comap (j.stalkMap x).hom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le (j.stalkMap x).hom) 2
  have hc := map_ideal_smul_top (j.stalkMap x).hom U _ _ hIJ hdiff
  have hcoeff := (frame_mem_ideal e _ _).mp hc
  let av := e (L.presheaf.germ ⊤ x trivial (tensorSectionsUnit j M v))
  have heq : e (U (M.presheaf.germ ⊤ (j x) trivial v - m)) = av - a.val := by
    calc
      _ = e (U (M.presheaf.germ ⊤ (j x) trivial v) - U m) :=
        congrArg e (U.map_sub _ _)
      _ = e (U (M.presheaf.germ ⊤ (j x) trivial v)) - e (U m) := e.map_sub _ _
      _ = av - a.val := congrArg₂ (fun p q : T ↦ p - q)
        (congrArg e (hUgerm v)) ((congrArg e hm).trans (e.apply_symm_apply a.val))
  have hc' : av - a.val ∈ (IsLocalRing.maximalIdeal T) ^ 2 := heq ▸ hcoeff
  have hav : av ∈ IsLocalRing.maximalIdeal T := by
    have hmem := (IsLocalRing.maximalIdeal T).add_mem
      (Ideal.pow_le_self (by decide : 2 ≠ 0) hc') a.property
    simpa only [sub_add_cancel] using hmem
  refine ⟨(frame_mem_ideal e _ _).mpr hav, ?_⟩
  unfold prescribedPointJet
  change (if h : av ∈ IsLocalRing.maximalIdeal T then
    TensorProduct.tmul T ((IsLocalRing.maximalIdeal T).toCotangent ⟨av, h⟩) (e.symm 1)
      else 0) = b
  rw [dif_pos hav]
  rw [(IsLocalRing.maximalIdeal T).toCotangent_eq.mpr hc']
  exact hb


/-- On a discrete scheme every family of module germs is represented by one section. -/
private theorem exists_section_of_discrete_germs {W : Scheme.{u}}
    [DiscreteTopology W] (F : W.Modules) (b : (x : W) → F.presheaf.stalk x) :
    ∃ t : Γ(F, ⊤), ∀ x, F.presheaf.germ ⊤ x trivial t = b x := by
  classical
  let U (x : W) : W.Opens := ⟨{x}, isOpen_discrete _⟩
  have hx (x : W) : x ∈ U x := Set.mem_singleton x
  choose V hxV s hs using fun x ↦ F.presheaf.exists_germ_eq (b x)
  have hUV (x : W) : U x ≤ V x := by
    intro y hy
    have : y = x := hy
    subst y
    exact hxV x
  let a (x : W) : Γ(F, U x) := F.presheaf.map (homOfLE (hUV x)).op (s x)
  let A : TopCat.Sheaf AddCommGrpCat.{u} W.toTopCat := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf U a := by
    intro x y
    apply TopCat.Presheaf.section_ext A
    intro z hz
    have hzx : z = x := hz.1
    have hzy : z = y := hz.2
    subst x
    subst y
    rfl
  obtain ⟨t, ht, _⟩ := A.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (by intro x _; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩) a hcompat
  refine ⟨t, fun x ↦ ?_⟩
  calc
    F.presheaf.germ ⊤ x trivial t = F.presheaf.germ (U x) x (hx x) (a x) := by
      rw [← ht x]
      exact (F.presheaf.germ_res_apply (homOfLE le_top) x (hx x) t).symm
    _ = b x := by
      rw [F.presheaf.germ_res_apply]
      exact hs x

/-- Compare the reduced finite subscheme and its square-ideal thickening with residue
vanishing and the concrete jet map. The interpolation is on the finite thickening only;
no global section on `Y` is asserted to exist.

Source: blueprint, finite-cover-curve proof, paragraph 2, displayed jet map;
Stacks Project, Tag 01IN, closed subschemes and quasi-coherent ideals.
(blueprint: lem-zl-prescribed-point-infinitesimal-model).

Proof: The locally finite-type `k`-scheme `Y` is Jacobson. The open immersion carries
the closed points of `X` to locally closed points, which are therefore closed in `Y`.
Let `J` be the vanishing
ideal of their finite union, let `Z` be its closed subscheme and `W` that of `J^2`.
Their supports agree with this union, so `W` has finite support. In the stalk at an
image of `x`, `J` is the maximal ideal. Trivialize the invertible module there.
Restriction to `Z` is zero exactly when the coefficient lies in that maximal ideal;
the stalk isomorphism for the open immersion gives the stated kernel equivalence.
Restriction to `W` has coefficient in the quotient by the square of the maximal ideal.
The ideal of `Z` inside `W` is therefore the cotangent space, tensored with the module
stalk. In the frame chosen by `prescribedPointJet`, this identification sends a
coefficient `a` to `[a]` tensor the frame generator; changing frames cancels the unit
in the two factors. Given a tuple of jets, represent each one in that square-zero
ideal. Since the underlying space of `W` is finite and discrete, each germ has a
representative on its singleton open. The sheaf axiom glues these representatives
to `t` on `W`. Every global lift of `t` consequently vanishes at the
points and has the prescribed jets. This also treats the empty set, with empty `W`.
-/
theorem exists_prescribedPoint_infinitesimalModel
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ (Y ↘ Spec (.of k)) =
      X ↘ Spec (.of k))
    (S : Finset X) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    ∃ (Z W : Scheme.{u}) (i : Z ⟶ Y) (w : W ⟶ Y)
      (_ : IsClosedImmersion i) (_ : IsClosedImmersion w),
      Set.range i = j '' (S : Set X) ∧
      (Set.range w).Finite ∧ w.ker = i.ker ^ 2 ∧
      ∀ (M : Y.Modules) [M.IsInvertible],
        (∀ v : Γ(M, ⊤), pullbackΓ i M v = 0 ↔
          prescribedPointVanishes ((tensorPullback j).obj M) S (tensorSectionsUnit j M v)) ∧
        ∀ (hMj : ((tensorPullback j).obj M).IsInvertible)
          (b : (x : S) → PrescribedPointJet ((tensorPullback j).obj M) x.val),
          ∃ t : Γ((Scheme.Modules.pullback w).obj M, ⊤),
            ∀ v : Γ(M, ⊤), pullbackΓ w M v = t →
              prescribedPointVanishes ((tensorPullback j).obj M) S
                (tensorSectionsUnit j M v) ∧
              ∀ x : S, @prescribedPointJet X ((tensorPullback j).obj M) hMj x.val
                (tensorSectionsUnit j M v) = b x := by
  classical
  have _ := hj
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (.of k))
  have hpoint (x : X) (hx : x ∈ S) : IsClosed ({j x} : Set Y) := by
    apply isClosed_singleton_of_isLocallyClosed_singleton
    rw [← Set.image_singleton]
    exact (hclosed x hx).isLocallyClosed.image j.isOpenEmbedding.isInducing
      j.isOpenEmbedding.isOpen_range.isLocallyClosed
  have hCclosed : IsClosed (j '' (S : Set X)) := by
    rw [← Set.biUnion_of_singleton (s := (S : Set X)), Set.image_iUnion₂]
    exact S.finite_toSet.isClosed_biUnion (fun x hx ↦ by
      simpa only [Set.image_singleton] using hpoint x hx)
  let C : TopologicalSpace.Closeds Y := ⟨j '' (S : Set X), hCclosed⟩
  let J := Scheme.IdealSheafData.vanishingIdeal C
  let Z := J.subscheme
  let W := (J ^ 2).subscheme
  let i : Z ⟶ Y := J.subschemeι
  let w : W ⟶ Y := (J ^ 2).subschemeι
  have hiRange : Set.range i = (C : Set Y) := by
    change Set.range J.subschemeι = (C : Set Y)
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hwRange : Set.range w = (C : Set Y) := by
    change Set.range (J ^ 2).subschemeι = (C : Set Y)
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hCfinite : (C : Set Y).Finite := S.finite_toSet.image j
  have hCpoints : ∀ y ∈ C, IsClosed ({y} : Set Y) := by
    rintro y ⟨x, hx, rfl⟩
    exact hpoint x hx
  have : Finite W := by
    have : Finite (C : Set Y) := hCfinite.to_subtype
    exact Finite.of_injective (fun z : W ↦ (⟨w z, hwRange.le ⟨z, rfl⟩⟩ : C))
      (fun z z' h ↦ w.isClosedEmbedding.injective (congrArg Subtype.val h))
  have : T1Space W := ⟨fun z ↦ w.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
    (by simpa only [Set.image_singleton] using hCpoints (w z) (hwRange.le ⟨z, rfl⟩))⟩
  refine ⟨Z, W, i, w, inferInstance, inferInstance, hiRange, ?_, ?_, ?_⟩
  · rw [hwRange]
    exact hCfinite
  · simp only [w, i, Scheme.IdealSheafData.ker_subschemeι]
  · intro M hM
    constructor
    · intro v
      let F := (Scheme.Modules.pullback i).obj M
      let A : TopCat.Sheaf AddCommGrpCat.{u} Z.toTopCat := ⟨F.presheaf, F.isSheaf⟩
      constructor
      · intro hv x hx
        obtain ⟨z, hz⟩ := hiRange.ge (show j x ∈ (C : Set Y) from ⟨x, hx, rfl⟩)
        apply (finiteReducedPoint_residue_germ_iff j C hCfinite hCpoints M x z hz v).mp
        change F.presheaf.germ ⊤ z trivial (pullbackΓ i M v) = 0
        rw [hv, map_zero]
      · intro hv
        apply TopCat.Presheaf.section_ext A
        intro z _
        obtain ⟨x, hx, heq⟩ := hiRange.le ⟨z, rfl⟩
        rw [map_zero]
        exact (finiteReducedPoint_residue_germ_iff j C hCfinite hCpoints M x z
          heq.symm v).mpr (hv x hx)
    · intro hMj b
      let f : W → S := fun z ↦
        ⟨(hwRange.le ⟨z, rfl⟩).choose, (hwRange.le ⟨z, rfl⟩).choose_spec.1⟩
      have hf (z : W) : w z = j (f z).val :=
        (hwRange.le ⟨z, rfl⟩).choose_spec.2.symm
      choose q hq using fun z : W ↦
        exists_finiteSquarePoint_jet_germ j C hCfinite hCpoints M (f z).val z (hf z)
          (b (f z))
      obtain ⟨t, ht⟩ := exists_section_of_discrete_germs ((Scheme.Modules.pullback w).obj M) q
      refine ⟨t, fun v hv ↦ ?_⟩
      have hlocal (x : S) :
          ((tensorPullback j).obj M).presheaf.germ ⊤ x.val trivial
              (tensorSectionsUnit j M v) ∈
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x.val)) •
              (⊤ : Submodule (X.presheaf.stalk x.val)
                (((tensorPullback j).obj M).presheaf.stalk x.val)) ∧
          prescribedPointJet ((tensorPullback j).obj M) x.val
            (tensorSectionsUnit j M v) = b x := by
        obtain ⟨z, hz⟩ := hwRange.ge (show j x.val ∈ (C : Set Y) from
          ⟨x.val, x.property, rfl⟩)
        have hfx : f z = x := Subtype.ext (j.isOpenEmbedding.injective ((hf z).symm.trans hz))
        have h := hq z v (by rw [hv]; exact ht z)
        exact hfx ▸ h
      exact ⟨fun x hx ↦ (hlocal ⟨x, hx⟩).1, fun x ↦ (hlocal x).2⟩

end

end AlgebraicGeometry
