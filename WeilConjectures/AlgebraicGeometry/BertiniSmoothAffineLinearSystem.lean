/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.StdBasis
import WeilConjectures.AlgebraicGeometry.BertiniPrescribedPointSmoothSystem
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsImmersionReindex
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-! # An affine coordinate presentation of the prescribed-point smooth system

Source: the current blueprint, finite-cover-curve proof, paragraph 2;
Stacks Project, Tags 0FD5 and 0FD6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

private theorem cachedSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := by
  infer_instance

private theorem cachedWEquals (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  infer_instance

attribute [local instance] cachedSheafify cachedWEquals
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local irreducible] tensorPullback tensorPullbackObj
  ProjectiveSpace.homOfGeneratingSections tensorSectionsUnit prescribedPointCombination
  prescribedPointRestrictedFamily prescribedPointMember prescribedPointVanishes
attribute [local irreducible] ProjectiveSpace Proj Proj.toSpecBase

private theorem exists_projective_chart
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X]
    [ConnectedSpace X] [Smooth (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    ∃ (N : ℕ) (Y : Scheme.{u}) (_ : IsReduced Y)
      (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (_ : IsClosedImmersion c)
      (j : X ⟶ Y) (_ : IsOpenImmersion j), DenseRange j ∧
      Set.range j = c ⁻¹' (ProjectiveSpace.standardOpen
        (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ⟨0⟩ : Set _) ∧
      j ≫ c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)) =
        X ↘ Spec (.of k) := by
  classical
  let f := X ↘ Spec (.of k)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular X := IsRegular.of_smooth f
  have : IsIntegral X := IsRegular.isIntegral X
  let : Algebra k Γ(X, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, ⊤) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance)
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨N, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k Γ(X, ⊤))
  let e : {i : ULift.{u} (Fin (N + 1)) // i ≠ ⟨0⟩} ≃ Fin N :=
    (Equiv.subtypeEquiv (Equiv.ulift) (by
      intro i
      exact not_congr ⟨fun h ↦ congrArg ULift.down h, fun h ↦ ULift.ext _ _ h⟩)).trans
      (finSuccAboveEquiv 0).symm
  let v : {i : ULift.{u} (Fin (N + 1)) // i ≠ ⟨0⟩} → Γ(X, ⊤) :=
    fun i ↦ q (MvPolynomial.X (e i))
  have hv : Algebra.adjoin k (Set.range v) = ⊤ := by
    have hr : Set.range v = Set.range (fun i : Fin N ↦ q (MvPolynomial.X i)) := by
      exact e.surjective.range_comp (fun i : Fin N ↦ q (MvPolynomial.X i))
    rw [hr, Algebra.adjoin_range_eq_range_aeval]
    have heval : MvPolynomial.aeval (fun i : Fin N ↦ q (MvPolynomial.X i)) = q := by
      ext i
      simp
    rw [heval, AlgHom.range_eq_top]
    exact hq
  have : IsDomain Γ(X, ⊤) := inferInstance
  obtain ⟨A, _, _, 𝒜, _, _, _, l, hl, hcov, _, c, _, hc, hover,
    ⟨x₀, hx₀, hsp⟩, ψ, hψ⟩ := Proj.exists_isClosedImmersion_chart
      (k := k) (K := Γ(X, ⊤)) (n := ULift.{u} (Fin (N + 1))) ⟨0⟩ v hv
  have : IsReduced (Proj 𝒜) := Proj.isReduced_of_isDomain 𝒜
  let U := c ⁻¹ᵁ ProjectiveSpace.standardOpen
    (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ⟨0⟩
  let j : X ⟶ Proj 𝒜 := X.isoSpec.hom ≫ ψ.hom ≫ U.ι
  have hj : IsOpenImmersion j := inferInstance
  have hrange : Set.range j = (U : Set (Proj 𝒜)) := by
    have hs : Function.Surjective (fun x : X ↦ ψ.hom (X.isoSpec.hom x)) :=
      ψ.hom.homeomorph.surjective.comp X.isoSpec.hom.homeomorph.surjective
    change Set.range (U.ι ∘ (fun x : X ↦ ψ.hom (X.isoSpec.hom x))) = _
    rw [hs.range_comp U.ι]
    exact U.range_ι
  have hdense : DenseRange j := by
    rw [DenseRange, hrange]
    intro x
    exact (hsp x).mem_closed isClosed_closure (subset_closure hx₀)
  refine ⟨N, Proj 𝒜, inferInstance, c, hc, j, hj, hdense, hrange, ?_⟩
  have hbase : ψ.hom ≫ U.ι ≫ Proj.toSpecBase 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤))) := by
    have hh := congrArg (fun g ↦ g ≫
      (𝔸({i : ULift.{u} (Fin (N + 1)) // i ≠ ⟨0⟩}; Spec (.of k)) ↘ Spec (.of k))) hψ
    simpa only [Category.assoc, ProjectiveSpace.standardOpenIso_hom_over,
      morphismRestrict_ι_assoc, hover, AffineSpace.homOfVector_over] using hh
  dsimp only [j]
  rw [Category.assoc, Category.assoc, hover, hbase]
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

private theorem tensorUnit_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (r : Γ(Y, ⊤)) (s : Γ(M, ⊤)) :
    tensorSectionsUnit f M (r • s) = f.appTop r • tensorSectionsUnit f M s := by
  rw [tensorUnit_eq]
  exact Hom.app_smul _ r s

private theorem tensorUnit_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules) :
    tensorSectionsUnit b M ≫ tensorSectionsUnit a ((tensorPullback b).obj M) ≫
      ((tensorSectionsComp a b).hom.app M).app ⊤ = tensorSectionsUnit (a ≫ b) M := by
  have hu := congrArg (fun t ↦ t.app ⊤)
    (unit_conjugateEquiv_symm (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b)))
      ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
        (Classical.choose (exists_tensorPullbackAdjunction a)))
      (pushforwardComp a b).inv M)
  rw [tensorUnit_eq, tensorUnit_eq, tensorUnit_eq]
  simp only [Adjunction.comp_unit_app, Hom.comp_app, pushforward_map_app,
    Functor.comp_map, pushforwardComp_inv_app_app] at hu
  change _ ≫ 𝟙 _ = _ at hu
  rw [Category.comp_id] at hu
  exact hu.symm

set_option maxHeartbeats 1000000 in
-- The dependent finite-system interface and its section conversions use this budget.
/-- A prescribed-point system on an affine smooth scheme, in finite basis coordinates.
No covering scheme or irreducibility condition is involved.

Source: blueprint `lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 2;
Stacks Project, Tags 0FD5 and 0FD6.
(blueprint: lem-zl-bertini-smooth-affine-linear-system).

Proof: Embed X into affine space using finite generation of its coordinate algebra over k,
and take its reduced projective closure. Smooth connected X is reduced, so it is the dense
standard affine chart of this closure. Apply the eventual prescribed-point smooth-system
lemma to the finite reduced closed set S and choose a twist beyond its bound. Pull that
twist back to X to obtain L. Choose an enumeration of the finite kernel basis and transport
its coefficient space to Fin r → k. Send a coefficient tuple to the restriction of its
linear combination. The pullback unit is additive and respects the structure-map scalar
action, proving the two linearity clauses. The kernel property gives vanishing on S.
The tensor-pullback composition isomorphism identifies the restricted generating family
and its projective morphism with those supplied by the smooth-system lemma. Transport the
coefficient open along the same permutation of polynomial coordinates. Its members are
exactly the restricted zero schemes, hence smooth, affine, and pure of dimension d-1.
This is only the smooth-system construction, before imposing any finite-cover condition.
-/
theorem exists_smooth_affine_prescribedPoint_linearSystem
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    ∃ (U₀ : X.Opens), (U₀ : Set X) = (S : Set X)ᶜ ∧
    ∃ (L : X.Modules) (_ : L.IsInvertible) (r : ℕ) (ψ : (Fin r → k) →+ Γ(L, ⊤)),
      (∀ (c : k) (v : Fin r → k),
        ψ (c • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v) ∧
      (∀ (v : Fin r → k) (x : X), x ∈ S →
        x ∈ (homOfGlobalSection L (ψ v)).zeroLocus.support) ∧
      ∃ hgen : Epi (((tensorPullback U₀.ι).obj L).freeHomEquiv.symm
        (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
          (homOfGlobalSection _ (tensorSectionsUnit U₀.ι L (ψ (Pi.basisFun k (Fin r) i.down)))))),
        IsImmersion (@ProjectiveSpace.homOfGeneratingSections
          (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
          (U₀.ι ≫ (X ↘ Spec (.of k))) ((tensorPullback U₀.ι).obj L)
          (Scheme.Modules.IsInvertible.of_iso
            (((Classical.choose (exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
              (pullbackPushforwardAdjunction U₀.ι)).app L).symm)
          (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
            (homOfGlobalSection _
              (tensorSectionsUnit U₀.ι L (ψ (Pi.basisFun k (Fin r) i.down))))) hgen) ∧
        ∃ O : (Spec (.of (MvPolynomial (Fin r) k))).Opens,
          (O : Set (Spec (.of (MvPolynomial (Fin r) k)))).Nonempty ∧
          ∀ a : Fin r → k,
            Set.range (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) a))) ⊆
              (O : Set _) →
            Smooth ((homOfGlobalSection L (ψ a)).zeroLocus.subschemeι ≫
              (X ↘ Spec (.of k))) ∧
            IsAffine (homOfGlobalSection L (ψ a)).zeroLocus.subscheme ∧
            (homOfGlobalSection L (ψ a)).zeroLocus.subscheme.IsPureDimension (d - 1) := by
  classical
  obtain ⟨N, Y, hY, c, hc, j, hj, hdense, hchart, hover⟩ := exists_projective_chart (k := k) X
  let := hY
  let := hc
  let := hj
  obtain ⟨n₀, U, hU, hsystems⟩ := exists_eventual_prescribedPoint_smoothSystem
    X d hd hdim S hS hclosed N Y c j hdense hchart hover
  obtain ⟨I, hI, s, hkernel, hgen, _, O, hO, hmembers⟩ := hsystems n₀ le_rfl
  let := hI
  let M := prescribedPointTwist c n₀
  let f := c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k))
  let L := (tensorPullback j).obj M
  let : M.IsInvertible :=
    ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n₀ : ℤ))).2
  let : L.IsInvertible := ((invertible_pullback_tensor j).1 M).2
  let r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let ψ : (Fin r → k) →+ Γ(L, ⊤) :=
    { toFun := fun a ↦ tensorSectionsUnit j M
        (prescribedPointCombination f M s (fun i ↦ a (e i)))
      map_zero' := by
        simp only [prescribedPointCombination, Pi.zero_apply, map_zero, zero_smul,
          Finset.sum_const_zero]
      map_add' := by
        intro a b
        simp only [prescribedPointCombination, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] }
  have hlinear (a : k) (v : Fin r → k) :
      ψ (a • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a) • ψ v := by
    change tensorSectionsUnit j M (prescribedPointCombination f M s
      (fun i ↦ a * v (e i))) = _
    have hsum : prescribedPointCombination f M s (fun i ↦ a * v (e i)) =
        f.appTop ((Scheme.ΓSpecIso (.of k)).inv a) •
          prescribedPointCombination f M s (fun i ↦ v (e i)) := by
      simp only [prescribedPointCombination, map_mul, mul_smul, Finset.smul_sum]
    rw [hsum, tensorUnit_smul]
    change (j ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv a) • _ = _
    rw [show j ≫ f = X ↘ Spec (.of k) by simpa only [f, Category.assoc] using hover]
    rfl
  have hzero : prescribedPointCombination f M s (0 : I → k) = 0 := by
    simp only [prescribedPointCombination, Pi.zero_apply, map_zero, zero_smul,
      Finset.sum_const_zero]
  have hsub (a b : I → k) : prescribedPointCombination f M s (a - b) =
      prescribedPointCombination f M s a - prescribedPointCombination f M s b := by
    simp only [prescribedPointCombination, Pi.sub_apply, map_sub, sub_smul,
      Finset.sum_sub_distrib]
  obtain ⟨a₀, _, ha₀⟩ := (hkernel 0).mp (by
    unfold prescribedPointVanishes
    intro x hx
    simp only [map_zero]
    exact Submodule.zero_mem _)
  have hinj : Function.Injective (prescribedPointCombination f M s) := by
    intro a b hab
    have hab₀ : prescribedPointCombination f M s (a - b) = 0 := by
      rw [hsub, hab, sub_self]
    exact sub_eq_zero.mp ((ha₀ _ hab₀).trans (ha₀ _ hzero).symm)
  have hvan (a : Fin r → k) (x : X) (hx : x ∈ S) :
      x ∈ (homOfGlobalSection L (ψ a)).zeroLocus.support := by
    have hv : prescribedPointVanishes L S (ψ a) :=
      (hkernel _).mpr ⟨fun i ↦ a (e i), rfl, fun b hb ↦ hinj hb⟩
    unfold prescribedPointVanishes at hv
    have hn : x ∉ nonvanishingLocus L (ψ a) := not_not_intro (hv x hx)
    rw [nonvanishingLocus_eq_compl_support_zeroLocus X L (ψ a)] at hn
    exact not_not.mp hn
  have hbasis (i : Fin r) :
      ψ (Pi.basisFun k (Fin r) i) = tensorSectionsUnit j M (s (e.symm i)) := by
    change tensorSectionsUnit j M (prescribedPointCombination f M s
      (fun l ↦ (Pi.basisFun k (Fin r) i) (e l))) = _
    congr 1
    unfold prescribedPointCombination
    rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro l _ hli
      have hne : i ≠ e l := by
        intro h
        exact hli (e.injective (by simpa using h.symm))
      simp [Pi.basisFun_apply, hne]
    · simp
  let α := (tensorSectionsComp U.ι j).symm.app M
  have hα (i : I) : α.hom.app ⊤ (tensorSectionsUnit (U.ι ≫ j) M (s i)) =
      tensorSectionsUnit U.ι L (tensorSectionsUnit j M (s i)) := by
    have hh := ConcreteCategory.congr_hom (tensorUnit_comp U.ι j M) (s i)
    change ((tensorSectionsComp U.ι j).hom.app M).app ⊤
      (tensorSectionsUnit U.ι L (tensorSectionsUnit j M (s i))) = _ at hh
    rw [← hh]
    change ((tensorSectionsComp U.ι j).inv.app M).app ⊤
      (((tensorSectionsComp U.ι j).hom.app M).app ⊤ _) = _
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id_app, Hom.id_app]
    rfl
  let : ((tensorPullback U.ι).obj L).IsInvertible :=
    ((invertible_pullback_tensor U.ι).1 L).2
  let : ((tensorPullback (U.ι ≫ j)).obj M).IsInvertible :=
    ((invertible_pullback_tensor (U.ι ≫ j)).1 M).2
  have hgen' := ProjectiveSpace.generatingSections_immersion_iso_reindex
    (U.ι ≫ (X ↘ Spec (.of k))) ((Equiv.ulift).trans e.symm)
    ((tensorPullback (U.ι ≫ j)).obj M) ((tensorPullback U.ι).obj L) α
    (fun i ↦ tensorSectionsUnit (U.ι ≫ j) M (s i))
    (fun i : ULift.{u} (Fin r) ↦ tensorSectionsUnit U.ι L
      (ψ (Pi.basisFun k (Fin r) i.down)))
    (by intro i; rw [hbasis]; exact hα (e.symm i.down))
    (by
      unfold prescribedPointRestrictedFamily at hgen
      unfold bertiniSectionFamily at hgen
      exact hgen)
  obtain ⟨hgen', himm⟩ := hgen'
  refine ⟨U, Set.ext (fun x ↦ hU x), L, inferInstance, r, ψ, hlinear, hvan,
    hgen', himm, ?_⟩
  let qring : CommRingCat.of (MvPolynomial I k) ⟶ CommRingCat.of (MvPolynomial (Fin r) k) :=
    CommRingCat.ofHom (MvPolynomial.renameEquiv k e).toRingHom
  have : IsIso qring :=
    (ConcreteCategory.isIso_iff_bijective qring).mpr (MvPolynomial.renameEquiv k e).bijective
  let qspec := Spec.map qring
  refine ⟨qspec ⁻¹ᵁ O, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hO
    obtain ⟨y, hy⟩ := qspec.homeomorph.surjective x
    change qspec y = x at hy
    exact ⟨y, by change qspec y ∈ O; rwa [hy]⟩
  · intro a ha
    have heval : Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) a)) ≫
        qspec = bertiniCoefficientPoint (k := k) (fun i ↦ a (e i)) := by
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply MvPolynomial.ringHom_ext
      · intro z
        simp [qring]
      · intro i
        simp [qring]
    have ha' : Set.range (bertiniCoefficientPoint (k := k) (fun i ↦ a (e i))) ⊆ (O : Set _) := by
      rw [← heval]
      rintro _ ⟨z, rfl⟩
      exact ha ⟨z, rfl⟩
    obtain ⟨hsmooth, haff, hdim, _, _⟩ := hmembers (fun i ↦ a (e i)) ha'
    unfold prescribedPointMember at hsmooth haff hdim
    exact ⟨hsmooth, haff, hdim⟩

end

end AlgebraicGeometry
