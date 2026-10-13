/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoCoherentModuleExtension
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison
import Mathlib.RingTheory.Finiteness.Basic

/-! # Coherence and depth of the canonical boundary pushforward algebra

Source: Stacks Project, Tag 0EY6(1), and the depth assertion in its proof of (2).
(blueprint: lem-sbc-depth-two-pushforward-coherence)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

private theorem depth_eq_of_linearEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (e : M ≃ₗ[R] P) : IsLocalRing.depth (R := R) M = IsLocalRing.depth (R := R) P := by
  have hmap : (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).map e.toLinearMap =
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have htop : (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤) ↔
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R P) = ⊤) := by
    constructor
    · intro h
      rw [← hmap, h]
      simp
    · intro h
      rw [← hmap] at h
      exact (Submodule.map_eq_top_iff.mp h)
  unfold IsLocalRing.depth Ideal.depth
  split_ifs with hM hP hP
  · rfl
  · exact (hP (htop.mp hM)).elim
  · exact (hM (htop.mpr hP)).elim
  · congr 1
    ext n
    constructor
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mp hreg, hmem, rfl⟩
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mpr hreg, hmem, rfl⟩

/-- The actual direct image algebra is quasi-coherent, finite on affine opens, and
has finite stalk modules of depth at least two on the boundary.

Source: Stacks Project, Tag 0EY6(1), proof of (2); Tag 0E9I.
(blueprint: lem-sbc-depth-two-pushforward-coherence)

Proof: On an affine Noetherian open V of L, U intersect V is quasi-compact.
The finite etale algebra on this intersection is finite locally free. Extend its
underlying module to a finite coherent module M on V, and take N = M double dual.
Dualization of finite presentations commutes with localization, so N restricts to
that locally free module. At each missing stalk, present M dual by finite free
modules. Dualizing realizes N as the kernel of a map between finite free modules.
A regular pair x,y for the base stalk is regular on this kernel: x is injective;
if y n = x nprime in the kernel, regularity in the free source writes n = x m.
Then x d(m) = 0 in the free target implies d(m) = 0, so m is in the kernel.
Thus N has depth at least two wherever its stalk is nonzero; a zero stalk has
infinite depth. Hartogs restriction, Tag 0E9I, identifies N with the pushforward
of the original module. These identifications are canonical restriction maps,
so the affine descriptions identify with the actual algebra direct image and
agree on overlaps. Hence it is quasi-coherent and finite on every affine open,
and its stalk modules are finite with the asserted depth. This is local on L;
no global quasi-compactness is needed. Empty covers yield the zero algebra. -/
theorem depth_two_pushforward_coherence
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f] :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    B.toModule.IsQuasicoherent ∧
      (∀ V : L.Opens, IsAffineOpen V → (B.hom.hom.app (op V)).hom.Finite) ∧
      ∀ y : L, y ∉ U →
        letI : Algebra (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj) :=
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map B.hom.hom).hom.toAlgebra
        ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj),
          letI := hfinite
          (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj) := by
  obtain ⟨N, hqc, hsections, hdepth, hrestrict⟩ :=
    exists_depth_two_coherent_module_extension U hboundary f
  obtain ⟨⟨e⟩, hstalk⟩ :=
    depth_two_hartogs_algebra_comparison U f N hqc hsections hdepth hrestrict
  refine ⟨(SheafOfModules.isQuasicoherent L.ringCatSheaf).prop_of_iso e hqc, ?_, ?_⟩
  · intro V hV
    have hN : Module.Finite (L.ringCatSheaf.obj.obj (op V))
        ((SheafOfModules.evaluation L.ringCatSheaf (op V)).obj N) := hsections V hV
    let eV := (SheafOfModules.evaluation L.ringCatSheaf (op V)).mapIso e
    have hfin := Module.Finite.of_surjective eV.hom.hom
      (ConcreteCategory.bijective_of_isIso eV.hom).surjective
    exact hfin
  · intro y hy
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    let : Algebra (L.presheaf.stalk y)
        ((TopCat.Presheaf.stalkFunctor CommRingCat y).obj B.right.obj) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat y).map B.hom.hom).hom.toAlgebra
    obtain ⟨hfinite, hd⟩ := hdepth y hy
    have := hfinite
    obtain ⟨ey⟩ := hstalk y
    have hfiniteB := Module.Finite.equiv ey
    refine ⟨hfiniteB, ?_⟩
    have := hfiniteB
    exact (depth_eq_of_linearEquiv ey) ▸ hd

end AlgebraicGeometry.Scheme
