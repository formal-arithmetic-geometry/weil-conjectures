/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Quasi-finite at a point implies isolated in the fibre

## References

* [Stacks Project, Tag 01TH](https://stacks.math.columbia.edu/tag/01TH)
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism locally of finite type and quasi-finite at a point has an isolated
point in its scheme-theoretic fibre, stated both for `f.asFiber x` in `f.fiber (f x)` and
for `x` in the subspace `f ⁻¹' {f x}`. -/
theorem quasiFiniteAtPoint_isolated_in_fiber
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType f] (x : X)
    (hfx : IsQuasiFiniteAtPoint f x) :
    IsOpen ({f.asFiber x} : Set (f.fiber (f x))) ∧
      IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) := by
  obtain ⟨U, hx, hU, V, hV, e, hft, hq⟩ := hfx
  let := (f.appLE V U e).hom.toAlgebra
  let := hft
  let q := hU.primeIdealOf ⟨x, hx⟩
  let p := q.comap (algebraMap Γ(S, V) Γ(X, U))
  let H := PrimeSpectrum.preimageHomeomorphFiber Γ(S, V) Γ(X, U) p
  have ho : IsOpen ({⟨q, rfl⟩} : Set
      (PrimeSpectrum.comap (algebraMap Γ(S, V) Γ(X, U)) ⁻¹' {p})) := by
    rw [← H.isOpen_image, Set.image_singleton]
    exact hq
  have hqa : Algebra.QuasiFiniteAt Γ(S, V) q.asIdeal :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q ho
  -- Identify the affine stalk map with the map between the localizations.
  have hqm : f.QuasiFiniteAt x := by
    rw [QuasiFiniteAt,
      RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f V hV U hU e hx)]
    apply RingHom.QuasiFinite.of_comp
      (g := algebraMap Γ(S, V)
        (Localization.AtPrime (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal))
    have heq : (Localization.localRingHom _ _ (f.appLE V U e).hom
        congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hx).1).symm).comp
        (algebraMap Γ(S, V)
          (Localization.AtPrime (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal)) =
        algebraMap Γ(S, V) (Localization.AtPrime q.asIdeal) := by
      ext a
      simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
      rfl
    exact heq.symm ▸ RingHom.quasiFinite_algebraMap.mpr hqa
  have hfiber : IsOpen ({f.asFiber x} : Set (f.fiber (f x))) :=
    quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqm
  refine ⟨hfiber, ?_⟩
  simpa only [Set.image_singleton, asFiber, Homeomorph.apply_symm_apply] using
    (f.fiberHomeo (f x)).isOpenMap _ hfiber

end AlgebraicGeometry.Scheme.Hom
