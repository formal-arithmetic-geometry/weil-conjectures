/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.FibreRingNoetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Geometric regularity of a fibre from maximal target localizations

For a fixed prime `p` of `R`, geometric regularity of the fibre of `R → S` over `p` can be
checked after localizing `S` at each maximal ideal. Flatness is not required.

## Implementation details

For a finite purely inseparable extension `K` of `κ(p)`, every localization of the extended
fibre `F_K` at a prime is a localization of the extended fibre of some `S_m`, hence regular.

## References

* [Stacks, Tag 07C0]
-/

@[expose] public section

universe u v

namespace Algebra

private theorem regular_tensor_of_maximal
    {R : Type u} {S : Type v} {K : Type (max u v)}
    [CommRing R] [CommRing S] [CommRing K] [Algebra R S] [Algebra R K]
    [IsNoetherianRing (TensorProduct R K S)]
    (h : ∀ (m : Ideal S) [m.IsMaximal],
      IsRegularRing (TensorProduct R K (Localization.AtPrime m))) :
    IsRegularRing (TensorProduct R K S) := by
  apply isRegularRing_iff.mpr
  intro n hn
  let f := (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R K S)
  let q := n.comap f.toRingHom
  have : q.IsPrime := Ideal.comap_isPrime _ n
  obtain ⟨m, hm, hqm⟩ := q.exists_le_maximal (show q.IsPrime from inferInstance).ne_top
  let _ := hm
  let M := m.primeCompl.map f
  have hd : Disjoint (M : Set (TensorProduct R K S)) (n : Set _) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ hx
    exact hs (hqm hx)
  let C := Localization M
  have hp : (n.map (algebraMap (TensorProduct R K S) C)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M C n hn hd
  let _ := hp
  have he : (n.map (algebraMap (TensorProduct R K S) C)).under
      (TensorProduct R K S) = n :=
    IsLocalization.under_map_of_isPrime_disjoint M C hn hd
  have : IsRegularRing C := by
    have := h m
    exact IsRegularRing.of_ringEquiv
      (IsLocalization.tensorProductEquivOfMapIncludeRight R K m.primeCompl
        (Localization.AtPrime m) C).toRingEquiv
  have e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
    (n.map (algebraMap (TensorProduct R K S) C))
  have : IsRegularLocalRing
      (Localization.AtPrime ((n.map (algebraMap (TensorProduct R K S) C)).under
        (TensorProduct R K S))) :=
    IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv
    (Localization.localRingEquiv
      ((n.map (algebraMap (TensorProduct R K S) C)).under (TensorProduct R K S))
      n (RingEquiv.refl _) (by
        change _ = n.comap (RingHom.id _)
        rw [Ideal.comap_id]
        exact he))

/-- For a fixed source prime, geometric regularity of the fibre can be checked after
localizing the target at each maximal ideal. Flatness is not required. -/
theorem isGeometricallyRegular_fiber_of_localizations_maximal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (p : Ideal R) [p.IsPrime]
    (h : ∀ (m : Ideal S) [m.IsMaximal],
      IsGeometricallyRegular p.ResidueField (p.Fiber (Localization.AtPrime m))) :
    IsGeometricallyRegular p.ResidueField (p.Fiber S) := by
  have := p.isNoetherianRing_fiber (B := S)
  refine ⟨inferInstance, ?_⟩
  intro K _ _ _ _
  let : Algebra R K := Algebra.compHom K (algebraMap R p.ResidueField)
  let : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  let F := p.Fiber S
  let : Algebra F (TensorProduct p.ResidueField K F) :=
    Algebra.TensorProduct.rightAlgebra
  have : Module.Finite F (TensorProduct p.ResidueField K F) := by
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight p.ResidueField F K).toLinearEquiv
  have : IsNoetherianRing (TensorProduct p.ResidueField K F) :=
    IsNoetherianRing.of_finite F _
  let e := Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K S
  have : IsNoetherianRing (TensorProduct R K S) :=
    isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  have : IsRegularRing (TensorProduct R K S) := by
    apply regular_tensor_of_maximal
    intro m hm
    have := (h m).2 K
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K
        (Localization.AtPrime m)).toRingEquiv
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

end Algebra
