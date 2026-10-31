/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.DeligneLaumon.SmoothLocalBranchInvariance

/-!
# Etale local maps preserve geometric unibranchness

Source: Stacks Project, More on Algebra, Tag 0DQ1 (part (1)), specialized to the
localization of the etale map in Tag 0GSC, together with Tag 0C37 (part (3))
(blueprint: lem-dl-a1-smooth-geounibranch-local).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

universe u v

open scoped TensorProduct

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An etale affine map preserves geometric unibranchness of local rings.

Source: Stacks Project, More on Algebra, Tag 0DQ1 (part (1)), specialized to the
localization of the etale map in Tag 0GSC, together with Tag 0C37 (part (3))
(blueprint: lem-dl-a1-smooth-geounibranch-local).

Proof:
1. Since `Spec C → Spec R` is etale, `C` is a finitely presented `R`-algebra with
   vanishing `H_1` of the cotangent complex and `Ω_{C/R} = 0`, so `R → C` is smooth
   (blueprint: lem-weil-pbc-etale-ring-map-iff-etale-affine). By base change
   `R_p → P := R_p ⊗_R C = S⁻¹C` is smooth, `S` the image of `R \ p`
   (blueprint: lem-weil-pbc-smooth-ring-map-base-change-composition). Since
   `q ∩ R = p`, `Q := S⁻¹q` is a prime of `P` and `C_q ≅ P_Q` as `R_p`-algebras; the
   map `R_p → C_q` is local, so `C_q` is essentially smooth over `R_p`
   (blueprint: def-weil-pbc-essentially-smooth-ring-map).
2. Apply the smooth branch invariance of Stacks Tag 0DQ1 (1) with Tag 0C37 (3)
   (blueprint: lem-dl-a1-smooth-local-branch-invariance) to `R_p → C_q`: irreducibility
   of the spectrum of a strict henselization of `R_p` is the geometric-unibranch
   hypothesis, and the conclusion is irreducibility for `C_q`.
-/
theorem smooth_geounibranch_local
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    (hEtale : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap R C))))
    (q : Ideal C) [q.IsPrime]
    (p : Ideal R) [p.IsPrime]
    (hp : q.comap (algebraMap R C) = p)
    (hgeom : ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [Algebra (Localization.AtPrime p) K]
      [IsScalarTower (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [CommRing H] [Algebra (Localization.AtPrime p) H],
      Algebra.StrictHenselizationPresentationIn.{u, v}
          (Localization.AtPrime p) K H →
        IrreducibleSpace (PrimeSpectrum H)) :
    ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
      [Algebra (Localization.AtPrime q) K]
      [IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
      [CommRing H] [Algebra (Localization.AtPrime q) H],
      Algebra.StrictHenselizationPresentationIn.{u, v}
          (Localization.AtPrime q) K H →
        IrreducibleSpace (PrimeSpectrum H) := by
  letI hLies : q.LiesOver p := by
    rw [Ideal.liesOver_iff]
    exact hp.symm
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have hloc : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom p q (algebraMap R C) hp.symm
  have hEtaleRing : RingHom.Etale (algebraMap R C) :=
    HasRingHomProperty.Spec_iff.mp hEtale
  have hA : Algebra.Etale R C :=
    (RingHom.etale_algebraMap (R := R) (S := C)).mp hEtaleRing
  letI : Algebra.Etale R C := hA
  have hEss : Algebra.EssentiallySmooth
      (Localization.AtPrime p) (Localization.AtPrime q) := by
    let M : Submonoid R := p.primeCompl
    let P : Type u := Localization (Algebra.algebraMapSubmonoid C M)
    let e := Localization.tensorRightAlgEquiv M C
    letI : Algebra (Localization.AtPrime p) P := inferInstance
    have hTensorSmooth : Algebra.Smooth (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[R] C) := inferInstance
    letI : Algebra.Smooth (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[R] C) := hTensorSmooth
    letI : Algebra.Smooth (Localization.AtPrime p) P :=
      Algebra.Smooth.of_equiv e
    have hle : Algebra.algebraMapSubmonoid C M ≤ q.primeCompl := by
      rintro _ ⟨r, hr, rfl⟩ hq
      apply hr
      rw [← hp]
      exact hq
    letI : Algebra P (Localization.AtPrime q) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (S := P)
        (T := Localization.AtPrime q) (Algebra.algebraMapSubmonoid C M)
        q.primeCompl hle
    letI : IsScalarTower C P (Localization.AtPrime q) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (S := P)
        (T := Localization.AtPrime q) (Algebra.algebraMapSubmonoid C M)
        q.primeCompl hle
    letI : IsScalarTower R C P := inferInstance
    letI : IsScalarTower R (Localization.AtPrime p) P := inferInstance
    letI : IsLocalization
        (q.primeCompl.map (algebraMap C P)) (Localization.AtPrime q) :=
      IsLocalization.isLocalization_of_submonoid_le (S := P)
        (T := Localization.AtPrime q) (Algebra.algebraMapSubmonoid C M)
        q.primeCompl hle
    letI : IsScalarTower (Localization.AtPrime p) P (Localization.AtPrime q) :=
      IsScalarTower.of_algebraMap_eq' (by
        apply IsLocalization.ringHom_ext M
        ext r
        simp only [RingHom.comp_apply]
        rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq,
          Localization.localRingHom_to_map]
        calc
          algebraMap C (Localization.AtPrime q) (algebraMap R C r) =
              algebraMap P (Localization.AtPrime q)
                (algebraMap C P (algebraMap R C r)) :=
            IsScalarTower.algebraMap_apply C P (Localization.AtPrime q)
              (algebraMap R C r)
          _ = algebraMap P (Localization.AtPrime q)
              (algebraMap (Localization.AtPrime p) P
                (algebraMap R (Localization.AtPrime p) r)) := by
            congr 1
            exact (IsScalarTower.algebraMap_apply R C P r).symm.trans
              (IsScalarTower.algebraMap_apply R (Localization.AtPrime p) P r))
    refine ⟨P, inferInstance, ?_⟩
    refine ⟨inferInstance, inferInstance, ?_⟩
    refine ⟨q.primeCompl.map (algebraMap C P), ?_⟩
    exact ⟨(IsLocalization.algEquiv
      (q.primeCompl.map (algebraMap C P)) (Localization.AtPrime q)
      (Localization (q.primeCompl.map (algebraMap C P)))).restrictScalars
        (Localization.AtPrime p)⟩
  exact smooth_local_branch_invariance
    (Localization.AtPrime p) (Localization.AtPrime q) hEss hgeom

end AlgebraicGeometry
