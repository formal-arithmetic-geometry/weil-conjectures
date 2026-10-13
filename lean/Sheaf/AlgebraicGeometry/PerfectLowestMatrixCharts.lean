/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen
import Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback

/-! # Local matrix charts for lowest cohomology

Source: Stacks Project, Tag 0BDL, local matrix calculation.
(blueprint: lem-sc-perfect-lowest-matrix-charts).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Lowest cohomology of fixed rank is represented locally on the rank-bound open
by finitely presented closed matrix loci.
Source: Stacks Project, Tag 0BDL, matrix-chart part of the proof.
(blueprint: lem-sc-perfect-lowest-matrix-charts).

Proof: At x choose a finite-free residue model (0BCD) on an affine neighbourhood,
shrunk into U. Tor amplitude kills terms below a. The degree-a term has rank
s = beta_a(x) <= r. Cut out all entries of the outgoing differential if s = r,
and use the empty closed subscheme if s < r. Termwise pullback computes derived
pullback and its lowest cohomology is the kernel. A zero differential has free
kernel of rank r. Conversely trivialize a free rank-r kernel on the source.
When s = r its injection into the first term is square, and 0EWY says the dual
of its cokernel is zero. Every coordinate of the outgoing differential factors
through that cokernel, so the differential is zero. When s < r, pad the target
of the injection with r-s zero coordinates. The resulting square injective map
has injective transpose by 0EWY, contradicted by a nonzero padded coordinate
on any nonempty source chart. Thus a source with rank-r kernel is empty in
this case. These arguments also cover r = 0 and the empty source. The finitely
many matrix entries generate a finite type ideal, so its closed immersion is
locally of finite presentation. No gluing of different base charts is claimed. -/
theorem exists_perfectLowestMatrixCharts
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ)
    (U : S.Opens) (hU : ∀ x : S, x ∈ U → derivedFiberBetti S E a x ≤ r) :
    ∀ x : U.toScheme, ∃ V : U.toScheme.Opens, x ∈ V ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ V.toScheme),
        IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
        (∀ (T : Scheme.{u}) (h : T ⟶ V.toScheme),
          (∃ g : T ⟶ Z, g ≫ i = h) ↔
            SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
                  ((derivedPullback ((h ≫ V.ι) ≫ U.ι)).obj E)) r) := by
  intro x
  obtain ⟨_, _, O, hxO, hO, P, hbounded, hrank, ⟨eP⟩⟩ :=
    exists_finiteFreeResidueModel S E hE (U.ι x)
  obtain ⟨V, hxV, hV, K, hb, hl, hf, ⟨eK⟩⟩ :=
    lowestResidueModel_withinOpen S E a b hamp U x O hxO hO P hbounded hrank eP
  have : IsAffine V.toScheme := hV
  have hsr : derivedFiberBetti S E a (U.ι x) ≤ r := hU (U.ι x) x.property
  obtain ⟨Z, i, hi, hfp, hZ⟩ := exists_affineFreeLowestMatrixLocus V.toScheme K a
    (derivedFiberBetti S E a (U.ι x)) r hsr hb hl
    (fun j ↦ ⟨derivedFiberBetti S E j (U.ι x), hf j⟩) (hf a)
  refine ⟨V, hxV, Z, i, hi, hfp, fun T h ↦ ?_⟩
  obtain ⟨_, _, _, c, _⟩ := exists_derivedPullbackComposition.{u, w}
  let e : (derivedPullback h).obj (DerivedCategory.Q.obj K) ≅
      (derivedPullback ((h ≫ V.ι) ≫ U.ι)).obj E :=
    (derivedPullback h).mapIso eK.symm ≪≫ (c h (V.ι ≫ U.ι)).app E ≪≫
      eqToIso (congrArg (fun f ↦ (derivedPullback f).obj E)
        (Category.assoc h V.ι U.ι).symm)
  let eH := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).mapIso e
  constructor
  · intro hh
    have := (hZ T h).mp hh
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eH
  · intro hh
    have := hh
    exact (hZ T h).mpr (SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eH.symm)

end AlgebraicGeometry.Scheme
