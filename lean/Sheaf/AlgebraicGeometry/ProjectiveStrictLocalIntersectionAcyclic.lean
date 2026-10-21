/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.ProjectiveFiniteAffineNeighbourhood
import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import Sheaf.AlgebraicGeometry.ArtinTensorEtaleAcyclic
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# Acyclicity of intersections of projective strict localizations

Source: Hübner–Schmidt, The tame site of a scheme, Definition 7.8, Proposition 7.9,
Theorem 7.10 and Proposition 7.14(i), printed pp. 14–16
(blueprint: lem-trf-projective-strict-local-intersection-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Over an affine base, the intersection of two strict localizations of a projective scheme
has vanishing positive derived étale cohomology for every torsion abelian sheaf.
Source: Hübner–Schmidt, The tame site of a scheme, Theorem 7.10 and Proposition 7.14(i)
(blueprint: lem-trf-projective-strict-local-intersection-acyclic).

Proof:
1. The projective embedding over the affine base is affine. Apply
   `lem-pd-projective-finite-affine-neighbourhood` to the two images to obtain a common
   affine open `V = Spec R`.
2. All generizations of both images lie in `V`, so both strict-localization maps factor
   through `V`. By `lem-trf-ind-etale-strict-local-invariance`, their strict localizations
   agree with those computed in `V`. By
   `lem-weil-pbc-strict-henselization-affine-chart-ind-etale` their coordinate rings are
   ind-étale over `R`; clause (1) of
   `lem-weil-pbc-strict-henselization-functoriality` makes them strictly henselian local.
   Each spectrum is connected and strictly henselian, hence étale acyclic by
   Hübner–Schmidt Proposition 7.9.
3. Since `V` is open in `P`, the fibre product over `P` equals the fibre product over `V`,
   hence is the spectrum of the tensor product of these two rings over `R`.
   Apply `lem-trf-artin-tensor-etale-acyclic` (Hübner–Schmidt Theorem 7.10) to this tensor
   product and transport cohomology across the isomorphism. This includes the zero ring
   and an arbitrary number of connected components. -/
theorem isZero_cohomology_projective_strictLocal_intersection
    {B P : Scheme.{u}} [IsAffine B] (p : P ⟶ B) [IsProjective p]
    {Ωx Ωu : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωu] [IsAlgClosed Ωu]
    (x : Spec (.of Ωx) ⟶ P) (y : Spec (.of Ωu) ⟶ P)
    (A : Sheaf (pullback (strictHenselizationStructuralMap x)
      (strictHenselizationStructuralMap y)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : IsTorsionAbelianSheaf A) (i : ℕ) (hi : 0 < i) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1}
      (pullback (strictHenselizationStructuralMap x) (strictHenselizationStructuralMap y))
      (i : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj A)) := by
  sorry

end AlgebraicGeometry.Scheme
