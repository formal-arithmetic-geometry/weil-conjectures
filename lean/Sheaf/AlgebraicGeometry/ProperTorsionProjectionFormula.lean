/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Torsion
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The proper projection formula with torsion coefficients

Source: Stacks Project, Etale Cohomology, Tag 0F0G,
`lemma-projection-formula-proper-mod-n`; blueprint sec-smooth-purity,
unit sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0f0g).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a proper morphism and a torsion commutative coefficient ring, the canonical
projection-formula map is invertible on arbitrary unbounded complexes.

Source: Stacks Project, Tag 0F0G, `lemma-projection-formula-proper-mod-n`
(blueprint: lem-kun-0f0g).

Proof plan:
1. Base change to a geometric point of Y. The geometric fibre is proper over an
   algebraically closed field, hence finite type and qcqs. Clause (2) of lem-kun-0f10
   gives finite torsion cohomological dimension on this fibre. No global bound on Y
   is asserted (lem-weil-pbc-proper-base-change, def-weil-pbc-scheme-conventions).
2. Identify inverse image to the point with the stalk (lem-kun-stalk-as-pullback).
   The Galois group of an algebraically closed field is trivial, so the equivalence
   of lem-exc-abelian-sheaves-gmodules identifies module sheaves on the point with
   modules, and their unbounded derived categories likewise. The pulled-back K is
   therefore a constant complex on the fibre.
3. Apply lem-kun-proper-base-change-torsion-ring to E and to the tensor with inverse
   image of K. Both exchange maps are invertible without boundedness assumptions.
   Monoidality (lem-kun-inverse-image-monoidal) and the commuting square of
   lem-kun-proj-formula-natural identify the stalk of the canonical projection map
   with the canonical projection map on the fibre, not just its endpoints.
4. The constant-complex formula lem-kun-0f12 on the qcqs fibre of finite dimension
   makes this map invertible. Its adjoint description is exactly
   def-kun-projection-formula-map.
5. Exact geometric stalks (prop-weil-pbc-geometric-stalks-exact) identify homology
   of the stalk map with stalks of its homology maps. Forgetting the coefficient
   action preserves kernels and cokernels. Conservativity
   (lemma-weil-pbc-geometric-stalk-conservative) makes every homology map invertible;
   the cone is acyclic, so the original map is invertible. No bound on E or K is used. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    (Λ : Type (u + 1)) [CommRing Λ] (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K) :=
  sorry

end AlgebraicGeometry.Etale
