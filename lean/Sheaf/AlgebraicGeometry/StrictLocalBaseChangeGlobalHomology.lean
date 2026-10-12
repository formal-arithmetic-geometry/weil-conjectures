/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
import Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # The strict-local base-change mate on global cohomology

Source: Stacks Project, Tags 03Q8, 03Q9 and 0GIT.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The homology of the derived base-change mate is invertible on strict-local sections.
This only asserts invertibility after global sections; it does not assert that the mate
is an isomorphism of sheaves on the strict-local base.
Source: Stacks Project, Tag 03Q9, the affine-neighbourhood continuity argument and the
injective-representative construction of the canonical map
(blueprint: lem-weil-pbc-strict-local-base-change-global-homology).

Proof: choose a bounded-below injective representative J of K. For each affine pointed
étale neighbourhood V of s, restriction of J to X ×_S V preserves injectives, so its
sections complex computes that neighbourhood's hypercohomology. Sheafification of this
cohomology presheaf gives H^n(Rf_*K) (03Q8), and sheafification leaves its geometric stalk
unchanged. Cofinality of affine pointed neighbourhoods identifies this stalk with the
filtered colimit of their hypercohomology. The strict henselization is their inverse limit;
fibre products with X commute with that limit. Each X ×_S V is qcqs because f is qcqs and
V is affine, and transitions are affine by base change of morphisms between affine schemes.
Derived continuity (0GIT) identifies the colimit with hypercohomology of the limit pullback
of K. Strict-local global sections are exact, and coincide with the closed-point stalk
(03QO); hence the source of the displayed map computes the same colimit, while its target
computes limit hypercohomology through Leray. At the level of J, the adjunction mate is
restriction of sections along the pullback square. After taking H^n this is the continuity
map on every neighbourhood. The equality on all germ components, and the colimit universal
property, therefore identify the displayed map with the continuity isomorphism. No torsion
assumption is needed by 0GIT.
-/
theorem isIso_strictHenselization_baseChange_globalHomology
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))) := by
  sorry

end AlgebraicGeometry.Etale
