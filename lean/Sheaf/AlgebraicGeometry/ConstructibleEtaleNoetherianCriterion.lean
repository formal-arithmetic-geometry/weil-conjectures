/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Constructibility from generic lissity on integral affine subschemes

Source: finite pushforward constructibility blueprint, steps 2 and 3;
Stacks Project, Tags 095E and 005L.
(blueprint: lem-weil-pbc-constructible-etale-noetherian-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- On a Noetherian scheme, generic lissity on every integral affine locally closed
subscheme gives a finite constructible lisse stratification. The hypothesis concerns
restrictions of an arbitrary set sheaf and makes no claim about finite direct images.

Source: blueprint `lem-weil-pbc-finite-pushforward-constructible-noetherian`, steps 2--3;
Stacks Project, Tags 095E and 005L.
(blueprint: lem-weil-pbc-constructible-etale-noetherian-criterion).

Proof: Use Noetherian induction on closed subsets T of X, endowed with their reduced
induced scheme structure, to partition the restriction of F into finitely many lisse
locally closed subschemes. For the empty subset choose the empty partition. If T is
reducible, its finitely many irreducible components are proper closed subsets. Apply
induction to each component. Subtract the union of earlier components from each of its
strata. These differences remain locally closed and lisse, are pairwise disjoint, and
cover T. If T is irreducible and nonempty, its reduced scheme is integral. Choose a
nonempty affine open S in it. Its composite immersion into X satisfies the hypothesis;
the supplied dense open W of S is also a dense open of T. Its sheaf is lisse by the
hypothesis and the composition isomorphism for inverse images. Its complement is a
proper closed subset of T, so adjoin W to the partition supplied by induction there.
The induction terminates because the topology of X is Noetherian, without a dimension
bound. At T = X with its reduced structure, compose all stratum immersions into X;
their images partition X. Each image is constructible by Noetherianity (Tag 005L).
Composition of inverse images identifies the restrictions with the lisse sheaves just
constructed, giving the required Stratification witness (Tag 095E). Restriction of a
lisse sheaf to an open stays lisse: restrict a trivializing etale cover and use the
unchanged geometric stalks. This justifies the differences in the reducible case. -/
theorem isConstructibleEtaleSheafOfSets_of_generic_lisse
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : ∀ (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
      (g : S ⟶ X) [IsImmersion g],
      ∃ W : S.Opens, Dense (W : Set S) ∧
        IsLisseEtaleSheafOfSets
          ((etaleSetPullback W.ι).obj ((etaleSetPullback g).obj F))) :
    IsConstructibleEtaleSheafOfSets F := by sorry

end AlgebraicGeometry.Scheme
