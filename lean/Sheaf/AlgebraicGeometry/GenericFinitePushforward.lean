/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.GenericFiniteAlgebraSplitting
import Sheaf.AlgebraicGeometry.IrreducibleLisseStrata
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Generic lissity of finite direct images

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1578
(blueprint: lem-weil-pbc-finite-pushforward-generic-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite direct image of a constructible abelian etale sheaf is lisse on a dense
open of an integral Noetherian affine base. Finiteness here means finite geometric
stalks, as in the blueprint, rather than finitely generated abelian stalks.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, order 1578
(blueprint: lem-weil-pbc-finite-pushforward-generic-constructible).

Proof: Write the base as Spec A for a Noetherian domain A. Finite morphisms are closed
by `pqf-lem-finite-integral-lft`. Replace the source by its reduction using
`thm-weil-pbc-universal-homeomorphism-invariance`; it has finitely many irreducible
components by `lem-weil-pbc-noetherian-finite-components`. If none dominates the base,
remove the closed image and the direct image is zero. Otherwise,
`lem-weil-pbc-irreducible-lisse-strata` gives open neighborhoods of the generic points
of dominating components where the sheaf is lisse. Their union contains the generic
fiber; remove the closed image of its complement to make the sheaf lisse everywhere.
By `lem-weil-pbc-generic-finite-algebra-splitting`, shrink again and take a finite
surjective etale cover of the base so that the reduced base change of the source is a
finite disjoint union of finite surjective universal homeomorphisms onto that cover.
Remove nilpotents by `thm-weil-pbc-universal-homeomorphism-invariance`. This equivalence
also identifies direct image along each factor with a finite locally constant sheaf.
The finite product from the disjoint union is lisse. By
`lemma-weil-pbc-finite-exchange`, it is the pullback of the original direct image.
Compose its trivializing etale cover with the etale surjective cover of the shrunken
base to conclude that the original direct image is lisse on that dense open. -/
theorem exists_dense_open_lisse_finite_directImage
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g]
    (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsConstructibleEtaleSheafOfSets
      ((sheafCompose Z.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      IsLisseEtaleSheafOfSets
        ((etaleSetPullback U.ι).obj
          ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E))) := by
  sorry

end AlgebraicGeometry.Scheme
