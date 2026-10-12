/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantStalk
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit

/-! # Finite local trivializations of finite étale representable sheaves

Source: Stacks Project, Tag 03RV, implication (2) to (1), and Tag 04HN.
(blueprint: lem-weil-pbc-finite-etale-yoneda-local-trivializations)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical sheaf of sections of a finite étale morphism has finite constant
local models, and its geometric stalks are finite.

Source: Stacks Project, Tag 03RV, implication (2) to (1); Tag 04HN gives the splitting.
(blueprint: lem-weil-pbc-finite-etale-yoneda-local-trivializations)

Proof: For each point of T, split P into finitely many copies of an étale neighbourhood
by Tag 04HN. These neighbourhoods form an étale cover. On the site localized at each
member, the sheaf of sections of this disjoint union is the constant sheaf with value
its finite set of sheets: a map into a disjoint union chooses a sheet on each open and
closed piece, so the sections are locally constant sheet-valued functions. This
identification commutes with restriction and gives the displayed sheaf isomorphisms.
At any separably closed geometric point, lift the point to a member of the cover.
Étale localization identifies the stalk with the stalk of the corresponding constant
sheaf; that stalk is its finite value. Thus all geometric stalks are finite, equivalently
finitely generated in the category of sets, which is IsFiniteSheaf. Empty fibres use
the empty set of sheets; the empty scheme uses the empty cover. -/
theorem finiteEtale_yoneda_local_trivializations
    (T P : Scheme.{u}) (π : P ⟶ T) [IsFinite π] [Etale π] :
    (∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty (((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)).over
            (𝒰.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (Type (u + 1))).obj S)) ∧
    IsFiniteSheaf ((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)) := by sorry

end AlgebraicGeometry.Scheme
