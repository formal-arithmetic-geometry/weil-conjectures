/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleModuleStalkSpecialization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFiniteStalkLocalPresentation
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSectionGermSpecialization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSectionGermNoetherianNeighborhood
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSectionGermIsoSupplement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Finite stalks and specialization imply finite local constancy

Source: Stacks Project, Tag 0GKC, lemma-characterize-locally-constant-module, (2) implies (1)
(blueprint: lem-weil-pbc-etale-finite-stalk-specialization-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
