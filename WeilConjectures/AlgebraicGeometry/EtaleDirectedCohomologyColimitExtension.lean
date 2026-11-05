/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleInjectiveColimitAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor
import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Directed colimits of derived etale cohomology at coefficient size

Source: Stacks Project, Tag 03Q5 (lemma-colimit).
(blueprint: lem-weil-pbc-etale-directed-cohomology-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
