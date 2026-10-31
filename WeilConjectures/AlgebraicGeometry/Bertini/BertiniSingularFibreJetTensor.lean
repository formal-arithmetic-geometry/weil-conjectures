/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini.BertiniSingularFibreCoordinates
public import WeilConjectures.AlgebraicGeometry.Bertini.BertiniLocalFirstJets
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniFibreJetComparison
import WeilConjectures.AlgebraicGeometry.Reduced.ReducedPullbackSectionVanishing
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The universal first-jet relation on the singular fibre

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`,
using the one-way hypersurface criterion of Algebra Tag 00T7.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  bertiniSingularFibreRingMap bertiniLocalFirstJet bertiniUniversalSection

end AlgebraicGeometry
