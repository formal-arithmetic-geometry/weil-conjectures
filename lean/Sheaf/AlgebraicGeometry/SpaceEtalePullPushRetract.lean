/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement
import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-!
# The split étale pull-push counit on algebraic spaces

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 0HAP,
`lemma-etale-pull-push-split` (blueprint: lem-sfb-space-etale-pull-push-retract).
The section below splits the counit of the specified module tensor adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The counit on a quasi-coherent module for a quasi-compact separated étale map
admits a module-linear section. Thus the module is a retract of its pull-push.
Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 0HAP
(blueprint: lem-sfb-space-etale-pull-push-retract).

Proof:
1. Form `W = X ×_Y X` with projections `p` and `q`. The actual restriction comparison
of lem-trf-space-etale-module-pushforward-restriction identifies `f^* f_* F` with
`q_* p^* F`. On a scheme chart `T → X`, both sides are compatible sections on
`X ×_Y T`. Fibre products are supplied by lem-trf-space-fibre-products-etale-covers;
sections on space objects use lem-trf-space-enlarged-etale-ringed-site-model.
2. By lem-sfb-space-separated-etale-diagonal-complement, the diagonal in `W` is open
and closed. Its pullback to `X ×_Y T` is the graph of `T → X`, hence isomorphic to
`T`, with open and closed complement.
3. Extend a section of `F(T)` to this graph by itself and to the complement by zero.
On each scheme chart these glue uniquely along the disjoint two-open cover, by the
sheaf axiom of def-weil-sheaf-of-modules-category. The glued chart sections agree
under every chart restriction by uniqueness.
4. Addition and the scalar action through the second projection preserve these two
restrictions, so the extension is linear. Pullback of the graph and its complement
commutes with maps of `T`, so these extensions define a module morphism `s`.
5. The adjunction triangle for def-trf-space-etale-module-functors, evaluated at the
graph chart, identifies the specified counit with restriction to the graph. Indeed,
the chart-unit formula is `1 ⊗ m`, and the étale normalization of
lem-trf-space-chart-adjunction-tensor-realization sends this to `m`; the restriction
comparison of lem-trf-space-etale-module-pushforward-restriction retains that same
section. Restriction after the extension of step 3 is the identity on every chart.
Consequently `s ≫ counit = 𝟙 F`. Empty charts and the zero module obey the same
formulas. No finiteness or Noetherian assumption is used. -/
theorem exists_section_moduleTensorAdjunction_counit
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hfqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hfsep : IsSeparatedPresheafMap f.hom.hom) (hfet : IsEtale f.hom.hom)
    (F : X.Modules) [SheafOfModules.IsQuasicoherent F] :
    ∃ s : F ⟶ (moduleTensorPullback f).obj ((moduleDirectImage f).obj F),
      s ≫ (moduleTensorAdjunction f).counit.app F = 𝟙 F := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
