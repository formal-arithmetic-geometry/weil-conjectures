/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf

/-! # Exterior sheaves under restriction to the full open

Source: Stacks Project, Tag 0BR0, the expression wedge^r N[-r].
(blueprint: lem-sc-sheaf-exterior-full-open-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Restricting to the full open, taking an exterior sheaf, and pushing back
forward gives the original exterior sheaf.
Source: Stacks Project, Tag 0BR0, identification of the exterior sheaf on the
constant-rank full stratum in the expression wedge^r N[-r].
(blueprint: lem-sc-sheaf-exterior-full-open-iso).

Proof: the inclusion j of the full-open subscheme into X is the scheme
isomorphism X.topIso.hom. On each open of X, restriction identifies the module
sections with those on the corresponding open of the full-open subscheme,
with their structure rings identified by j. The exterior-power universal
property identifies the sectionwise exterior powers: the map sends the wedge
of the transported sections to the transport of their wedge. Its inverse is
the exterior map for the inverse section identification. Both inverse laws
hold on pure wedges, which span. The section identifications commute with
restrictions, so the exterior maps commute with restrictions as well, again
by checking pure wedges. Thus the sectionwise exterior-power presheaves agree
under the equivalence of opens induced by j. This equivalence identifies
covering families, so a sheafification on one side transports to a
sheafification on the other: morphisms from the transported presheaf into
a sheaf factor uniquely by the sheafification adjunction, after transporting
that sheaf back along the inverse equivalence. The two universal properties
give inverse sheafification maps. Applying this to the exterior presheaves
and pushing forward gives the asserted module-sheaf isomorphism.
For d = 0 this uses the zeroth exterior power, without local freeness.
For empty X every sheaf involved is zero, and the same identification holds. -/
theorem exteriorSheaf_fullOpen_pushforward_iso {X : Scheme.{u}} (M : X.Modules)
    (d : ℕ) :
    Nonempty ((pushforward (⊤ : X.Opens).ι).obj
      (exteriorSheaf ((restrictFunctor (⊤ : X.Opens).ι).obj M) d) ≅
        exteriorSheaf M d) := by sorry

end AlgebraicGeometry.Scheme.Modules
