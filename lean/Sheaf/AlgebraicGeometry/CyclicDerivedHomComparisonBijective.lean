/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.CyclicDerivedHomComparisonMap

/-! # Bijectivity of free-representable cohomology comparison
Source: Stacks Project, Tags 03Q8 and 072W, and the free-sheaf adjunction.
(blueprint: lem-sbc-abelian-representable-cohomology-map-bijective). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The explicit universal-section map computes the cohomology of the fibre product.

Source: Stacks Project, Tags 03Q8 and 072W; the free-sheaf/étale-extension-by-zero
argument of `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/FreeSheaf.lean`.
(blueprint: lem-sbc-abelian-representable-cohomology-map-bijective).

Proof: Put T = Y ×_X W and r = T → Y. The free/sheafification/Yoneda adjunction
identifies maps from h*Z[W] with sections over T, naturally in the target sheaf.
The exact left adjoint r_! to r* takes the constant integer sheaf to h*Z[W], by
this same universal property. Its adjunction unit at the constant integer sheaf
is precisely abelianRepresentableGenerator: evaluate the h*-adjunction unit at
id_W, change the pullback order, and restrict to id_T. Since r_! and r* are
exact, their derived adjunction identifies Ext(h*Z[W], F, q) with
Ext(Z_T, r*F, q). The forward map is pullback of the Ext class followed by
precomposition with this generator, hence is abelianRepresentableCohomologyMap.
The fully faithful inclusion of D+ into D identifies its input with Ext through
abelianPlusHomExtEquiv. All constituent maps are bijective, proving the result
for every F and q, including q = 0 and empty T. -/
theorem abelianRepresentableCohomologyMap_bijective {X Y : Scheme.{u}}
    (h : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (W : X.Etale) :
    Function.Bijective (abelianRepresentableCohomologyMap h F q W) := by sorry

end AlgebraicGeometry.Etale
