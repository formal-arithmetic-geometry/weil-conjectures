/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-! # Quasi-compact cancellation for algebraic-space morphisms

Source: Stacks Project, Morphisms of Spaces, Tags 03KS and 03KG(1), (3)
(blueprint: lem-sfb-space-qc-cancellation).

Quasi-compactness uses the existing affine-test predicate `MapIsQuasiCompact`, with
compactness of the point space in its atlas topology. Quasi-separatedness is the same
predicate on the relative diagonal. The ambient spaces need not be quasi-compact.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a composite is quasi-compact and its second arrow is quasi-separated, its first
arrow is quasi-compact. Source: Stacks Project, Morphisms of Spaces, Tag 03KS,
using the affine-test characterization of Tag 03KG(1), (3)
(blueprint: lem-sfb-space-qc-cancellation).

Proof: (1) By [lem-a1-space-etale-open-image], compactness of the point space is
 equivalent to existence of a surjective etale atlas from a quasi-compact scheme.
 Thus [lem-sfb-space-quasicompact-affine-tests] applies to the stated convention and
 supplies arbitrary base-change stability and tests by all quasi-compact schemes.
 (2) Fix an affine scheme `T` and a map `t : T → Y`. Put `P = X ×_Z T` and
 `Q = X ×_Y T`. These are algebraic spaces by [lem-trf-space-fibre-products-etale-covers].
 The natural map `Q → P` is the pullback of the relative diagonal of `g` along
 `P → Y ×_Z Y`, sending `(x,t)` to `(f(x),t)`. On scheme tests, deleting the redundant
 equal `Y` coordinate and reinserting `f(x)` are mutually inverse natural maps.
 (3) The composite hypothesis makes `P` quasi-compact. The diagonal hypothesis and
 base-change stability from [lem-sfb-space-quasicompact-affine-tests] make `Q → P`
 quasi-compact, so its pullback over every quasi-compact scheme is quasi-compact.
 (4) Choose a surjective etale quasi-compact scheme atlas `U → P` by
 [lem-a1-space-etale-open-image]. Then `R = Q ×_P U` is quasi-compact. Choose such
 an atlas `V → R` as well. The projection `R → Q` is representable surjective etale by
 [lem-trf-space-fibre-products-etale-covers]. Thus `V → Q` is representable surjective
 etale: on scheme tests this follows from [def-trf-algebraic-space] and the singleton
 case of [lem-weil-pbc-etale-covering-composition]. The atlas `V → Q` makes the point
 space of `Q` compact by [lem-a1-space-etale-open-image].
 (5) This holds for every affine test `T → Y`, which is exactly the conclusion.
 Empty pullbacks use the empty scheme atlas. No global compactness assumption is used. -/
theorem quasiCompact_of_comp_of_quasiSeparated
    {S : Scheme.{u}} (X Y Z : AlgebraicSpace S) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hcomp : MapIsQuasiCompact (f.hom.hom ≫ g.hom.hom))
    (hg : MapIsQuasiCompact (pullback.diagonal g.hom.hom)) :
    MapIsQuasiCompact f.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
