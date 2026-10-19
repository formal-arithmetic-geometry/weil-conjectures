## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedExtensionZeroBaseChangeVerticalPasting` states
`AlgebraicGeometry.Etale.derivedExtensionZeroBaseChangeVerticalPasting`.  It uses the
finite coefficient ring `Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ]`, two
`OpenImmersionSquare` records, and a module sheaf
`F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.

The first square is rendered by `sq₁data : OpenImmersionSquare gU j' j g`; its
`isOpenImmersion` and `isOpenImmersion'` fields provide the open-immersion hypotheses
for `j` and `j'`.  The second is rendered by
`sq₂data : OpenImmersionSquare hU j'' j' h`; its `isOpenImmersion'` field provides the
open-immersion hypothesis for `j''` (the second square's other open-immersion field is
part of the square record).  The two chosen pullback records are converted to
`IsPullback` values `sq₁` and `sq₂` by `IsPullback.of_iso_pullback`, using the chosen
pullback isomorphisms and both projection equations.  Thus no cartesianness or
open-immersion hypothesis is added or omitted.

For the first base-change map, the expression
`(@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
(ModuleCat.{u + 1} Λ) sq₁)).inv.app F` is the inverse of the canonical map
`j'_! g_U^* F ⟶ g^* j_! F`, hence renders the node's `b_{g,F}` in the direction
`g^* j_! F ⟶ j'_! g_U^* F`.  Applying `h^*` with `Functor.map` renders the first
arrow in the displayed composite.  The next expression is the analogous inverse for
`sq₂`, applied to `(gU)^* F`, and renders
`h^*j'_!(gU)^*F ⟶ j''_!h_U^*(gU)^*F`.

The composite square is the horizontal pasting `sq₂.paste_horiz sq₁`; this gives the
cartesian square with top arrow `hU ≫ gU`, bottom arrow `h ≫ g`, and open arrows
`j''` and `j`.  Its inverse base-change map renders `b_{g∘h,F}`.  The inverse of
`upperStarComp (ModuleCat.{u + 1} Λ) h g (h ≫ g)` identifies the source
`h^*g^*j_!F` with `(h ≫ g)^*j_!F`, and the hom of
`upperStarComp (ModuleCat.{u + 1} Λ) hU gU (hU ≫ gU)` identifies the target
`(hU ≫ gU)^*F` with `hU^*gU^*F`; mapping the latter through `j''_!` gives exactly
the target comparison in the node.  The equality therefore has the same source,
target, clauses, and canonical module-linear inverse-image identifications as the
natural-language statement.

The declarations read and used were:

* `AlgebraicGeometry.OpenImmersionSquare` from
  `Sheaf.AlgebraicGeometry.OpenImmersionSquare` (the dependency
  `def-cbc-open-immersion-square`);
* `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap` and
  `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap` from
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
  (the dependency `lem-cbc-extension-zero-base-change`);
* `AlgebraicGeometry.Etale.upperStarComp` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (the composition
  comparison underlying `lem-weil-pbc-inverse-image-composition-module-linear`);
* `AlgebraicGeometry.etaleInverseImageCompositionModuleLinear` from
  `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`, which supplies
  the module-linearity and canonical-unit characterization of those comparisons; and
* `AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction` from
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, the recorded
  extension-by-zero adjunction dependency.

The source declarations were checked in full, including their universe parameters and
module-sheaf coefficient categories.  No existing declaration states this exact
underived vertical-pasting equality.  No new definition node or dependency module was
needed.

Edge cases checked before writing the statement were identity maps `g` or `h` (the
formula reduces to the corresponding composition/unit comparison), empty open schemes,
`F = 0`, and the zero finite commutative ring.  The chosen-pullback data is retained in
both input square records; the composite uses the canonical pasted `IsPullback`.

Searches made:

* `msearch.py ... leanfinder "successive cartesian base changes composition law for
  extension by zero underived etale module sheaves"`: eight algebra/base-change hits,
  no etale sheaf extension-by-zero pasting declaration;
* `msearch.py ... loogle "openImmersionLowerShriekBaseChangeMap_comp, upperStarComp,
  lowerShriekComp"`: zero hits, with the queried identifier unknown;
* `msearch.py ... grep "vertical.?pasting|openImmersionLowerShriekBaseChangeMap.*comp|extension.*zero.*base.?change" Mathlib`:
  no Mathlib hits;
* `rg` over the source and project Lean trees for the node id and the same base-change
  and pasting patterns: only the general derived-pasting files and the primitive
  base-change-map declarations were found, not this statement.

## Second reading by Q25

I reread the node and the declaration after compilation.  The coefficient-ring,
finite-module-sheaf, two-square, and open-immersion hypotheses are all present.  The
left side is exactly the two inverse canonical base-change maps with `h^*` applied to
the first; the right side is exactly the composite-square inverse map transported by
the two canonical `upperStarComp` comparisons.  The source and target match after
those comparisons, and the statement ends with `:= by sorry`.  No definition contains
`sorry`; the only postponed proof is this named theorem.
