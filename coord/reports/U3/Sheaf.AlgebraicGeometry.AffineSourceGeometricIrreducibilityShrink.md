## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.AffineSourceGeometricIrreducibilityShrink` with the
combination of a radicial reduced affine model, a spreading affine source chart,
and the existing geometric fibre density theorem. The Lean proof intersects the
two neighbourhoods, proves irreducibility of each geometric fibre as the closure
of the continuous image of its irreducible dense chart, and descends the open
and the fibre assertion through the base universal homeomorphism.

Added two statement modules, each with one public named theorem and its own node:
`Sheaf.AlgebraicGeometry.GenericRadicialGeometricallyReducedModel` and
`Sheaf.AlgebraicGeometry.GenericGeometricallyIntegralAffineChart`. Existing
signatures, visibility, definitions and target statements are unchanged. The
original node's proof and proof dependencies now describe the Lean reduction.
The unit's realized statement and steps are unchanged; its realized arrays are
empty, so this refinement bypasses no realized unit node.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_open_affine_source_geometric_irreducibility_shrink`
(node `lem-sbc-affine-source-geometric-irreducibility-shrink`). There is no sorry
in the item's final proof.

Added two holes:

- `AlgebraicGeometry.exists_generic_radicial_geometrically_reduced_model`
  (node `lem-sbc-generic-radicial-geometrically-reduced-model`). This constructs
  a flat finitely presented reduced affine model with geometrically reduced
  generic fibre and gives pointwise comparison of geometric fibre spaces; it
  makes no special-fibre irreducibility assertion.
- `AlgebraicGeometry.exists_generic_geometrically_integral_affine_chart`
  (node `lem-sbc-generic-geometrically-integral-affine-chart`). This controls
  only an affine open of a reduced flat finitely presented source over an
  integral affine base, with a geometrically reduced generic fibre. It makes
  no assertion that this open is dense in special fibres, or that the full
  source fibres are irreducible.

This is a decomposition, not an unconditional proof: one upper hole closed,
two lower holes added, net minus one. The unchanged existing dependency
`AlgebraicGeometry.exists_open_geometric_fibre_dense_of_open` still has its own
sorry in its existing module and node; no copy of it was added.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation` from the item's module
and replaced its direct dependency on
`lem-sbc-generic-flat-finite-presentation` by the radicial model. That node and
module are still needed by the radicial model; this is not global pruning.
`Sheaf.AlgebraicGeometry.GenericOpenGeometricFibreDensity` remains needed and
used. No other original dependency node or module is pruned.

Further source-library tools found for the next workers: the sorry-free
`MvPolynomial.bertini_noether` in
`WeilConjectures.RingTheory.BertiniNoether` already proves the polynomial
spreading assertion over an arbitrary domain, for every field-valued ring map.
The chart worker should use it instead of proving the monic coefficient-algebra
argument again. `GenericIrreducibility.exists_locSub_eq` supplies a proved
common-localization argument. The top ring-level theorem
`exists_ne_zero_forall_isIrreducible_fiber` additionally assumes a noetherian
base and concludes ordinary irreducibility of residue-field fibres, so it does
not directly prove this item over an arbitrary base or supply its geometric
field-extension tests. `FieldExtension.exists_finitePurelyInseparable_separablyGenerated`
in `Sheaf.FieldTheory.MakeSeparablyGenerated` is also available for the model
worker, but still needs the radicial integral algebra and geometric fibre glue.
These tools are not imported by the main proof because it does not directly
use their statements.

## Where the brief, the DAG or earlier work was wrong

The original two imported declarations cover generic flatness and geometric
fibre density, but neither states the finite radicial model construction or
the spreading common hypersurface chart. Those non-elementary parts of steps
2 and 3 required separate statements. The original theorem itself is unchanged
and no false statement was found.

Sources read: Stacks Tags 0559 (especially its second proof, reductions,
purely inseparable extension, and common hypersurface open) and 0557 (monic
factor-coefficient argument). Blueprint searches for 0557 and hypersurface
found no matching imported node; the geometric reduction search found related
notions and smooth reduced-fibre results, not these statements. Mathlib
LeanFinder and grep found no exact match; LeanSearch returned Internal Server
Error, recorded as unavailable rather than no match.

Edge cases checked: an empty source is excluded by geometric irreducibility
of its generic fibre; characteristic zero uses the identity purely inseparable
extension; inseparable positive-characteristic generic fibres are handled by
the radicial model and source reduction; relative dimension zero uses a linear
hypersurface and no positive factor-degree pair; nilpotents in the original
base and source are removed by universal homeomorphisms; non-quasi-compact
original affine base inclusion is not used to infer quasi-compactness of f.
The density theorem is applied to g between affine schemes, where g is
quasi-compact independently of that original inclusion.

## New nodes

`lem-sbc-generic-radicial-geometrically-reduced-model`, in
`dag/nodes/sec-smooth-base-change/`, corresponds to
`Sheaf.AlgebraicGeometry.GenericRadicialGeometricallyReducedModel`. It separates
the reductions, generic flatness and finite radicial extension part of Tag
0559. Its only existing proof dependency is generic flat finite presentation.

`lem-sbc-generic-geometrically-integral-affine-chart`, in the same chapter,
corresponds to `Sheaf.AlgebraicGeometry.GenericGeometricallyIntegralAffineChart`.
It separates the common hypersurface open and Tag 0557 argument. Both new
statements have complete natural-language proof docstrings and recorded actual
searches. No change record is needed: no existing interface changed.


## Second reading by U3

1. **Existing interfaces: PASS.** Compared the delivered item with the repository
   by `diff -u` and checked its theorem signature byte for byte, through the
   conclusion before `:= by`. Only its proof imports and proof changed. The
   other two modules are new, not adaptations. No definitions, existing
   signatures, visibility, or target statements changed; no change record is
   required.
2. **Proof and axioms: PASS as a decomposition.** Compiled all three modules in
   import order with `lcompile.py --all`: no errors or warnings. The item has no
   sorry; the two new public named theorems each have exactly `:= by sorry`.
   There are no definitions or forbidden declarations in the delivery.
   A scratch module's `#print axioms` for all three declarations reported only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is
   expected from the two listed open statements and the imported fibre-density
   theorem. Existential witnesses are eliminated locally inside a proposition's
   proof; no public data is defined by choosing an unspecified witness.
3. **Split statements: PASS.** Independently read
   [Stacks 0559](https://stacks.math.columbia.edu/tag/0559), both proofs, and
   [Stacks 0557](https://stacks.math.columbia.edu/tag/0557).
   The radicial model isolates reductions, inseparable extension, and restored
   flat finite presentation; it asserts no special-fibre irreducibility. The
   chart isolates the common hypersurface open and polynomial specialization;
   it asserts nothing about the remaining source fibre. These are proper parts
   of the argument, combined by a real density and descent proof in the item.
   Checked empty source (excluded), identity extension in characteristic zero,
   purely inseparable extensions in positive characteristic, dimension zero,
   nilpotent original bases, and arbitrary nonnoetherian domains. In the chart,
   flatness embeds B in its integral generic fibre; a primitive polynomial and
   a monic base localization justify the hypersurface domain used for the
   common open. The common principal open is affine and finitely presented over
   the base; its flat map has open image, giving nonempty fibres after shrinking.
   For the model, choose a principal original-base open inside the image of the
   final radicial-base shrinking: its pullback stays affine and preserves all
   required properties. Both holes have complete source/proof docstrings and
   matching nodes. Independent LeanFinder queries used "integral flat affine"
   and "reduction of a finite type integral algebra"; Loogle queried
   `AlgebraicGeometry.GeometricallyReduced`. No exact theorem was found.
   Searched `lean/Sheaf`, the source `GenericIrreducibility` and `BertiniNoether`,
   and DAG declaration names. Bertini--Noether proves only the polynomial part;
   the ring-level whole-family theorem requires a noetherian base. Neither
   closes either new hole in a few minutes. The field extension theorem supplies
   only the field part of the model, not the affine model and fibre comparison.
4. **Route and pruning: PASS.** Read the original two proof dependencies and
   `dag/units/sk-prop-normal-form.json`. The unit's statement and two step
   `realized` arrays are empty and are unchanged; no realized unit is bypassed.
   The item uses exactly the model, chart, and existing fibre-density imports;
   all are proof-only imports. Its original generic-flat-finite-presentation
   dependency is the only direct dependency removed, and remains needed below
   the model. The report correctly distinguishes direct removal from global
   pruning and records the net hole change as minus one.
5. **DAG agreement: PASS.** Checked each recorded Lean statement against its
   module and each `proof_deps` against the union of proof-step `uses`. The
   item's steps match the model call, chart call, density/irreducible-closure
   argument, and open-image descent. New nodes contain source, creation,
   blueprint, searches, chapter/unit, and Lean records. Existing-node changes
   are confined to proof-owned fields.

Second reading changes: clarified the chart's natural-language proof and node
about primitive polynomial choice and the hypersurface domain after monic
localization; corrected the report's field theorem namespace from `Algebra`
to `FieldExtension`. No Lean proof or signature needed repair. Removed the
scratch axiom probe after checking it. The delivery still closes one of one
original holes and adds two lower holes; it is a decomposition.
