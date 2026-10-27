## What changed

In `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`:

- Proved `AlgebraicGeometry.AlgebraicSpace.moduleTensorPullback_etale_restriction` from
  `space_chart_adjunction_tensor_realization`. Representable etaleness gives chartwise
  etaleness by `isEtale_comp`; compose the chosen chart comparison with the realization's
  multiplication isomorphism, and apply its two normalized section equations.
- Proved `AlgebraicGeometry.AlgebraicSpace.moduleChartBaseChange_triangle` using
  `CostructuredArrow.w`, the square equality on underlying presheaves, and associativity.
- Reduced `AlgebraicGeometry.AlgebraicSpace.etale_module_pushforward_restriction` to the
  independent direct-image and tensor-square comparisons below. The proof derives
  etaleness of `h` from representable base change of the flipped presheaf pullback square,
  obtains the two comparisons, and packages their formulas. The explicit transports
  in the new statements are definitionally the existing `moduleChartBaseChange`;
  their triangle proofs are irrelevant. No declaration signature or definition changed.

Added proof imports of the two new comparison modules, `SpaceChartTensorRealization`,
 and `ChartwiseEtalePermanence`. The new modules have one public theorem each, including
complete sourced proofs in words. Updated the item's node to match the actual reduction.
All three delivery modules compiled separately in import order, in 10.2, 11.3, and 23.0
seconds before the removal of redundant imports; delivery preflight checks the final files.

## Proved and sorry left

The original module contained three holes. Two are proved from existing declarations:

- `AlgebraicGeometry.AlgebraicSpace.moduleTensorPullback_etale_restriction`.
- `AlgebraicGeometry.AlgebraicSpace.moduleChartBaseChange_triangle`.

The third original hole,
`AlgebraicGeometry.AlgebraicSpace.etale_module_pushforward_restriction`, is closed by a
complete Lean reduction to the two new statements. This is a decomposition, not a proof
of the remaining geometric comparisons. The original module now has zero direct holes.

Exactly two holes are added, each the entire proof of its named public theorem:

- `AlgebraicGeometry.AlgebraicSpace.etale_directImage_chart_comparison` in
  `Sheaf.AlgebraicGeometry.SpaceEtaleDirectImageChartComparison`, node
  `lem-trf-etale-direct-image-chart-comparison`.
- `AlgebraicGeometry.AlgebraicSpace.etale_tensor_square_comparison` in
  `Sheaf.AlgebraicGeometry.SpaceEtaleTensorSquareComparison`, node
  `lem-trf-etale-tensor-square-comparison`.

Thus three original direct holes are closed, two by proof and one by decomposition;
two lower holes are added, for a net reduction of one textual hole in this packet.
The proof of the restriction helper still uses the existing chart-realization theorem,
whose own postponed proof is an existing dependency, not a newly added hole.

Edge cases checked against the statements and source: the maps `g` and `h` may be
nonsurjective; no scheme representability, properness or quasi-coherence of `f` is used;
identity squares and zero modules are allowed; empty chart schemes cause no exception.
The tensor-square statement uses only commutativity, and hence also covers commutative
squares which are not pullbacks. Its formula is only on the specified local tensors,
without claiming that every sheaf section is globally a pure tensor.

## No longer needed

Removed the original direct private imports:

- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`: its role belongs to the remaining
  direct-image comparison, whose new module imports it. It is still needed transitively.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: redundant with the
  existing tensor-realization interface, which imports it publicly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: already supplied by the public module-operations
  import.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: already supplied by tensor realization.

No existing module or node is withdrawn. The original geometric dependencies are retained
under the appropriate smaller comparison: enlarged chart limits and ringed localization
under direct images, and normalized tensor realization under tensor composition. In
particular this is no claim that their modules leave the targets' import closure.
The original public imports remain verbatim. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The existing dependencies provide a
normalized tensor realization, so the restriction helper does not require a new tensor
construction. The large final theorem combines two independent comparisons; its tensor
part does not use the pullback property, only the commuting square. The new statements
make that separation explicit while retaining every original normalization equation.
The source-library composition theorem in `SpaceFlatDirectImageBaseChange` cannot be
imported here because that module already imports this item; the chart tensor realization
is the available dependency in the correct direction.

## New nodes

`lem-trf-etale-direct-image-chart-comparison` isolates the original proof's enlarged-site
localization and projection comparison (steps 1, 3, and 4). Its conclusion is only the
normalized direct-image comparison for a specified etale `h`; it contains no tensor
pullback comparison and does not assert etaleness of the pullback map. The module is
`Sheaf.AlgebraicGeometry.SpaceEtaleDirectImageChartComparison`.

`lem-trf-etale-tensor-square-comparison` isolates the tensor-composition portion (steps 2
and 5). It has no direct-image comparison, no conclusion about etaleness, and needs no
cartesian square. Its argument uses normalized tensor composition and the etale
multiplication/unit formulas. The module is
`Sheaf.AlgebraicGeometry.SpaceEtaleTensorSquareComparison`.

Both nodes inherit the item's chapter and unit, cite the original Stacks argument and
nearest blueprint ancestor, record the search results, and specify their remaining
proof dependencies. No change record is needed: existing public signatures, definition
bodies, attributes, and public imports are unchanged; only proofs and private imports
of the assigned module change, together with the new theorem modules and nodes.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
