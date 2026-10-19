## Worker report

The delivery states `AlgebraicGeometry.etale_of_comp_of_surjective_etale` in
`Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`. Its only proof is `sorry`,
as required for stage 2. The module docstring cites Stacks Descent Tag 036W, and the
theorem docstring carries all four steps of the node's proof with their dependency ids.
The node copy changes only `lean`; no statement correction or new notion is needed.

Clause-by-clause translation:

- “Let T, X, Y be schemes”: `{T X Y : Scheme.{u}}`, with `universe u` explicitly declared.
  This is the usual common ambient universe for a diagram of schemes and imposes no
  geometric size, separation, or finiteness condition.
- “h : X → T and p : Y → X”: `(h : X ⟶ T) (p : Y ⟶ X)`.
- “p is surjective”: `[Surjective p]`, precisely surjectivity on underlying points.
- “p is étale”: `[Etale p]`, using Mathlib's existing affine-local étale predicate.
- “h composed with p is étale”: `[Etale (p ≫ h)]`; Lean's composition order is first p,
  then h, exactly the node's h ∘ p.
- “then h is étale”: the conclusion `Etale h`.
- “No separation, finite-type or Noetherian hypothesis”: none of these appears in the
  binders; neither does quasi-compactness, nonemptiness, affineness, or a chosen point.

Recorded statement dependencies used, with signatures and docstrings inspected:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  These are locally ringed spaces locally affine, and their morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
  Its sole field is `Function.Surjective p` on points.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
  Its affine-open maps are étale ring homomorphisms. The inspected
  `Etale.iff_flat_and_formallyUnramified` gives flatness, formal unramifiedness, and
  local finite presentation, the equivalent notion recorded by the dependency.

All currently stated proof dependencies are imported. The recorded fibre-dimension
module is a legacy non-`module` file; Lean rejects importing it from a `module` file.
This consumer therefore uses the compatible legacy import format (all imports
are plain `import`), rather than duplicating or changing that dependency:

- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`:
  `AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `SmoothOfRelativeDimension`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.isBasis_affineOpens`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation.finitePresentation_appLE`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` (and the
  dependency's quasi-compactness notion is already available through this module).
- `Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint`:
  `AlgebraicGeometry.flat_composite_fibre_dimension_at_point`.
- `Sheaf.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension`:
  `AlgebraicGeometry.exists_etale_open_of_smooth_of_fibre_dimension_zero`.
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`:
  `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`.

Source and edge checks: read `literature/stacks-project/descent.tex`,
`lemma-etale-etale-local-source` (036W), and `morphisms.tex`,
`lemma-etale-permanence-two` (02K6), including its footnote explaining that local
finite presentation of the descended map follows from the other hypotheses.
For X empty the map h is étale by the empty source cover, and the signature allows it.
For Y empty, surjectivity forces X empty. For T empty, any admitted diagram also has
X and Y empty. Taking p to be an identity reduces to the given hypothesis on h.
Arbitrary non-quasi-compact covers remain allowed: smooth source descent only asks
flatness, surjectivity, and local finite presentation of p. No base field,
characteristic, Noetherianity, separation or global finite-type condition is introduced.
There is no `STATEMENT-DISPUTED` or identified node fault.

Searches (through `/home/ubuntu/weil-launcher-nt/msearch.py`, group Q02, this item):

- LeanFinder: “Etaleness of a scheme morphism descends along a surjective etale cover
  of its source”. Eight hits, including `IsEtale.of_comp`, postcomposition
  cancellation, base change, and ring-map locality; no exact statement.
- LeanSearch: “If p is a surjective etale morphism of schemes and p followed by h is
  etale, then h is etale”. Eight hits about composition, base change, and surjective
  ring maps; no exact statement.
- Loogle: `"Etale", "Surjective"`. Four hits: two ring algebra results, the
  `DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` target-base-change
  instance, and a geometric-point fibre surjectivity result; none is this assertion.
- Mathlib grep: `Etale.*of_comp|of_comp.*[Ee]tale|[Ee]tale.*[Ss]urjective|[Ss]urjective.*[Ee]tale`
  in `AlgebraicGeometry/Morphisms`. Four hits: weakly étale cancellation, the target
  base-change descent instance, `Etale.of_comp`, and its use for maps of étale objects.
  Reading the exact declarations confirms that none cancels a source cover to conclude
  étaleness of the second arrow, as required here.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared
  `lean/Sheaf` searched étale descent, cancellation, and surjectivity names. Results
  concern other descent constructions or uses of the opposite-arrow `Etale.of_comp`.
  Searching the item id finds only a consumer's proof docstring, not a declaration.
- Searched `dag/lean_names_upstream.json` for étale descent and cancellation: recorded
  names include `Etale.of_comp`, composition, base change, and unrelated cohomological
  descent. No exact source-cover theorem or duplicate of the proposed name was found.

Validation: the prescribed single-file `scompile.py` and `deliver2.py --no-push`
checks are run for this module. Their results are recorded below after completion.

## Second reading by Q02

This is the dispatch worker's own second pass, not an independent agent review;
the maintainer supplies the independent review under the direct-delivery brief.
With the node and module open, rechecked the three scheme binders, both arrow
orientations, all three property assumptions, and the sole conclusion. In particular,
`[Etale (p ≫ h)]` is étaleness of h ∘ p and the conclusion concerns h, so the
opposite-arrow Mathlib cancellation theorem was not mistaken for this node.
The source-cover hypothesis is genuinely surjectivity of p on X, with no finite or
quasi-compact condition. Empty schemes are admitted and the parameter u is explicit.
The proof docstring reproduces smooth descent, finite-type passage, pointwise fibre
dimensions, and source locality. No mismatch was found and no node field other than
`lean` was changed. All theorem proofs remain `sorry`, and no definition was added.

Compile repair: the initial module-format attempt was rejected because
`Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint` is non-`module`.
Removed the new `module` command and used ordinary imports for legacy compatibility.
The statement and dependency list are unchanged.

`scompile.py Q02 lem-trf-etale-descent-through-source-cover <module>` succeeded:
sandbox compilation 4.2 s, library-form single-file compilation 10.4 s, no errors
or warnings reported. All binders and the universe are explicit. The JSON signature
matches the file verbatim and a structural comparison confirms `lean` is the only
changed node key.

The prescribed `deliver2.py Q02 lem-trf-etale-descent-through-source-cover --no-push`
returned `OK (dry run)`: commit `0c2824907b` passes server preflight and per-file
compilation. The staged packet contains exactly the module, item node, and report.
