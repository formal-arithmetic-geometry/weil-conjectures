## Worker report

Item: `lem-trf-fibre-open-affine-reduction`, group NW, stage 2.
Module: `Sheaf.AlgebraicGeometry.FibreOpenAffineReduction`.
Declaration:
`AlgebraicGeometry.exists_affine_neighbourhood_quasiCompact_open_of_fiber_open`.
The only postponed proof is this theorem's `sorry`; no definitions or axioms are introduced.
The accepted statement, split, dependency lists and proof are unchanged. In particular the
previous worker's stale stage-1-dispatch refusal does not apply: brief-stage2 section 0
explicitly authorizes stating an accepted split with no usable Lean record. The queue lists
the item at stage 2, and its live `lean` field is null. No repair note exists for this item.

The source was read in `literature/stacks-project/more-morphisms.tex`, the first paragraph
of the proof of `lemma-fibre-geometrically-connected-reduced` (Tag 055W). Its preliminary
open-lifting reduction does not use the later geometric connectedness assumption. The
accepted DAG proof supplies the finite-subcover justification and explicitly handles empty T.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes Y and S and their morphism h | `{Y S : Scheme.{u}} (h : Y ⟶ S)` |
| h is flat | `[Flat h]` |
| h is of finite presentation, including quasi-separatedness | `[LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]` |
| Every scheme-theoretic fibre is geometrically reduced over its residue field | `hred : ∀ t : S, GeometricallyReduced (h.fiberToSpecResidueField t)` |
| A point s of S | `(s : S)` |
| Any open subscheme T of Y_s | `(T : (h.fiber s).Opens)`; no connectedness, nonemptiness or quasi-compactness premise |
| An affine open neighbourhood S₀ of s | `∃ S₀ : S.Opens, s ∈ S₀ ∧ IsAffineOpen S₀ ∧ ...` |
| An open subscheme W of Y ×_S S₀ | `∃ W : (pullback h S₀.ι).Opens, ...` |
| W is quasi-compact as a scheme | `CompactSpace W`, where the carrier of the open subscheme is used |
| W → S₀ is its canonical structure map | The explicit composite `W.ι ≫ pullback.snd h S₀.ι` throughout |
| This map is flat | `Flat (W.ι ≫ pullback.snd h S₀.ι)` |
| This map is of finite presentation | The three conjuncts `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` of this same composite |
| Its fibres are geometrically reduced | `∀ t : S₀, GeometricallyReduced ((W.ι ≫ pullback.snd h S₀.ι).fiberToSpecResidueField t)` |
| W_s equals T as open subschemes of Y_s, under the canonical fibre identification | `(h.fiberι s) ⁻¹ᵁ (W.ι ≫ pullback.fst h S₀.ι).opensRange = T` |

For the last clause, the first projection `pullback.fst h S₀.ι` is an open immersion
because it is the base change of `S₀.ι`. Its composite with `W.ι` is the canonical
open immersion into Y. `opensRange` is its actual open image; pulling it back along
`h.fiberι s` gives a specific element of `(h.fiber s).Opens`. An element of this lattice
has its canonical restricted structure sheaf and inclusion. Thus equality here means
equality of the corresponding open subschemes, with their inclusions. It is not an
arbitrary scheme isomorphism, and no arbitrary comparison map or choice is assumed.
Since `s ∈ S₀`, the base change of Y along the open neighbourhood has the canonical
same fibre at s, and this expression is precisely its W-fibre viewed in Y_s.

Recorded statement dependency declarations used, read with their signatures and docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; its docstring and `Flat.iff_flat_stalkMap` identify
  the affine-chart presentation with the stated stalkwise definition.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-pbc-scheme-conventions`: a convention node with no declaration/module.
  It explicitly prescribes finite presentation as the conjunction of local finite
  presentation, quasi-compactness and quasi-separatedness. The latter two classes are
  `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `.fiberι`, `.fiberToSpecResidueField`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `.Hom.residueFieldMap`; the residue
  field is used through `fiberToSpecResidueField`, whose target is its spectrum.
- `def-pc-geometrically-irreducible`: its recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` publicly imports the recorded
  `AlgebraicGeometry.GeometricallyReduced` in `Geometrically.Reduced`.
  This is applied only to structure morphisms of fibres over residue fields.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. Canonical open subschemes and their maps
  `W.ι` and `S₀.ι` use this notion; the same module supplies
  `AlgebraicGeometry.Scheme.Hom.opensRange`, with no replacement definition.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `.map`; the affine-open condition is the existing
  `AlgebraicGeometry.IsAffineOpen` in `Mathlib.AlgebraicGeometry.AffineScheme`,
  defined as affineness of the canonical open subscheme.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.

All proof dependencies were also read. Their modules are imported publicly when they
already serve a statement dependency and otherwise by plain `import`:

- `lem-weil-pbc-affine-opens-basis`: `Scheme.isBasis_affineOpens` in `AffineScheme`.
- `lem-weil-pbc-qcqs-morphism-permanence`: `quasiCompact_of_compactSpace`,
  `QuasiSeparated.of_quasiSeparatedSpace`, `QuasiCompact.compactSpace_of_compactSpace`,
  `quasiSeparatedSpace_of_quasiSeparated` and the quasi-compact, quasi-separated and
  locally-finitely-presented base-change instances, in the corresponding `Morphisms` modules.
- `lem-weil-pbc-flat-morphism-base-change`: `Flat.isStableUnderBaseChange` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `lem-weil-pbc-affine-scheme-qcqs`: `Scheme.compactSpace_of_isAffine` in
  `Mathlib.AlgebraicGeometry.AffineScheme`, and `quasiSeparatedSpace_of_isAffine` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and the already imported `QuasiCompact`.
- `pqf-def-locnoeth`, `pqf-lem-locnoeth-lft`, `lem-sfb-noetherian-open-immersion-qc`:
  `IsLocallyNoetherian`, `LocallyOfFiniteType.isLocallyNoetherian` and the open-immersion
  quasi-compactness instance in `Mathlib.AlgebraicGeometry.Noetherian`.
- `lem-weil-pbc-open-fibre-product`: `Scheme.pullback_map_isOpenImmersion` in
  `Mathlib.AlgebraicGeometry.Pullbacks` and `Scheme.Pullback.range_map` in
  `Mathlib.AlgebraicGeometry.PullbackCarrier`.
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`:
  `LocallyOfFinitePresentation.finitePresentation_appLE` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`:
  `quasiSeparatedSpace_iff_forall_affineOpens` and
  `Scheme.quasiSeparatedSpace_of_isOpenCover` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-pc-reduced-scheme`: `IsReduced` in `Mathlib.AlgebraicGeometry.Properties`.
  The remaining repeated proof dependencies are among the statement dependencies above.

Edge cases checked before writing:

- Empty T: the empty open W satisfies compactness and all restricted morphism
  conditions; geometric reducedness of empty fibres is permitted by the Mathlib class.
- Disconnected T: no connectedness predicate occurs in any premise or conclusion.
- T equal to the entire fibre: its quasi-compactness follows from finite presentation
  over a field; the finite affine subcover argument still applies.
- Non-closed s: `fiberι` and the induced subspace topology do not require a closed point.
- Empty Y and empty fibres are allowed. Empty S has no point s, so its instance of
  the universally quantified statement is vacuous, as in the node.
- S need not be quasi-compact or quasi-separated; only the chosen affine S₀ is.
  Y need not be separated. The input quasi-separatedness is that of h.
- No characteristic restriction or field perfection hypothesis is introduced.
- The explicit universe `u` is arbitrary; no smaller independent field/test universe
  is introduced. All scheme and fibre objects remain in the original scheme universe.

Searches for an existing statement:

- `msearch.py ... leanfinder`: query “An arbitrary open in a fibre of a flat finitely
  presented scheme morphism with geometrically reduced fibres lifts to a quasi compact
  open after restricting to an affine neighbourhood of the base point”. Eight hits:
  universal openness of flat lfp morphisms, flatness/affine-chart facts,
  `exists_isAffineOpen_preimage_eq` for inverse limits, and the affine criterion for
  quasi-compact morphisms. None states this prescribed fibre-open lift.
- `msearch.py ... loogle`: query
  `AlgebraicGeometry.Scheme.Hom.fiber, AlgebraicGeometry.IsAffineOpen`; zero hits.
- `msearch.py ... grep`: query
  `fibre.*open.*lift|fiber.*open.*lift|exists.*[Oo]pen.*[Ff]iber` in `AlgebraicGeometry`;
  zero Mathlib hits.
- `msearch.py ... leansearch`: query “An open subscheme of a fibre of a finitely
  presented morphism extends to a quasi compact open of the total space over an affine
  neighbourhood”. Eight hits: finite affine unions characterize compact opens,
  quasi-compact covers, affine neighbourhoods, `IsAffineOpen`, and local finite
  presentation of open immersions/restrictions. None gives the asserted fibre-open
  lift. The raw search results are preserved in the sandbox's `searches.jsonl`.
- `rg` of the above expression in both project roots `lean/WeilConjectures` and
  `lean/Sheaf`, plus a direct item-id search: no exact statement. The related upstream
  `AlgebraicGeometry.exists_affine_open_lift_of_generic_fibre` in
  `WeilConjectures.AlgebraicGeometry.GenericFibreAffineOpenLift` was read in full at
  its signature/docstring. It requires an affine integral base, a generic point,
  affine source and affine prescribed open; it is not this arbitrary-point,
  arbitrary-open statement. Other hits concern quasi-finite isolated fibre points,
  nonempty generic loci or unrelated sheaf fibres.
- Additional `rg` in all three Lean roots for
  `exists_affine.*fibre|exists_affine.*fiber|exists_affine.*open.*lift|exists_affine.*quasiCompact`
  found the same generic-fibre theorem and unrelated flat hypersurface, ample-open,
  perfect-complex and curve results. No declaration with the new name exists.

No statement fault or disputed mathematical assertion was found. No new nodes,
dependency repair modules or statement correction are needed. The accepted six proof
steps are reproduced in the theorem docstring, with their node references.

Validation: prescribed `scompile.py NW lem-trf-fibre-open-affine-reduction` compiled
the delivered file in sandbox mode (6.2 seconds) and its library module mode
(5.5 seconds), both with exit code 0 and no reported errors or unexpected warnings.
`autoImplicit` is false; every universe, variable and parameter is explicitly bound.
All Lean lines have length at most 100. The prescribed `deliver2.py ... --no-push`
reported `OK (dry run)`: the delivery passes preflight and compiles, with exactly
the item node, its module and this report staged. A separate JSON comparison confirms
that `lean` is the only changed node field and that its signature matches the file.

## Second reading by NW

This is the dispatched worker's separate second pass with the node and delivered
module open. No other agent was started, as the dispatch explicitly prohibits it;
the maintainer performs the independent review after delivery.

I checked every row of the correspondence table against the actual theorem signature.
Both input and output finite presentation include quasi-separatedness. W lives in
the actual pullback, and its structure map is the second projection preceded by
its canonical open inclusion. The geometric-reducedness clauses refer to each
fibre's own residue-field structure map, on the whole base and the chosen open base
respectively. The conclusion quantifies over every open T without implicit extra
structure or nonemptiness. `CompactSpace W` is absolute quasi-compactness of W,
separate from `QuasiCompact` of its map. The final equality is in the original
fibre's opens and uses only the canonical open image in Y; it preserves the
inclusion into the fibre and its restricted structure sheaf. The base point
membership supplies the stated canonical localization identification.

The node is unchanged except for its Lean record. The recorded signature was
extracted verbatim from the final file. All eleven statement dependencies have
usable records (the scheme-conventions node intentionally records a convention),
and the referenced declarations were used. No mismatch or further change was found.
