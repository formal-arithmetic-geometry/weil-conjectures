## What changed

Reduced `AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleTrace_image_charts`
without changing its statement or its existing public imports. The proof now obtains
simultaneous normalized sheet charts, computes the actual trace-image ranges on
those charts, uses the existing continuous lattice sum theorem to identify the
range with continuous functions into the algebraic lattice sum, and constructs
the presentation explicitly.

The item adds proof imports of
`Sheaf.Paper.ContinuousFiniteEtaleLatticeSheetCharts`,
`Sheaf.Paper.FiniteEtaleTraceSheetRanges`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`.

The new `Sheaf.Paper.FiniteEtaleLatticeSheetMaps` module constructs the actual sheet
maps and the actual pulled-back categorical image inclusion from the existing
coefficient and composition comparisons. It proves the latter map monic.
There is no choice of arbitrary data from an unproved existence theorem.

The private helpers `additive_equiv_of_equal_ranges`, `latticeInclusion_injective`
and `presentation_of_range` are proved. In particular the final presentation is
not postulated: equal ranges and injectivity give unique additive lifts, and
naturality and the continuous scalar action are checked after the injective
continuous-function inclusion.
The module encoding is kept irreducible locally during this proof to avoid
unnecessary unfolding; its definition and public attributes are unchanged.

Two separate geometric/interface steps remain in new modules. The sheet-chart
step contains no trace morphism or trace image; the range step starts with a
specified splitting and actual sheet charts, assumes no local freeness, and
chooses no cover or charts. They are separate steps of the existing blueprint
argument, not a renaming of the original global existence theorem.

Validation: all four modules compiled with `lcompile.py --all`. The final main
module, with profiling options removed and the local irreducibility attribute,
compiled without warnings in 31.0 seconds. The helper modules compiled in 9.9,
45.8 and 15.1 seconds. The original theorem signature was compared verbatim,
and all Lean lines are at most 100 characters.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleTrace_image_charts`.
The item module now has zero holes. Added two holes, so this is a decomposition,
not a net proof gain (one closed minus two added = minus one):

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleLattice_sheet_charts`
  in `Sheaf.Paper.ContinuousFiniteEtaleLatticeSheetCharts`, node
  `lem-sfb-continuous-finite-etale-lattice-sheet-charts`.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleTrace_sheet_ranges`
  in `Sheaf.Paper.FiniteEtaleTraceSheetRanges`, node
  `lem-sfb-finite-etale-trace-sheet-ranges`.

Both are public named theorems with the entire proof `by sorry`, source locations,
and proofs in words. There are no holes in definitions or instances.
`finiteEtaleTraceImageEmbedding_mono` is proved, as are the three private helpers.

The new statements were checked on empty schemes, empty test objects, rank zero,
the identity cover, one sheet and multiple identical or distinct lattices.
The chart theorem discards empty cover members and uses an empty cover for an
empty base, so positivity does not exclude any case. The range theorem requires
a positive sheet count but neither surjectivity of the original p nor freeness
of P or M; its supplied splitting and sheet ranges provide exactly the local
hypotheses it needs. In particular it asserts no sectionwise surjectivity of an
arbitrary sheaf epimorphism: the continuous sum is already a sheaf, which is
why its section ranges agree with the categorical image.

## No longer needed

No existing module or public import is withdrawn, and no global pruning is claimed.
The original proof dependencies remain needed in the two geometric steps.
The parent's `proof_deps` now names the two new steps, the actual-map definitions,
the continuous lattice sum theorem and the encoding/presentation definitions.
Finite-etale local splitting, encoding-lattice and encoding-restriction comparison,
local-freeness pullback, and lattice-class local constancy have moved to the
sheet-chart step; trace-image comparison and exact pullback have moved to the
range step. This is redistribution of needed dependencies, not pruning.
No unit statement or step is bypassed. The range-step plan also names the existing
generic tools `splitProEtaleModuleProductMap_isIso`, `comapUpperStarIso_mate`
and `comapUpperStarIso_comp`. Their sources were read: they prove the actual
counit product comparison and the coefficient-restriction mate/composition
identities needed to identify the canonical sheet maps. They replace no
unit-level argument. No maintainer-owned `tool_uses` field is edited.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or change of mathematical route. The original node's three
steps are mathematically appropriate. Their declarations do not directly supply
the required glue: lattice classes and the trace-image theorem use sectionwise
module sheaves, coefficient transports and slice encodings, while this item uses
internal modules and the categorical image of a specified trace. The normalized
sheet embeddings, rather than mere abstract isomorphisms, must be retained.
The two remaining theorems isolate that glue. The new actual-map module makes
those maps explicit, so the trace normalization is not replaced by an arbitrary
isomorphism or by an assumed epic trace.

## New nodes

`def-sfb-finite-etale-lattice-sheet-maps` records the constructed sheet maps and
pulled-back trace-image inclusion in `Sheaf.Paper.FiniteEtaleLatticeSheetMaps`,
including the proved monicity instance. All data are explicit composites of
existing maps. No existing interface changes, consumers to adapt or change
records are required.

`lem-sfb-continuous-finite-etale-lattice-sheet-charts` records the trace-independent
common-refinement and normalized embedded-sheet-range assertion. It follows the
second paragraph of Local computation, together with finite-etale splitting.

`lem-sfb-finite-etale-trace-sheet-ranges` records the computation of the categorical
trace image on an already supplied split chart. It follows the first paragraph
of Local computation and the continuous lattice sum theorem to eliminate the
remaining image sheafification. It assumes no local freeness and makes no
existence assertion about covers or coordinates.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
