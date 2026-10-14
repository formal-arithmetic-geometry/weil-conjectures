## What changed

Replaced the proof hole in `AlgebraicGeometry.relativeMV_cover_rows` by a complete
combination of a geometric chain square and a proved algebraic mapping-cylinder
replacement. Its signature and public imports are unchanged.

Added `Sheaf.CategoryTheory.DerivedCategory.ConeDiagramFullSESPresentation`:
`cone_diagram_full_ses_presentation` proves the functorial cylinder construction,
including the middle-component identity missing from the existing theorem. Its
private construction follows the existing G1 cylinder implementation, with the
additional projection computation. No arbitrary witness is used in a definition.

Added `Sheaf.AlgebraicGeometry.RelativeMVCoverChainSquare` for the remaining geometric
step. This asks for a strict square and its prescribed cone comparison, before any
short exact replacement. The main proof constructs short exact rows from that
square and explicitly transports all six comparisons and all three components.

## Proved and sorry left

Closed the original hole: `AlgebraicGeometry.relativeMV_cover_rows`
(`lem-pc-relative-mv-cover-rows`).

Proved without sorry: `cone_diagram_full_ses_presentation`
(`lem-pc-cone-diagram-full-ses-presentation`) and its private cylinder helpers.

Added one hole: `AlgebraicGeometry.relativeMV_cover_chain_square`
(`lem-pc-relative-mv-cover-chain-square`). This contains the geometric resolution,
comparison and strictification steps, with source and proof in its docstring and
node. No sorry remains in the assigned module. This is a decomposition: one upper
hole closed and one geometric hole added, net zero; the algebraic short exact
replacement is fully proved. No other hole is introduced.

Edge cases: empty opens give zero local terms, repeated opens give split restriction
rows, zero coefficients give zero diagrams. The algebraic proof works for arbitrary
chain maps, including zero maps and zero complexes. No compactness, affine,
flatness or quasi-coherence hypothesis was added.

## No longer needed

Removed direct proof imports from the assigned module:
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`;
- `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`;
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`;
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`.

These four dependencies remain in the geometric split module and are not pruned
from the target closure. All six old proof dependencies leave the main node and remain needed in the
geometric node:
- `prop-pur-kinjective-resolutions-exist`;
- `lem-pc-kinjective-mayer-vietoris-presentation`;
- `def-pc-derived-pullback`;
- `lem-pc-mayer-vietoris-underived-open-counit-square`;
- `lem-pc-derived-direct-image-composition`;
- `def-pc-relative-mv-maps`. No node or module is claimed globally pruned.
The restricted `RelativeMVSESPresentation`, `RelativeMVConePresentation` and
`EndpointConePresentation` are not imported: their hypotheses are too restrictive
or their middle component is not prescribed. The existing cone-diagram SES module
also omits the middle identity, so its construction is reused in the new proved
module without importing that API.

## Where the brief, the DAG or earlier work was wrong

The recorded proof dependencies supply the individual geometric ingredients, but
none directly states the coherent finite-diagram lift and prescribed overlap
comparison. That work remains explicitly in the new geometric statement.
The existing generic SES presentation only records the first and third vertical
components; applying it alone cannot prove the two middle projection equalities.
The new generic theorem proves precisely the additional component computation.

The unit `sk-thm-picard-coherence` has empty realized statement/step lists. This
split retains the original geometric route and separates its algebraic replacement;
no unit statement or route is bypassed. No existing definition, statement or
visibility changes; no forced adaptations or change records.

## New nodes

`lem-pc-relative-mv-cover-chain-square`: the geometric chain-level step before short
exact cylinder replacement; one sorry, with all original geometric dependencies and
the existing homotopy-square rectification node.

`lem-pc-cone-diagram-full-ses-presentation`: generic functorial short exact cylinder
replacement retaining all three vertical components; fully proved from Mathlib.
The original cover-rows node now records these two dependencies and the explicit
composition/projection proof. Searches found no exact Mathlib or blueprint match;
the existing G1 implementation supplies the algebraic construction.

## Second reading by F1

1. Compared the assigned module with the repository using a declaration/signature
   comparison and the source diff. Verdict: its existing theorem signature is
   byte-for-byte unchanged, as are its public imports, definitions and visibility.
   The other two delivered modules are new. No change record or forced adaptation
   is needed; no open change record for these modules was found.
2. Compiled all three modules in dependency order through lcompile.py without errors
   or warnings. Read the cylinder definitions and degreewise splitting proof, its
   contractible-cone projection comparison and its functorial row map. All data are
   explicit; no definition selects an arbitrary witness from an unproved existence
   theorem. There is exactly one textual sorry, the entire proof of the public named
   geometric theorem. No prohibited declaration or kernel-check bypass appears.
   Scratch #print axioms shows only propext, Classical.choice and Quot.sound for
   cone_diagram_full_ses_presentation; the two geometric declarations additionally
   use sorryAx, as reported. Verdict: the algebraic proof is complete; the assigned
   theorem is conditional on the explicitly reported geometric hole.
3. Read the split theorem and its natural-language proof against Stacks Tags 08BV,
   08HZ, 08FE and 08HY and the existing HomotopySquareRectification implementation.
   Empty opens (with the other open covering), repeated opens (necessarily the
   whole space for a cover), zero objects and zero comparison maps introduce no
   extra assumptions. The cone comparison must come from the resolved geometric
   diagram; a generic triangulated-category completion would not prescribe it.
   Independent leanfinder, loogle and grep searches are recorded in its node.
   Checked CommutativeSquareLift, EndpointConePresentation, RelativeMVConePresentation
   and ConeDiagramSESPresentation: none supplies this unrestricted comparison with
   the middle and overlap maps both prescribed. Verdict: the geometric step is
   needed and true by the enhanced resolved-diagram construction. It omits the
   separate algebraic short-exact replacement, which is now proved, so this is a
   genuine decomposition rather than merely renaming the original hole. It is not
   a net proof gain, and closing the geometric step requires substantial further
   formalization rather than a few-minute application of an existing theorem.
4. Read the main proof from its conclusion backwards. It transports all six
   isomorphisms and the first/third component identities, then uses both biproduct
   projection identities on the proved middle component. The discarded horizontal
   cylinder identities are stronger than the assigned statement needs, not missing
   obligations. Imports distinguish public signature dependencies from proof-only
   dependencies. All six former proof_deps are accounted for under No longer needed;
   they move to the geometric node and no module leaves the target closure. The
   unit's realized lists are empty, and the original geometric route is retained.
   Verdict: no shorter applicable library theorem found and no unit route bypassed.
5. Compared the existing node changes and both new nodes with the Lean declarations.
   Existing node edits concern only lean/proof/proof_deps/proof_origin. The new nodes
   have sources, complete proof plans, search records, split status, creation and
   blueprint provenance and verbatim Lean statements. The assigned node's two
   proof dependencies are exactly the two theorems its proof applies; the geometric
   node retains the original geometric ingredients and specified-cone rectification.
   Verdict: the records agree with the reduction and the one remaining hole.

Second reading changed documentation only: expanded the geometric node's informal
statement to spell out its hypotheses and vertices instead of referring to the
assigned item; recorded independent searches; explicitly listed all six displaced
proof-dependency node IDs in the pruning report. No Lean proof or signature changed.

Sources checked: [unbounded Mayer--Vietoris](https://stacks.math.columbia.edu/tag/08BV),
[relative Mayer--Vietoris](https://stacks.math.columbia.edu/tag/08HZ),
[open restriction](https://stacks.math.columbia.edu/tag/08FE),
[base-change mate](https://stacks.math.columbia.edu/tag/08HY), and
[cylinder factorization](https://stacks.math.columbia.edu/tag/013N).
