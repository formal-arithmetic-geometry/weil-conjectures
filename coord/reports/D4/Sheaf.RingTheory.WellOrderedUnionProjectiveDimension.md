## What changed

Replaced the sole proof hole in
`Sheaf.RingTheory.WellOrderedUnionProjectiveDimension` by natural-number induction.
The module, index type and filtration hypotheses are generalized before induction;
the successor helper receives the resulting hypothesis for every module and filtration.
The original declaration's signature and all original public imports are unchanged.

Added two modules, `Sheaf.RingTheory.WellOrderedUnionProjectiveDimensionZero` and
`Sheaf.RingTheory.WellOrderedUnionProjectiveDimensionSucc`, for the base and successor
obligations. Their docstrings now contain the source, complete arguments, universe
considerations and edge-case checks. Repaired the prior attempt's node signatures,
search records and self-contained statements, and updated the main node's proof route.
All three modules compile through `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in
`ModuleCat.hasProjectiveResolutionLE_of_wellOrderedUnion`
(node `lem-weil-pbc-well-ordered-union-projective-dimension`) by a complete Lean induction
from the two named obligations. This is a decomposition, not a proof independent of sorry.

Added two holes, each the whole proof of one named public theorem in its own module:

- `ModuleCat.hasProjectiveResolutionLE_of_wellOrderedUnion_zero`, node
  `lem-weil-pbc-well-ordered-union-zero-step`: splitting and the transfinite direct-sum
  argument, only at bound zero.
- `ModuleCat.hasProjectiveResolutionLE_of_wellOrderedUnion_succ`, node
  `lem-weil-pbc-well-ordered-union-succ-step`: the projective presentation, kernel
  filtration, dimension shift and splicing at a successor, assuming the smaller-bound
  induction hypothesis for every module and filtration.

The item's module has zero remaining holes. The delivered helper modules have two;
net local hole change is one closed minus two added. No definitions or axioms were added.
No imported existing theorem was edited. The item's axiom closure still includes the
helper sorries; no claim of a sorry-free target proof is made.

## No longer needed

Removed the item's proof imports `Sheaf.Algebra.ProjectiveDimensionWellDefined` and
`Sheaf.RingTheory.ProjectiveDimensionSESKernel`. Its only new proof imports are the
zero and successor helper modules. Public imports needed by the original signature stay.

`lem-weil-pbc-projective-dimension-well-defined` and its module
`Sheaf.Algebra.ProjectiveDimensionWellDefined` are no longer needed by this route:
identity resolutions and the spliced resolution have the required zero tails directly.
The free-module construction nodes `def-weil-pbc-free-module` and
`lem-weil-pbc-free-module-projective` are no longer needed by the successor argument;
use the projective presentations already supplied by the quotient resolutions instead.

The original main node's other proof dependencies are redistributed to the base and
successor nodes, not claimed globally pruned. In particular
`lem-weil-pbc-projective-dimension-ses-kernel` remains an intended dependency of the
successor obligation, although its module is not imported by the completed induction.
Nothing here changes a unit's realized statement or proof steps. No claim is made that
another target does not still require any of the locally unused nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier tool failure is repaired externally: `deliver3.py` now gets through its
import-source checks. The earlier sandbox nodes had empty Mathlib search lists and
placeholder `lean.statement` strings. The main node had not been updated, the helper
proof descriptions omitted key steps, and unused proof imports had not been removed.
These are repaired in this attempt. LeanSearch returned an internal server error;
LeanFinder, Loogle and the Mathlib source search ran and their real search records are
included, with no verdict fabricated for the unavailable service.

The original free-module proof assumes a universe containing R, but the item has
independent universes u and v. `Ring.projectiveDimensionLE_of_shortExact` is stated
only for `ModuleCat.{max u v} R`; it cannot directly discharge the successor obligation
for arbitrary v. Both helpers keep the item's generality. Their arguments use
categorical projectivity. In the successor, degree-zero projective presentations come
from the supplied quotient resolutions, and active indices inject into M, permitting
shrinking of the sum into universe v. Dimension shifting must be proved in this
category from the supplied resolutions by the Schanuel argument, or its existing
interface generalized in a later delivery. No interface was silently changed here.

Checked edge cases before retaining the new statements: an empty index type contradicts
hcover applied to zero; a single stage has zero predecessor; repeated stages have zero
quotients; the successor case at n=0 produces the usual two-term resolution. The
quotient comap and all universe binders agree with the item. The item does not realize
a unit-level statement or step, so this decomposition preserves the unit route.

Files changed are the three Lean modules, their three node records and this report.
The metadata repair script and searches.jsonl are sandbox-only working files.

## New nodes

`lem-weil-pbc-well-ordered-union-zero-step` is the base case of Stacks 0D1U, with module
`Sheaf.RingTheory.WellOrderedUnionProjectiveDimensionZero`. It records quotient
splitting, finite-support injectivity, well-founded surjectivity and projectivity.

`lem-weil-pbc-well-ordered-union-succ-step` is the induction step of Stacks 0D1U,
with module `Sheaf.RingTheory.WellOrderedUnionProjectiveDimensionSucc`. It records
projective presentations, their filtered kernel, dimension shifting, the supplied
smaller-bound hypothesis and splicing. The same-universe categorical presentation
variant is explicitly attributed as an agent adaptation of the source argument.

There are no statement/interface changes and no change records or forced adaptations.

## Second reading by D4

1. **Visible declarations and statements.** I compared the delivered main module with the repository version. The original theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. The two helper declarations are new split-off statements, and their signatures match the corresponding node `lean.statement` fields.

2. **Compilation and proof hygiene.** I compiled all three modules with `lcompile.py --all`; all compile cleanly. The main theorem has no `sorry`; the only remaining `sorry`s are the two named helper theorem proofs listed above. No definitions contain `sorry`, and no forbidden declarations (`axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`) were added. The helper statements are intentionally open obligations, so their axiom closure includes `sorryAx` until later work proves them.

3. **Truth and strength of split statements.** The zero helper is exactly the `n = 0` obligation and retains every filtration and quotient hypothesis. The successor helper is exactly the `n + 1` obligation, with a universally quantified induction hypothesis for arbitrary modules and filtrations in the same universes. Both are strictly smaller than the original induction theorem and preserve the original conclusion; edge cases (empty index, least stage, repeated stages, and `n = 0` successor) are addressed in their docstrings. No duplicate library theorem was found by repository search or the recorded Mathlib searches.

4. **Pruning and imports.** The main proof uses only the two helper modules, so the former proof-only imports of `ProjectiveDimensionWellDefined` and `ProjectiveDimensionSESKernel` were removed. Public imports needed by the original statement remain unchanged. The main node's proof and proof dependencies now record the induction and the two helper obligations; the helper node records contain their source, proof route, searches, and exact Lean declarations.

5. **Route and unit preservation.** The induction still realizes the unit's original well-ordered-union argument: zero case by splitting/direct sum, successor case by projective presentation, kernel filtration, dimension shift, induction, and splicing. The decomposition only exposes the two obligations as separate nodes and does not alter the unit statement or its realized route.

I changed only this report after the first dry run: added this second-reading record. No Lean source or node statement required repair.
