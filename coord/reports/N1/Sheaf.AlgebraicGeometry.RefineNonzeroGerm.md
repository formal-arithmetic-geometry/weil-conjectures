## What changed

Proved `AlgebraicGeometry.Scheme.refine_section_nonzero_germs` in
`lean/Sheaf/AlgebraicGeometry/RefineNonzeroGerm.lean`, with its statement unchanged.
Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`, whose proved
`CategoryTheory.constantSheafOverIso` identifies the two constant-sheaf restrictions.
The proof uses a set-sheaf trivialization, two pointed image-sieve refinements,
and local injectivity of sheafification. Its set-sheaf isomorphism is never assumed
additive. Updated the node's proof, dependencies, and proof origin to this route.
The unit `sk-prop-sf-cbc` has empty realized statement and step lists; no unit route
is bypassed. The argument retains the trivialization and refinement steps of the plan.

The proof was developed through single-file compiles. Final local compilation takes
about four seconds with no warnings and no increased heartbeat limit. A scoped
`backward.isDefEq.respectTransparency false` handles the etale-over objects during
elaboration. The simpler `overPullbackConstantSheafIso` implementation was tested,
but its right Kan extension instance search exceeds the heartbeat limit; the
already proved `constantSheafOverIso` compiles promptly.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.refine_section_nonzero_germs`
(node `lem-weil-pbc-refine-nonzero-germ`): 1 of 1 original sorries closed.
No sorry remains in the item; no new declarations, modules, or sorries were added.
The required dry run printed OK after local and server compilation and the axiom
probe. A separate `#print axioms AlgebraicGeometry.Scheme.refine_section_nonzero_germs`
compiled successfully and reported exactly `propext`, `Classical.choice`, and
`Quot.sound`. The dry run's only outstanding check is the second reading, which
the second reader supplies; nothing was pushed.

## No longer needed

No original import was removed: both public imports support the existing statement.
The following planned proof nodes are unused and removed from this item's
`proof_deps`:

- `lem-weil-pbc-sets-sheafification-geometric-stalk`
  (`Mathlib.CategoryTheory.Sites.Point.Skyscraper`, the stalk-isomorphism API).
- `lem-weil-pbc-colimit-constant-connected-diagram`
  (`Mathlib.CategoryTheory.Limits.Connected`, `isColimitConstCocone`).

Neither API is used in the proof. Their Mathlib modules may still be transitively
imported by the public statement imports; this delivery does not claim to remove
that transitive reach. The retained constant-sheaf definition and geometric-stalk
definition are used directly. Local bijectivity of sheafification replaces the
explicit computation of stalks of a constant sheaf. No project module becomes
unreached merely by removing the two Mathlib-leaf DAG dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or the planned route. The
constant-sheaf stalk formula and cofinality comparisons are unnecessary here:
local surjectivity produces the two constant representatives, and local
injectivity detects their equality on any pointed refinement. The existing
source proof in `WeilConjectures.ConstructibleSheaf.Restriction` provides the
chart and image-sieve pattern, but its module-valued theorem is not applicable
to the set-only local constancy hypothesis. Only the generic, already proved
constant-over-site isomorphism is imported as a tool.

Edge cases: the marked point supplies actual nonemptiness even when X or U could
otherwise be empty; a zero section cannot satisfy ha; no connectedness,
finiteness, or nonempty constant value is assumed; arbitrary algebraically closed
fields and every lift to V remain quantified exactly as in the original statement.

## Second reading by N1

1. Compared the complete delivered module with the repository using `diff` and
   separately compared the theorem signature byte for byte: unchanged. No existing
   declaration, definition, public import, or docstring was changed. The added
   import is proof-only, and the elaboration option is scoped to this theorem.
   No change record is needed. Verdict: pass.
2. Independently compiled the module with `lcompile.py`: clean, about four seconds.
   Compiled a scratch copy with `#print axioms`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Scanned the full module: no sorry and no
   prohibited declaration or trust escape. Read each refinement, naturality
   identity, and contradiction: the retained marked lift proves nonemptiness and
   m differs from z; local injectivity rules out a zero germ at every other lift.
   The set-sheaf chart is never treated as additive. Verdict: pass.
3. No statement is split off and no new declaration or node is introduced.
   Checked the relevant small cases: an empty scheme cannot supply the marked
   point; the zero section cannot satisfy ha; an empty or singleton constant
   value cannot supply the two distinct representatives. There is no hidden
   connectedness or finiteness assumption. Verdict: pass.
4. Searched the library for nonvanishing-germ and locally constant restriction
   results and ran an independent LeanFinder query using unequal germs and
   nonvanishing neighbourhoods. The results concern topological/ringed-space
   germs, not this etale statement. Read the upstream restriction theorem: its
   module-sheaf hypothesis is stronger, so it cannot replace this set-sheaf
   argument. The existing generic constant-over isomorphism is reused. Both
   public imports support the statement and the added plain import supplies
   that isomorphism. Every removed old proof dependency is listed under
   No longer needed. Inspected sk-prop-sf-cbc.realized (empty lists) and its
   recorded statement and steps; the proof bypasses no realized unit step.
   Verdict: pass.
5. Compared both node versions: only proof, proof_deps, and proof_origin differ.
   The union of step uses equals proof_deps. The new steps accurately describe
   the delivered chart, two image-sieve refinements, marked-point contradiction,
   and equalizer-sieve argument. The statement and Lean signature records are
   unchanged. Verdict: pass.

Second reading changed only this report by adding the independent review;
no repair to the proof, imports, or node was necessary.
