## What changed
Added a proved reduction theorem `constructible_of_short_exact` using the existing
constructible sub-quotient theorem. Added `finite_pushforward_data` as a named
intermediate statement collecting the geometric stalk and pullback construction.
The target theorem now combines these two statements.

## Proved and sorry left
Proved `CurveCoefficientPair.constructible_of_short_exact` and the target theorem
by applying the intermediate data theorem. `CurveCoefficientPair.finite_pushforward_data`
remains a single documented `sorry` (blueprint: lem-weil-pbc-finite-pushforward-constructible-descent).

## No longer needed
None; existing imports are retained for the stated geometric construction.

## Where the brief, the DAG or earlier work was wrong
The six-step geometric argument is substantial in Lean; it is isolated as one
strict intermediate existential theorem, while the quotient conclusion is fully proved.

## New nodes
`lem-weil-pbc-finite-pushforward-data` records the geometric short exact data left as
`sorry`; its node is delivered with this item.

## Second reading by P1
1. Compared the delivered module with the repository version: the target signature is
   byte-for-byte unchanged, and only proof declarations plus the documented split node
   were added.
2. Compiled the complete sandbox module successfully. There is one named `sorry`, in
   `CurveCoefficientPair.finite_pushforward_data`; no definitions contain `sorry`, and
   no forbidden declarations were introduced.
3. Checked the reduction theorem: it applies the existing constructible sub-quotient
   theorem with exactly the required torsion and short-exact hypotheses; the split
   existential is strictly weaker than the target and is mathematically the missing
   geometric construction.
4. Checked the proof route and imports against the node and source argument. The
   finite-stalk/counit construction remains isolated in the split theorem; no shorter
   available theorem was found, and no import was demonstrably removable.
5. Checked the DAG node and unit metadata: the split node names the delivered theorem,
   records its source and blueprint, and keeps unit `sk-thm-p1` realized through the
   original target.

Changed the proof docstring to obey the line-length convention and corrected this report
to identify the delivered split node explicitly.
