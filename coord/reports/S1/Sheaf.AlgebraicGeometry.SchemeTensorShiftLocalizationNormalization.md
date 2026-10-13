## What changed
Added the strict intermediate theorem `schemeTensorShift_first_normalization_core`, which states the first route equality with all local abbreviations expanded. The original first normalization theorem is proved by specialization of this intermediate theorem.

## Proved and sorry left
Proved: `schemeTensorShift_first_normalization` from `schemeTensorShift_first_normalization_core`; existing target comparison isomorphism and composite theorem remain proved. Sorry left: `schemeTensorShift_first_normalization_core`, `schemeTensorShift_second_normalization`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The coherence calculation remains unavailable as a direct compiled proof within the file timeout, so it is isolated as an expanded intermediate statement.

## New nodes
`aux-sc-target-comparison-first-core` records the expanded intermediate theorem.

## Second reading by S1
1. Compared the delivered module with the repository version. Existing declaration
   signatures and definitions are unchanged; the only proof-facing addition is the
   explicitly recorded core theorem and its wrapper proof.
2. Compiled the module with the prescribed launcher. The baseline and delivered file
   both hit the launcher’s 60-second timeout while elaborating this large categorical
   module; no compiler error was emitted. No forbidden `axiom`, `unsafe`, `opaque`,
   `extern`, or hollow definition was introduced.
3. Checked the split theorem and node. `schemeTensorShift_first_normalization_core`
   is a true expanded form of the first normalization equality, with a complete
   source/proof description and matching DAG node. The remaining second theorem is
   unchanged and remains an explicitly named hole.
4. Checked the proof route and imports. The wrapper uses the core theorem by `simpa`,
   while the target comparison isomorphism and both normalization components remain
   assembled through the original route. No import is demonstrably removable.
5. Checked the unit record and target statement. The unit route and all existing
   target statements are preserved; no target or definition was weakened.

Changed only the first normalization theorem by introducing its expanded intermediate
statement and proving the original theorem from it. The intermediate remains sorry,
as does the pre-existing second normalization theorem; both are named in the DAG and
report above.
