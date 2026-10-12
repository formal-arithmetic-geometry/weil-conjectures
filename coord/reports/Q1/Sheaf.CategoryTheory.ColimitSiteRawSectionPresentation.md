## What changed

Added `ColimitSiteRawSectionCompatibility`, an intermediate compatibility theorem whose
conclusion is the canonical isomorphism and generator equations for a fixed colimit cocone.
The target theorem now constructs the standard Type-valued colimit cocone and combines its
colimit property with that intermediate statement.

## Proved and sorry left

`raw_section_presentation` is proved by a real combination of the chosen colimit cocone and
`raw_section_presentation_compatibility`. The latter remains a named `sorry` intermediate
(statement node `lem-weil-pbc-colimit-site-raw-section-compatibility`).

## No longer needed

The target proof no longer directly uses `def-weil-pbc-arrows-functor`,
`def-weil-pbc-category-colimit`, `def-weil-pbc-sites-and-cohomology`, or
`lem-weil-pbc-filtered-colimit-sets-elementwise`; these remain available through the
statement imports and are still dependencies of the split compatibility node. No source
import was removed because the existing theorem signature needs the category-theory and
site declarations.

## Where the brief, the DAG or earlier work was wrong

The full filtered Kan extension and finite-refinement argument is too large to close in this
item; it was split into the strictly smaller fixed-cocone compatibility statement above.

## New nodes

`lem-weil-pbc-colimit-site-raw-section-compatibility` records the remaining compatibility
argument and its source in Stacks Tag 0A35.

## Earlier second reading (a previous round; superseded)

Pending independent second reading of the intermediate statement and proof decomposition.

## Second reading by Q1

1. Compared the delivered presentation module with the repository version. The theorem
   signature and its definitions are byte-for-byte unchanged; only a proof-only import and
   proof body were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`; there are no errors, forbidden
   declarations, or additional `sorry`s beyond the named compatibility theorem. The target
   proof uses only the allowed axioms through its imported split theorem. Verdict: pass.
3. Checked the split-off statement and node. The compatibility theorem fixes an arbitrary
   colimit cocone and supplies the canonical equation, so it is a genuine stricter
   intermediate rather than a renamed copy of the target; its remaining `sorry` has a
   source, proof sketch, and node. Verdict: pass.
4. Re-read the proof from the target downward. The target now chooses `colimit.cocone D`,
   obtains `colimit.isColimit D`, and applies the compatibility theorem. The target node's
   proof and `proof_deps` were pruned to this route; the earlier filtered-colimit and
   construction dependencies are no longer direct dependencies. Verdict: pass.
5. The unit route is preserved: the target still goes through the canonical raw-section
   presentation, with the compatibility theorem realizing the fixed-cocone comparison
   step. Verdict: pass.

Changed the target node's proof route and dependencies, and recorded the checks above. No
Lean statement or definition was changed, and no imports were removed.
