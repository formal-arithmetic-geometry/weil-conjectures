## What changed
Proved `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_fullOpen_pushforward_iso` by
specializing the existing open-restriction comparison to the full open, then composing
restriction/pullback and inverse-pushforward functor isomorphisms. Added two proof-only
imports: `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.
No existing signature, definition, visibility, or public import changed.

## Proved and sorry left
Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_fullOpen_pushforward_iso`.
Added zero holes; no `sorry` remains in the delivered module. No split-off statements.
The proof depends on the existing open theorem
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_iso`
(node `lem-sc-exterior-sheaf-restrict-iso`), which still has `sorry` upstream.
Thus this closes the local hole, not the target's entire axiom closure.
The draft's new holes `exteriorSheaf_restrict_iso_pullback` and
`exteriorSheaf_pushforward_pullback_iso`, and their proposed nodes, were removed.

## No longer needed
No original import removed; the exterior-sheaf import is needed for the signature.
All four old direct proof dependencies are replaced by
`lem-sc-exterior-sheaf-restrict-iso`: `def-pc-scheme`,
`def-weil-sheaf-of-modules-category`, `def-sc-sheaf-exterior-power`, and
`lem-pc-presheaf-module-sheafification-ring`.
The first three still occur as statement dependencies; exterior sheafification is
handled within the existing restriction theorem. No whole module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong
The draft missed the existing arbitrary-open exterior restriction comparison and the
proved upstream `pullbackIsoPushforwardInv`. Its proposed two-hole decomposition was
unnecessary. Its new theorem comments were ordinary comments, not docstrings, and
its existing node had not been updated to describe the composition. These faults are
eliminated by removing both proposed declarations and recording the actual reduction.

## Second reading by H1
1. Compared the entire delivered module against the repository with `diff`.
   The original theorem signature is byte-for-byte unchanged; no definitions change.
   No relevant open change record was found. Verdict: pass.
2. The delivered module compiles without errors or warnings through `lcompile.py`.
   It contains no sorry, axiom, unsafe, opaque, implemented_by, or extern declaration.
   A scratch `#print axioms` check records the allowed standard axioms and `sorryAx`
   from the existing open restriction theorem. Verdict: pass with that existing dependency.
3. No new statement or split-off hole remains. Searched the library by restriction,
   full-open, inverse pushforward, and exterior-sheaf terms, and read both existing
   comparison declarations and their proofs/docstrings. The construction requires no
   local freeness and applies to degree zero and the empty scheme. Verdict: pass.
4. Used the shortest found route through existing library declarations. Both new imports
   are proof-only and used; the sole public import supplies the signature. Listed every
   obsolete direct proof dependency above. The unit `sk-thm-picard-duality` has empty
   realized statement/step lists; this change is below its unit route and changes neither
   the unit nor its realization. Verdict: pass.
5. The existing node now records the open-restriction specialization and the exact
   functor-isomorphism composition, with its used node as the sole proof dependency.
   No new nodes remain. Verdict: pass.

Second reading changed: removed both redundant split-off lemmas/nodes, replaced the
proof by the existing-library composition, corrected the original node's proof metadata,
and rewrote the report to distinguish local closure from the remaining upstream hole.
