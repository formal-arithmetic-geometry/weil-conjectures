## What changed

Replaced `AlgebraicGeometry.Scheme.alternatingCechRestrictionHomotopy`'s sorry by a
complete Lean proof, preserving its signature and existing docstring. Added two
proof-only imports: `Sheaf.AlgebraicGeometry.AlternatingCechSection` and
`Sheaf.AlgebraicGeometry.AlternatingCechKernelNullHomotopic`. The first states the
signed extension section construction (Tags 01FJ/01FK); the second states that a
full-complex endomorphism with zero increasing coordinates is null homotopic
(Tag 01FM). Both have complete proof plans in their docstrings and nodes.

The main proof uses the exact section equation and the given coordinate formula to
show that `r ≫ i - id` vanishes on increasing tuples, applies the kernel theorem,
and uses `Homotopy.equivSubZero` and `Homotopy.ofEq` for the two conclusions.
No data is defined by choosing a witness from a mere existence theorem. The
section is eliminated only in the proof of an existential proposition. No existing
statement, definition or public import changed. All three modules compile cleanly
with the mandated compiler. Search found no existing ordered Čech contraction.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.alternatingCechRestrictionHomotopy`
(node `lem-pc-alternating-cech-restriction-homotopy`). No sorry remains in the item.
Added two holes, each strictly part of the original argument:
`AlgebraicGeometry.Scheme.alternatingCechRestrictionHomotopy_map`
(node `lem-pc-alternating-cech-section`) and
`AlgebraicGeometry.Scheme.alternatingCechKernelNullHomotopic`
(node `lem-pc-alternating-cech-kernel-null-homotopic`). This is a decomposition,
not a net reduction in the hole count and not an axiom-free proof of the full result.

Edge cases checked in the statements: empty I gives trivial products; singleton I
has no positive-degree increasing tuples; no covering hypothesis is needed.
The kernel theorem applies to any chain endomorphism annihilated by restriction;
it does not assume or conclude a homotopy inverse of restriction.

## No longer needed

Removed the unused `Mathlib.Algebra.Homology.Homotopy` import from the new
`AlternatingCechSection` module. The original public imports of the item are needed
by the preserved signature. In the parent node, `def-sc-zariski-site` and
`def-weil-pbc-site-cech-complex` are no longer direct proof dependencies: the latter
remains needed by both intermediate results, and the former is statement context.
No entire module is claimed to leave the target closure. No unit route is bypassed;
`sk-thm-picard-pn` has no realization assigned to this node.

## Where the brief, the DAG or earlier work was wrong

The existing sandbox only contained the original unproved theorem. The original
DAG's non-elementary signed extension and homotopy steps had no separate nodes;
these steps have now been isolated as two independent, strictly partial obligations.
No mathematical error is asserted in the original statement or plan. The source
files are not materialized under literature on this machine; the cited Stacks tags
were read directly at their published URLs.

## New nodes

`lem-pc-alternating-cech-section` states the section construction and exact retraction
of Tags 01FJ/01FK in
`lean/Sheaf/AlgebraicGeometry/AlternatingCechSection.lean`.

`lem-pc-alternating-cech-kernel-null-homotopic` states the kernel contraction from
the two Tag 01FM homotopies in
`lean/Sheaf/AlgebraicGeometry/AlternatingCechKernelNullHomotopic.lean`.

No change record is needed: existing statements and definitions are unchanged.

## Second reading by W3

1. **Interface and accidental changes.** Compared the delivered restriction-homotopy module with the repository version. The theorem signature and existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body were added. The two new modules contain the split declarations recorded in the DAG. Verdict: pass.

2. **Compilation and trust.** Compiled all three modules with `lcompile.py --all`; all compile cleanly. The only remaining `sorry`s are the two named split theorems, each a public theorem with a source, proof docstring, and matching DAG node. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition was found. Verdict: pass, with the two declared split obligations remaining.

3. **Truth and strength of split statements.** Checked the section statement against the signed-extension argument of Stacks Tags 01FJ/01FK and the kernel statement against Tag 01FM. Tested the empty-index and singleton-index edge cases conceptually; both statements remain valid and do not add a covering hypothesis. Each is a strict sub-obligation of the parent and is not a restatement. Verdict: pass.

4. **Shortest route and pruning.** Searched the local Sheaf sources and recorded LeanFinder, Loogle, and grep searches; no existing ordered-Cech contraction or section declaration was found. The parent proof uses the two split lemmas and the standard `Homotopy` conversion lemmas. Removed the unused public Homotopy import from the new section module. All remaining imports are needed. Verdict: pass after repair.

5. **DAG and unit route.** The parent node proof and `proof_deps` match the Lean proof, and both new nodes carry matching declarations, sources, proof plans, and search records. The unit record has no realized route assigned to this item, so no unit step is bypassed. Verdict: pass.

Changed in this second reading: removed the unused Homotopy import from the new section module and added this review section; no proof or statement changes were needed.
