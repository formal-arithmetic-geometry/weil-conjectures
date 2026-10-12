## What changed

Completed `AlgebraicGeometry.Etale.finiteEtaleTrace_unique` in
`Sheaf.AlgebraicGeometry.FiniteEtaleTraceExistsUniqueness`, with its statement and docstring
unchanged. Added proof-only imports of `Sheaf.Paper.FiniteEtaleEtaleLocalSplit` and
`Mathlib.AlgebraicGeometry.Sites.Etale`.

The proof first derives component equality on every object over a splitting neighborhood,
using the common split sum, an explicitly constructed iterated-pullback comparison, both
localization identities, and cancellation of three isomorphisms. It then pulls the splitting
neighborhoods back to every object of the small site. Point lifting proves that this family
covers, and naturality plus sheaf separatedness establishes global component equality.
Dependent function extensionality finishes equality of the trace families.

Updated the item's DAG proof and dependencies to match these steps. The existing Mathlib leaf
`lem-weil-pbc-fibre-product-points` supplies point lifting; no new node is needed. The item's
unit is `sk-thm-p1`; the item is below its realized statement/steps, and the unit route is kept.

Searches: LeanFinder for trace uniqueness returned unrelated étale algebra and generic
sheaf extensionality declarations; Loogle for `"IsSheaf", "ext"` found the used
`Presheaf.IsSheaf.hom_ext_ofArrows`; the recorded Sites grep found sheaf separatedness APIs.
Project searches found no noncircular existing trace uniqueness theorem. The source was read
online at Stacks https://stacks.math.columbia.edu/tag/03SH and
https://stacks.math.columbia.edu/tag/04HN because the local literature files are absent.

## Proved and sorry left

`AlgebraicGeometry.Etale.finiteEtaleTrace_unique`: its sole original `sorry` is closed.
There are no `sorry`s in the delivered module and none added elsewhere; zero statements split
off. Local compilation succeeds without warnings in about 5 seconds, and every line has at
most 100 characters. The import-direction checker permits the splitting-theorem import.

The axiom audit prints `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`:
`finite_etale_etale_local_split` itself has these same transitive axioms, while
`upperStarIsoLocalizationRestriction` has only the three allowed axioms. Thus this is a
complete stage-3 reduction to the existing splitting declaration, whose deferred dependencies
remain separate work; it does not claim final transitive closure of the target.

Edge cases: no assumption that X or W has a point is used. Empty W is covered by the empty
family. The split formula is applied to arbitrary `Fintype J`, including empty J, and equality
uses the same sum on both sides. The naturality-in-F hypotheses are not required.

## No longer needed

No existing import is removed, and no entire module is claimed globally unreachable.
The following former proof dependencies are removed from this node:

- `lem-weil-pbc-cartesian-square-pasting`: the comparison and inverse are constructed using
  `pullback.lift` and verified by `pullback.hom_ext`.
- `lem-weil-pbc-etale-covering-base-change`: coverage of the pullback family is proved directly
  by `Scheme.Pullback.exists_preimage_pullback` and the small-site covering criterion.

These nodes may still be needed by other statements or proofs; the node's statement
dependencies are unchanged. `lem-weil-pbc-fibre-product-points` is the existing replacement
proof dependency for the second step.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The first dry run detected accidental
`letI`-to-`let` edits in the signature from a proof-linter cleanup. The original signature
was restored verbatim and the declaration-diff checker now reports no statement changes. The original DAG's general presheaf
transport and terminal-object specialization are unnecessary here: applying the split formula
to every object W over the splitting neighborhood directly supplies the required equality.
The source literature is not populated in this machine's read-only clone, so its primary
Stacks pages were read online. No library, target statement, definition, or tool was edited.

## Second reading by S2

1. **No accidental visible changes.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof body and a proof-only import changed. The DAG node changes only proof metadata and dependencies, with no statement change. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The transitive `sorryAx` comes only from the imported splitting theorem, as documented. Verdict: pass for this module's proof.

3. **Split statements and searches.** No statements were split off and no new nodes were added. Existing declarations and Mathlib searches recorded in the report were checked; no shorter existing trace uniqueness result was found. Verdict: pass.

4. **Pruning and route.** The proof uses the local splitting theorem, direct pullback constructions, point lifting, localization, and sheaf separatedness. The former cartesian-pasting and covering-base-change dependencies are no longer used and were removed from the node. The unit route through `sk-thm-p1` remains intact. Verdict: pass.

5. **DAG agreement.** The node's proof steps and `proof_deps` follow the Lean proof, including the replacement point-lifting dependency and removal of unused nodes. Verdict: pass.

Changed in this reading: appended this audit section only; no Lean code or theorem statement required repair.
