## What changed

Replaced the earlier same-statement auxiliary with an actual resolution argument.
`Sheaf.Paper.ZariskiEtaleResolutionMap` keeps its original public signature and
constructs its witnesses from one comparison b, then uses homology independence
to transfer the formula to the given arbitrary comparison a.

Added `Sheaf.Paper.ZariskiEtaleResolutionHomologyIndependent`, fully proved.
Exact inverse image makes the direct image preserve injectives. A coinductive
null homotopy of a-b is constructed by exactness of R and injectivity of the
pushed terms. Additive evaluation preserves this homotopy, so the two section
homology maps agree. This does not require i_*I to be a resolution.

Added `Sheaf.Paper.ZariskiEtaleResolutionComparisonExists` for the remaining
construction and canonical-map identification (steps 1–2 of the original plan).
The existence theorem is used only within a proof of a proposition; no definition
chooses data from its unproved existence statement.

Updated the parent node and supplied one node per new module. All three modules
compile together using lcompile.py. No existing signature, definition, instance,
visibility, or public import was changed. The second reader restored the two
planned proof-dependency imports in the comparison-existence module.

## Proved and sorry left

Closed the original hole `zariski_etale_resolution_map`
(node `lem-weil-pbc-zariski-etale-resolution-map`). This is a decomposition,
not a claim that the canonical resolution construction is proved.

Added one hole: `zariski_etale_resolution_comparison_exists`
(node `lem-weil-pbc-zariski-etale-resolution-comparison-exists`). It constructs
one augmentation-compatible comparison and the evaluation identifications,
with the canonical-map formula. Its docstring contains the source and proof plan.

Proved `zariski_etale_resolution_homology_independent`
(node `lem-weil-pbc-zariski-etale-resolution-homology-independent`) with no sorry.
No sorry remains in the original module. The earlier attempted duplicate
`zariski_etale_resolution_map_aux` was removed. Holes closed: 1; holes added: 1;
net: 0, with the homotopy-independence part fully discharged.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
and `Sheaf.CategoryTheory.SiteCohomologyPullback` from the original module.
These remain planned dependencies of the new comparison-existence node, so
neither is claimed pruned from the targets' closure.

The parent now directly uses only the two new nodes. Its old direct proof
edges to `def-weil-pbc-sites-and-cohomology`, `def-sp-injective-resolutions`,
`lem-weil-pbc-site-cohomology-pullback` and
`lem-weil-pbc-right-derived-universal-delta-functor` move to the appropriate
subargument; these nodes are still needed. The old direct proof dependency
`lem-weil-pbc-derived-functor-map-via-lift` is not needed by the new proof:
its arbitrary-comparison role is discharged by the proved null-homotopy lemma.
It is a Mathlib leaf, so no additional Sheaf module becomes globally unreachable.
No public import was removed; no other module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt merely renamed the complete theorem and left that
copy sorry. It did not separate a strict subargument. The present delivery
separates comparison construction from independence and actually proves the
latter (including the non-quasi-isomorphic pushed-complex case).

Mathlib's InjectiveResolution.descHomotopy cannot be applied directly: i_*I need
not resolve i_*F. Its null-homotopy induction only uses source exactness and target
termwise injectivity, however; the proof generalizes that induction explicitly.

Edge checks: q=0 uses the initial exact sequence of R; the induction handles every
positive degree. No local vanishing, quasi-isomorphism, invertibility of a, or
inclusion-specific condition was added. The comparison-existence statement
asserts the formula for its constructed identifications, not for arbitrary additive
equivalences. The unit route is unchanged.

The local literature paths are absent on this machine. The cited Stacks tags
01FB, 013P and 015B were read at their official web pages; the new statements
follow the existing parent plan and these resolution/comparison results.

## New nodes

`lem-weil-pbc-zariski-etale-resolution-comparison-exists`:
`lean/Sheaf/Paper/ZariskiEtaleResolutionComparisonExists.lean`, declaration
`zariski_etale_resolution_comparison_exists`. Remaining construction of one
comparison representing the canonical map; no arbitrary input comparison.

`lem-weil-pbc-zariski-etale-resolution-homology-independent`:
`lean/Sheaf/Paper/ZariskiEtaleResolutionHomologyIndependent.lean`, declaration
`zariski_etale_resolution_homology_independent`. Fully proved equality of homology
maps for two augmentation-compatible comparisons. No change records are needed.

## Second reading by U1

1. Compared the delivered parent module with the repository version. The public
   theorem signature is byte-for-byte unchanged; the only changes are proof imports
   and the proof body. The two added modules and their declarations are new split
   nodes, as recorded above. Verdict: pass.

2. Compiled all three modules with `lcompile.py --all`, and compiled the parent and
   homology-independence modules individually. No errors or warnings occurred. The
   only remaining `sorry` is the named theorem
   `zariski_etale_resolution_comparison_exists`; there are no forbidden declarations
   or sorries in definitions. Explicit `#print axioms` scratch copies show only
   propext, Classical.choice and Quot.sound for homology independence, and these
   plus sorryAx for comparison existence and the parent. Verdict: pass, with the
   documented split hole.

3. Checked the split statements against their proofs and nodes. The comparison
   theorem constructs one comparison and its identifications, while the independence
   theorem proves a strictly smaller equality for two given comparisons; neither
   restates the parent target. The homology-independence proof is fully discharged.
   Repeated searches with augmentation/homotopy terminology found Mathlib
   InjectiveResolution.descHomotopy, whose target must itself be a resolution;
   it cannot apply to the pushed complex without an extra exactness assumption.
   The degree-zero and successive-degree cases are covered explicitly by exact₀
   and exact_succ. Verdict: pass.

4. The parent proof first uses the comparison-existence result and then the proved
   homology-independence result. The unit route remains represented by the parent
   node and its downstream use. Removed direct proof-only imports are not needed by
   the delivered parent; the old comparison-construction dependencies remain in the
   split node. Verdict: pass.

5. The parent node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof;
   both new nodes have matching Lean records, sources, statements, and dependency
   lists. Verdict: pass.

Second reading restored proof-only imports of RightDerivedUniversalDeltaFunctor
and SiteCohomologyPullback in the comparison-existence module, preserving its
planned dependency route. Corrected its docstring to say that Ext is effaceable
in the second (coefficient) argument with the first argument fixed. No theorem
signature or proof body changed. Replaced the two new nodes' whitespace-normalized
Lean statement records with the verbatim signatures from their modules.
