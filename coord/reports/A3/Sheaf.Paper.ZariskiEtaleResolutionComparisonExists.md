## What changed

Preserved the complete signature and docstring of
`zariski_etale_resolution_comparison_exists`. Its proof now constructs an augmented
chain map and applies the section-homology comparison to that map, then assembles
all witnesses. Replaced its two original proof imports with the two new modules.

Added `Sheaf.Paper.ZariskiEtaleResolutionChainMapExists`: its theorem
`zariski_etale_resolution_comparison_chain_map_exists` is proved directly from Mathlib
by extending through injective terms and assembling the commutative squares with
`CochainComplex.mkHom`. Its hypotheses do not include fstar, hfstar, q, V or HasExt.
It does not require the pushed complex to be exact.

Added `Sheaf.Paper.ZariskiEtaleResolutionHomologyDataExists`: its public theorem is
the remaining computation of the canonical pullback-counit map on section homology
for a prescribed augmented comparison. It carries a complete proof in words, source
and node. Its proof plan uses the existing homology-independence theorem to handle
the prescribed comparison. Updated the parent node's proof and proof dependencies.
No existing statement, definition, public import or visibility changes.

## Proved and sorry left

Closed the one original hole in `zariski_etale_resolution_comparison_exists`
(node `lem-weil-pbc-zariski-etale-resolution-comparison-exists`). The assembly is a
complete Lean proof from the chain-map construction and the remaining comparison
obligation. This is a decomposition, not an axiom-free proof of the original result:
one hole closed, one lower hole added, net zero holes.

Fully proved `zariski_etale_resolution_comparison_chain_map_exists`
(node `lem-zariski-etale-resolution-chain-map-exists`); no hole added there.

The only delivered sorry is `zariski_etale_resolution_homology_data_exists`
(node `lem-zariski-etale-resolution-homology-data-exists`), whose proof is exactly
`by sorry` in its own new module. It does not assert existence of a comparison map;
that substantial part of the argument is already proved independently in Lean.

Compiled all three modules in import order with lcompile.py. The chain-map proof
first compiled with the original imports; pruning exposed the needed abelian-group
instance import, which was added explicitly, and all three then compiled successfully.

## No longer needed

Removed direct proof imports `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
and `Sheaf.CategoryTheory.SiteCohomologyPullback` from the original module. Their nodes
`lem-weil-pbc-right-derived-universal-delta-functor` and
`lem-weil-pbc-site-cohomology-pullback` remain needed by the homology-data obligation
and are imported there. Neither module is claimed globally pruned.

The chain-map construction needs neither of these modules, no cohomology-pullback
family, no Ext instance and no quasi-isomorphism of the pushed complex. No existing
DAG node or module becomes unneeded throughout the complete remaining argument.
The unit sk-thm-p1 and all its realized statement/step nodes are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt left its new obligations in the original module,
provided one-line docstrings without complete proofs or sources, recorded prose
instead of Lean signatures, and did not update the parent node. These are repaired:
one new statement per new module, complete documentation and exact signatures,
self-contained node statements, and the parent proof matching the assembly.
The formerly holed chain-map obligation is now proved.

The parent plan's phrase "Ext in the first variable is effaceable ... in the
coefficient variable" is misleading: the fixed first argument is the free abelian
sheaf, while effacement is in the second argument. The new homology-data proof
states this correctly. Existing statements and the original docstring are unchanged.

The source tex files are absent from this checkout; the local Stacks reference
copies were read for the resolution-cohomology and universal delta-functor argument.
LeanSearch returned Internal Server Error; this was recorded as unavailable.
LeanFinder, Loogle and local source searches worked. Existing global étale section
comparison statements do not cover the arbitrary site functor and objectwise
cohomology formula of this item.

Edge cases checked: q=0 has no incoming boundaries, empty V and the zero sheaf
are covered by the evaluation/Ext identifications, and the chain construction
uses only exactness of R, so does not incorrectly assume exactness of i_*I.
No data definition chooses arbitrary witnesses from an unproved existence theorem.

## New nodes

`lem-zariski-etale-resolution-chain-map-exists`, in
`dag/nodes/sec-proper-base-change/`, records the directly proved augmented chain-map
construction in `Sheaf.Paper.ZariskiEtaleResolutionChainMapExists`. It is independent
of cohomology and supplies the chain-map and augmentation part of the parent.

`lem-zariski-etale-resolution-homology-data-exists`, in the same node directory,
records the remaining section-homology computation in
`Sheaf.Paper.ZariskiEtaleResolutionHomologyDataExists`. It uses a prescribed augmented
chain map and proves the two identifications and their compatibility with the
normalized pullback followed by counit. It does not replace the chain-map construction.
No change record is needed: all existing signatures and public imports are preserved.

## Second reading by A3

1. **Visible changes and signatures — pass.** I compared the delivered parent module
   against the repository version. Its theorem signature and docstring are byte for byte
   unchanged; the two added modules contain only the newly recorded declarations.
2. **Compilation and proof status — pass.** All three delivered modules compile with
   `lcompile.py`; the chain-map theorem is proved without `sorry`, while the one remaining
   `sorry` is the named homology-data theorem. Scratch-copy `#print axioms` shows only `propext`, `Classical.choice` and
   `Quot.sound` for the chain-map theorem, and additionally `sorryAx` for the
   homology-data theorem and parent. No forbidden declarations or hollow definitions occur.
3. **Split statements — pass.** Both new statements are true reductions: the chain-map
   theorem supplies only the augmented comparison, and the homology-data theorem takes
   that comparison as input. Neither merely renames the parent existential. Their
   docstrings, sources and DAG nodes agree. I corrected the two new node signature
   fields to store the verbatim multiline Lean signatures. Independent LeanFinder,
   Loogle and local source searches found no ready-made theorem giving the full
   prescribed-comparison formula; resolution/Ext lemmas cover its constituent steps.
   Degree zero uses the augmentation identity; the zero sheaf and empty open have
   zero section cohomology, and positive degrees use coefficient effacement.
4. **Pruning and route — pass.** The parent proof uses both new modules; the chain-map
   construction uses the injective extension route, and the homology-data obligation keeps
   the universal-delta-functor, site-pullback and homology-independence dependencies. No
   unused proof import or realized unit step was removed.
5. **DAG agreement — pass.** The parent and both split nodes record the declarations,
   proof steps, dependencies and proof origins implemented by the delivered files. The
   unit `sk-thm-p1` remains realized through the parent route.

I added this report section and changed the two new nodes’ signature formatting to
verbatim Lean text. No Lean code repair was needed.
