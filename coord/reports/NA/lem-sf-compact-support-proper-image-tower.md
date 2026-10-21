## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-compact-support-proper-image-tower.json`: statement node, split in four steps; no Mathlib match. No new nodes or Mathlib leaves.
- `citations.json`: seven verbatim statement excerpts covering all step/node pairs.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id and the compact-support, open-reduction and tower notions. No project declaration states this exact comparison. The related `lean/Sheaf/Paper/SfIntegralCompactSupportConstructible.lean` gives a proof sketch in which step 7 needs this argument, but its theorem is sorried and concerns integral constructibility, so it is not an attachment. `lean/Sheaf/SixFunctors/IntegralOpenReductionComparison.lean` is the already represented open comparison, not the requested proper-image tower comparison.

## WANTED

None.

## Corrections and source scope

The item had no proof. Its statement, statement dependencies, source, creation information and blueprint ancestry are retained. No statement dispute was found. The current blueprint ancestor is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-int-brown/def-weil-integral-rational-qbar-compact-support.md`, order 1849. Its integral derived-limit formula needs the finite-level transitions checked here. The older unit and chapter were read; their compactification formula is preserved, without any route replacement or edits to those files.

I read Bhatt–Scholze, Definition 6.7.6 and Lemma 6.7.7 (PDF p. 56), Stacks `sites-modules.tex`, Tag 0E8I, label `lemma-j-shriek-and-tensor`, and `sites-cohomology.tex`, Tag 0GL1, the same label. The paper defines the compact-support composite and establishes its constructible scope; it does not itself state this arbitrary-complete-object tower identity. The proof here is therefore explicitly marked agent-written, deducing the identity from the existing normalized open-reduction and scalar-restriction statements. It does not infer unbounded assertions from the paper's constructible statement. I also read Stacks `categories.tex`, Tag 0030, label `definition-system-over-poset`, for tower indexing and composites.

## Searches and reuse

There was no earlier item copy or report in the sandbox. The live item had inherited Mathlib search records; these are retained. Five new queries were run with the required `batch2/msearch.py`, using leanfinder twice with different phrasings, loogle, leansearch and grep. All services returned successfully. The exact queries and returned declaration names are appended to `mathlib_searches` from `searches.jsonl` without rewriting that log.

I read the returned types. The plausible diagram hit `localCohomology.diagramComp` (`Mathlib/Algebra/Homology/LocalCohomology.lean:109`) is the identity comparison for an ideal-indexed local-cohomology diagram; `CompactlySupportedContinuousMap.compLinearMap` (`Mathlib/Topology/ContinuousMap/CompactlySupported.lean:600`) concerns continuous functions. `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:478`) concerns ordinary scheme-module restriction. None supplies the pro-etale open reduction or its proper-image coefficient square. Generic category functoriality is used as an elementary calculation, not made into a redundant node.

DAG searches for the title concepts, proper-image towers, quotient transitions and Tag 0E8I found the already cited open-comparison and scalar-restriction nodes. Blueprint searches with `tools/blueprint_refs.py` for `proper-image reduction`, `quotient transitions` and `compact-support tower`, and a broad compact-support search, found no imported node with this exact statement. The integral compact-support definition is its ancestor, not an alternative statement of the tower isomorphism. `same_as` remains empty.

## Not duplicates

No new nodes were created. The existing open-reduction theorem gives a system comparison before direct image; the existing compact-support scalar-restriction theorem gives the coefficient comparison used to define the target tower's transitions. Neither alone is relabelled as the conclusion: the naturality computation in steps 1–3 proves the required equation.

## Review by NA

For step 1 I opened and read the full statement of `lem-sf-integral-open-reduction-comparison`, especially its specified natural system isomorphism, canonical tensor evaluation, and compatibility with every strict quotient transition. This supplies the displayed open square, including its actual quotient arrows. I compared its termwise open-extension identification with the one specified in the statement of `lem-sf-compact-support-restriction-of-scalars`: both keep the underlying sections and the quotient scalar action. That is why the square contains the same e_n that the target transition uses. Quasi-compactness of j and derived completeness of K are stated hypotheses here. Invertibility of ell on the schemes follows from their maps to Spec K_0. The notation is translated explicitly: the open theorem's R is this item's A and its A_n is this item's P_n. No change between ordinary constant finite coefficients and completed integral coefficients is assumed; reduction is exactly the open theorem's completed-ring reduction.

For step 2 I reread the scalar-restriction statement's actual formula: its comparison is proper direct image of the open identification followed by the normalized proper direct-image comparison. Thus v_n is exactly its value after applying the compact-support functor to k_n, in the correct order; it is not just some isomorphism with matching endpoints. The source is D_{n+1}J_{n+1}K_{n+1} and the target is S_n^Y D_n J_nK_n. I opened `def-weil-l-adic-coefficient-extension` and checked that it explicitly states that these P_n are finite local rings and specifies the quotient homomorphisms. The separated finite-type f and the fixed compactification satisfy the comparison's geometric assumptions. The direct-image morphism p is the same one in both towers.

For step 3 I opened `lem-weil-proetale-direct-image-restriction-of-scalars` and verified that its isomorphism is natural in the argument, rather than merely an objectwise existence assertion. Apply this naturality to the derived arrow alpha_n. I checked the square's source D_{n+1}S_n^V L_n and target S_n^Y D_n J_nK_n. Composing on the right with D_{n+1}(d_n), then substituting the open square, yields all three displayed lines. This is the explicit missing transition calculation. It uses no claims about preservation of injectives by scalar restriction, no base-change theorem, and no bound on K. The comparison theorem permits arbitrary scheme morphisms, so p is allowed. The remaining argument is a few-line application of this naturality statement and functor composition, and is marked elementary.

For step 4 I opened `def-weil-integral-derived-restriction-of-scalars`; its functor is exact termwise restriction of the completed coefficient sheaf. Restricting first to P_{n+1}, then to P_n gives the same action as the projection R_Y to P_n on every complex and arrow. This justifies the final change of coefficient category in the equation. I opened `def-weil-inverse-system`, which states the consecutive-arrow condition and componentwise composition. The displayed identity is precisely that condition. I wrote out the condition for the component inverses too, so no theorem about detection of isomorphisms by evaluation is silently invoked.

All four steps are shorter than 2000 characters. I checked B–E against the sources and the node statements: no new unsplit proof hidden in a statement; every non-elementary input is a cited existing node; all seven citations are literal substrings of the respective statements; no proof-only claim is borrowed from a cited node; no new statement or hypothesis is invented; no SGA source is used. The off-unit open comparison is declared as a tool use because it supplies a generic coefficient-system square needed by this unit, without replacing the compactification route.

I checked K=0, j=id, p=id, and the empty source. The first gives the zero tower and the same equation, j=id reduces the calculation to direct-image naturality, p=id reduces it to the open quotient square, and the empty source gives zero open extensions. The first transition n=1 only uses P_2 to P_1; no nonexistent P_0 is used. Quotient maps need not be flat: their derived reductions and strict transitions come from the existing open theorem. No constructibility, finite Tor-amplitude, boundedness, cohomological-dimension, inverse-limit comparison or compactification-independence result enters this proof.

## Unfinished work

None in the one-level split. The existing dependency nodes retain their own stage status. No Lean files were written and no compiler or build command was run.

## Validation

The standalone server `review_split` passed. The first delivery dry run required a longer excerpt for the direct-image naturality citation; I replaced the short phrase with the entire natural-isomorphism assertion, verbatim. This changes no argument or cited dependency.
