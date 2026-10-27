# Q42: lem-sfb-space-constructible-affine-etale-test

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-constructible-affine-etale-test.json`: statement, split in six steps; no Mathlib match for the algebraic-space chart criterion. Existing searches retained and the searches actually run in this attempt appended.
- `dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-space-spectral.json`: new statement-only prerequisite, unsplit; no Mathlib match. Stacks 0A4G says that the atlas point space of a qcqs algebraic space is spectral.
- `citations.json`: 28 entries, one verbatim statement excerpt for each citation occurrence in the six steps.
- `searches.jsonl`: actual msearch.py log. No hand-written entries.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and constructible/affine/etale terminology. The matching scheme and sheaf declarations do not state the algebraic-space point-set criterion. Also searched project source for the new spectral-space assertion: no completed matching project declaration was found. Mathlib declarations concern schemes or assume the requisite topological instances; they are not attachments for this item.

## WANTED

None. All sources used here are available locally.

## Corrections and scope

The statement is retained mathematically. Repeated TeX backslashes in the imported statement were normalized to single TeX commands; no hypothesis or conclusion was changed. “Quasi-separated algebraic space” is read in the standard absolute sense used in the cited Stacks source and in the existing splitting-filtration and permanence nodes. In particular no hypothesis on the base scheme's diagonal is inserted.

The source proof is Stacks `decent-spaces.tex`, Tag 0ECZ (`lemma-locally-constructible`), read in full through its final finite-union argument. I also read `spaces-properties.tex`, Tags 0ECT (`lemma-locally-constructible`) and 0ECU (`definition-locally-constructible`). The item is the qcqs specialization with condition (2) of 0ECT spelled out, so there is no need to add a definition of etale-local constructibility or a new node restating either implication. I used the same 07ST filtration as 0ECZ, already available as `lem-sfb-qcqs-space-splitting-filtration`.

I read the chapter/unit records and the latest blueprint unit and direct-images proof, especially paragraph (3). This is a general topological input in the inherited supporting chain, not a replacement for the unit's six-functor route. `blueprint_refs.py ancestor` reports a null ancestor for this imported auxiliary chain; I preserved that null and its existing via list, and prepended this item for the new child. Whole-blueprint searches for the chart criterion, locally constructible point topology, spectral algebraic spaces, and 0A4G found no duplicate blueprint statement.

The only new node has a complete statement with its own S and X, absolute diagonal hypothesis, point topology, and spectral-space definition. It carries no proof sketch. Its source, read in `spaces-properties.tex`, is Tag 0A4G (`lemma-quasi-compact-quasi-separated-spectral`), including the proof by an affine atlas and quasi-compact intersections. The existing stack spectrality nodes concern stacks over a field; they cannot be substituted silently for a space over an arbitrary scheme. The new node is a topological structural lemma independent of any subset E, not a restatement of either clause of the item.

## Not duplicates

lem-sfb-qcqs-space-spectral vs lem-weil-pbc-qcqs-scheme-spectral: the existing 094L node assumes a scheme; the new 0A4G node proves spectrality for algebraic spaces with their atlas point topology.

lem-sfb-qcqs-space-spectral vs lem-sfb-qc-diagonal-stack-spectral: the existing node assumes an algebraic stack over a field with a specified smooth-atlas topology; the new node concerns algebraic spaces over an arbitrary scheme and the already defined etale-atlas topology.

No existing node cites Tag 0A4G. I searched the whole DAG by that tag and by the spectral-space statement, and checked the named candidates above. The existing 07ST filtration is reused, as are 09YI restriction and 09YJ assembly; none is recreated.

## Review by Q42

I checked delivery-errors B through E against the node files, the local Stacks text, and each cited statement. My review concerns the actual mathematical inputs, not only JSON validation.

Step 1 is the explicit bridge between the affine-test definition of a quasi-compact morphism and inverse images of quasi-compact opens of the point space. `lem-a1-space-etale-open-image` supplies the open subspace corresponding to W; `lem-sfb-qc-space-affine-etale-atlas` supplies its affine surjective etale atlas. The definition of quasi-compactness then applies to that affine scheme B mapping to X. `lem-a1-space-point-open-calculus` supplies continuity and the exact fibre-product image identity, and `lem-weil-pbc-continuous-image-quasi-compact` gives quasi-compactness of the inverse-image subset. These are statements of the nodes, not claims lifted from their proofs. This is a few-line consequence of those inputs, marked elementary, not a new general lemma with the same proof moved elsewhere.

Step 2 checks both spaces in the retrocompact-open comparison. The affine-scheme qcqs node and qcqs-scheme spectrality apply to U; the new 0A4G node applies to X. `lem-sfb-space-qcqs-permanence` requires a quasi-compact source and a quasi-separated target, both present, and makes the test map quasi-compact. The point-calculus node supplies continuity. Step 1 and the existing retrocompact-iff-quasi-compact lemma establish exactly the hypothesis of `lem-weil-pbc-constructible-preimage` (005I). Thus the forward implication does not assert that an arbitrary continuous map preserves constructibility.

Step 3 uses `lem-sfb-space-change-base-to-integers` for the equivalence with spaces over Spec Z and for the small-etale-site identification, not just for the existence of a changed-base sheaf. This discharges the explicit base restriction of `lem-sfb-qcqs-space-splitting-filtration`. The filtration statement gives quasi-compact opens, quasi-compact separated schemes V_p, and the actual isomorphism over each reduced closed stratum. Returning along the equivalence equips V_p with its map to S. On every scheme test an open subspace inclusion is an open immersion; `lem-weil-pbc-open-immersion-etale` makes it etale, and `lem-trf-space-representable-etale-scheme-tests` provides composition and the comparison between scheme and representable etaleness. Therefore every affine open of V_p really gives a test covered by the item's hypothesis.

Step 4 uses the hypothesis only after those test maps have been checked. Affine opens give locally constructible E_p. `lem-pc-separated-quasi-separated` applied to the absolute structure morphism makes each separated V_p quasi-separated. Its quasi-compactness is supplied by the filtration, so `lem-trf-locally-constructible-qcqs-global` applies exactly as stated. The scheme spectrality node supplies the basis and intersection property used next. Quasi-compact-source permanence applies to the composite V_p to X without requiring quasi-separatedness of the base S.

Step 5 checks the missing complement condition that often invalidates a closed-subspace restriction. Step 1 makes O_p, the inverse image of the quasi-compact open U_(p+1), quasi-compact. It is retrocompact in the spectral point space of V_p, so its complement Z_p is constructible by the Boolean definition. `lem-weil-pbc-constructible-intersection-in-constructible` is applied with E=Z_p and E'=E_p, and therefore gives constructibility in the correct subspace Z_p. `lem-sfb-space-reduced-closed-support` explicitly identifies the base-changed closed point space with the inverse image as a homeomorphism. The isomorphism in the filtration, together with continuity in the point-calculus statement and the open-subspace homeomorphism, identifies this with T_p in X. I wrote out why homeomorphisms preserve the finite Boolean presentations, instead of hiding a constructibility comparison in the word “transport.” This uses 09YI in place of the source's 09YE, with both of its constructibility hypotheses verified.

Step 6 checks both quasi-compact opens defining every stratum are retrocompact in X, so T_p is constructible. `lem-weil-pbc-constructible-in-retrocompact-open`, despite its narrower title, states the full 09YJ result for an arbitrary constructible subspace of a space with a quasi-compact-open basis. I read that statement and use exactly that generality. It takes constructibility on T_p to constructibility in X. Finite union closure is explicitly part of `def-weil-constructible-subset`. The filtration differences cover X, yielding E. This is the assembly argument, not an application of a new node which already states the conclusion.

I checked small cases: X empty; E empty or all of X; empty strata or repeated successive opens; X an affine scheme (including a non-Noetherian one); and base S not assumed quasi-separated. The filtration allows empty spaces, and no argument selects a point from a stratum. The hypotheses on the new spectral-space node exclude the non-quasi-separated case where the retrocompact comparison would fail. The new node specializes to the established scheme result but does not identify the two point-space constructions by fiat. No Noetherian, separatedness of X, finite-type, or surjectivity condition on individual affine tests was added.

I also checked the graph inputs for cycles: the new spectral node has only definition dependencies, and the existing filtration and topological assembly nodes do not use the item. All non-elementary imported facts used in each step occur in that step's `uses`; all corresponding excerpts are copied verbatim into `citations.json`. Off-unit generic tools are declared in `split_report.tool_uses`, not in maintainer-owned `tool_uses`. All steps are under 1000 characters and there is no long inline lemma hidden in them. No SGA source is used. No Lean file or repository file was written, and no compiler, Lake or local DAG-checking tool was run.

For Mathlib I used msearch.py for every query and read its returned hits, then read the relevant source declarations. The new node has two semantic phrasings, Loogle, grep and LeanSearch records. Scheme instances in Properties.lean:43-60 and abstract SpectralSpace constructors in Topology/Spectral/Basic.lean:32-49 do not build the algebraic-space point topology. For the item, the first Loogle query mentioned a namespace as if it were a constant and returned an unknown-identifier message; I retained that actual result and ran a successful second query, "IsConstructible". The other searches return genuine constructibility facts, already used where appropriate, but not the whole item.

## Unfinished work

No part of the one-level split remains unfinished. The new 0A4G statement is intentionally unsplit for a later worker. Delivery validation and push follow this report.
