# Repair of lem-trf-ordinary-point-delta-branches

## Files written

The sandbox initially contained only dispatcher brief markers: no node files, report, citations or search log. I copied the current repository item, which contains the returned 11-step, 8831-character proof. Its statement, Lean record, source record, imported metadata and ancestry are unchanged. The current project declaration `AlgebraicGeometry.ordinary_point_delta_branches` in `lean/Sheaf/AlgebraicGeometry/OrdinaryPointDeltaBranches.lean:106` ends in `sorry`; searches under `lean/WeilConjectures/` found no full attachment.

- `dag/nodes/sec-trace-formula/lem-trf-ordinary-point-delta-branches.json`: statement retained; five assembly steps, 2197 characters.
- `dag/nodes/sec-trace-formula/lem-trf-coordinate-axes-normalization.json`: statement, status unsplit, 1413 characters; four logged Mathlib searches, no complete match; no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-curve-delta-completion-data.json`: statement, status unsplit, 1738 characters; four logged Mathlib searches, no complete match; no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-normalization-pair-ring-invariance.json`: statement, status unsplit, 1692 characters; four logged Mathlib searches, no complete match; no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-normalized-curve-branch-coordinates.json`: statement, status unsplit, 1520 characters; four logged Mathlib searches, no complete match; no proof steps or proof dependencies.
- `citations.json`: one verbatim statement quotation for every node used by every assembly step.
- `searches.jsonl`: unmodified search-command output log for the four new nodes. The parent's historical Mathlib searches remain unchanged in its JSON.

## Attachments

None. The project theorem still has sorry; no upstream declaration gives the whole item or any whole new node. The existing general coordinate theorem `lem-trf-regular-complete-coefficient-coordinates` is reused as an input for the branch-coordinate task, not duplicated as a new coefficient-field theorem.

## WANTED

WANTED: the original item's `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Appendix B, printed pp. 56–57, remains absent locally. I did not claim to have read this PDF. This repair reads the available Stacks sources instead: varieties.tex 0C1R/0C3V and curves.tex 0C1U/0C1V, including their proofs and the explicit axes-ring discussion. The new nodes have local source documents and exact labels/tags; the parent assembly's proof_origin now names the local Stacks text. No SGA source was used.

## What was wrong and what changed

The return is about work distribution: the already reviewed mathematical argument is too large for one item. Four independent results now carry it, each with a self-contained statement and empty proof. They are not the branch–delta inequality or a disguised complete ordinary-point theorem. The inequality and its equality test still follow from the elementary residue quotient calculation in the parent. The extracted work is geometric normalization/completion, the actual power-series coordinates on its branches, the algebra of the concrete axes ring, and invariance of normalized pairs under ring isomorphisms. These can be proved independently and none depends on the parent or any other new node.

The ring-versus-k-algebra distinction in the old reviewer's Step 11 correction is preserved. A node gives a ring isomorphism only. The new pair-invariance statement provides equal quotient dimensions by composition length, and the parent's equality criterion then supplies the scalar-compatible presentation. I did not assume an arbitrary ring isomorphism is k-linear.

No target statement, unit route or chapter changed. I read the chapter record and sk-i-curve-zero. This is its inherited historical exceptional-fibre normalization branch; the contemporary contracting-correspondence route remains exactly as recorded in the parent blueprint field. The new blueprint.from fields insert the item at the head of via and identify precisely which returned steps they extract.

## Work-distribution map and proof plans for future workers

1. `lem-trf-curve-delta-completion-data` carries old Steps 1–3 (2488 characters): restriction of normalization to an affine open, finite nonempty fibre, closedness and structural residue field of its points, Noetherianity and dimension of A; nonsmooth finite-length normalization quotient and smooth normal-locus case; finite simple filtration and k-dimension; comparison with the normalization of the completion. Its statement explicitly includes the tensor-product comparison, the k-linear quotient comparison, and B=A in the smooth case. Existing inputs are the normalization/finite-fibres/residue-field/Noetherianity nodes, `lem-trf-normalization-singular-skyscraper`, `lem-trf-curve-normalization-completion`, the simple-filtration theorem, and the regularity/smoothness and dimension-one normality tools. In the smooth case the quotient comparison is the zero-module map, not an invocation of the singular-support theorem at a point outside S.

2. `lem-trf-normalized-curve-branch-coordinates` carries old Steps 4–5 (1786 characters): completion of a finite algebra with actual fibre indices; normal curve smoothness over the perfect field; affine connected separated neighbourhoods for the DVR theorem; DVR completion; completeness and residue field with the given structural coefficients; expansion in every chosen uniformizer. The old coefficient expansion is retained verbatim below. The existing `lem-trf-regular-complete-coefficient-coordinates` also gives the evaluation isomorphism after its hypotheses are checked, so this new node is not a second general coefficient-field theorem. It additionally constructs the product for the actual normalization, its H-algebra compatibility, and the identical residue maps from H. The Step 5 completeness repair is retained: use `lem-weil-pbc-local-completion-local-ring` to identify the maximal ideal and `lem-weil-pbc-adic-completion-mod-ideal` for completeness, rather than incorrectly attributing completeness to the DVR-preservation node alone.

3. `lem-trf-coordinate-axes-normalization` carries old Steps 7–8 (1842 characters): separate-axis evaluation, its equal-constant image, its infinite-series kernel obtained by assigning mixed monomials to the first two positive indices; finite generation by coordinate idempotents and integrality; the conductor element s, the product of fraction fields, characterization of non-zero-divisors by their coordinates, and the normality/projection of monic equations proving that D is the entire normalization. The statement includes D/P and its P-action through the residue field, so neither the equality converse nor the node case needs to use its eventual proof. No primeness or irreducibility of the axes ring is assumed.

4. `lem-trf-normalization-pair-ring-invariance` carries the comparison in old Step 9 and old Step 11 (1644 characters): preserve non-zero-divisors and send a/s to phi(a)/phi(s); transport monic equations in both directions; obtain the quotient map with semilinear module action; transport submodule chains and composition length; recognize primitive idempotents as coordinate idempotents in products of nonzero local domains. For completeness, the length-to-k-dimension argument also applies here: a simple module over a local ring with structural residue field k is k, so a finite composition series has one-dimensional simple factors. The quotient need not itself be killed by the maximal ideal. It is killed by that ideal in the two-axis case by the separate axes calculation. Thus an arbitrary ring isomorphism suffices for branch number and defect dimension, while scalar compatibility is needed only to call the induced map k-linear.

Old Step 6 remains the parent residue-map argument. Old Step 10 remains the parent's short use of existing regularity and smoothness theorems. Old Step 9 is assembled using the new axes calculation and pair invariance. Old Step 11 is assembled using those same nodes and the existing nodal-point definition. The entire returned proof, including these retained arguments, is copied below so no calculation is discarded or blurred by shortening the parent.

## Review by Q97

Renewed repair on 2026-10-23, for the return naming head f0ef96862ea: I began with the mandated dry run on the retained sandbox. It exited with a same-tag check naming four current nodes. I opened their entire statements and also the newer split-node component-normalization statement. The finite-support skyscraper result supplies a coherent sheaf decomposition, the coherent-support result supplies the normalization cokernel and its support, the finite-colength comparison supplies a general completion quotient map under a finite-length hypothesis, and the stalk-Euler result needs properness and gives global cohomology. None states the retained geometric completion-data node in full. The split-node component result requires a fixed nodal completion; the retained statements allow arbitrary reduced curve singularities. Ten explicit comparisons below cover both retained nodes that share these sources. These current nodes are useful inputs for their future proofs; they do not justify deleting the retained statement-only tasks.

I compared the retained parent with the current repository again: its statement, statement dependencies, ancestry, source and Lean metadata still agree; its assembly replaces the original eleven-step proof. All thirteen retained quotation entries remained verbatim in the current dependency statements. I re-read those eight cited statements, Stacks varieties.tex 0C1R/0C3V and curves.tex 0C1U/0C1V, and the coefficient-field result 0C0S. I retained the search log after reading all sixteen recorded results: none of the new statements or search questions changed. The four new nodes remain unsplit and have no proof or proof dependencies.

I made a further mathematical repair in Step 5: the nodal argument now explicitly invokes Step 1's finite normalization and finite defect and Step 2's actual-fibre local-domain factors before applying pair invariance to a possibly non-k-linear ring isomorphism. Both supporting nodes are now direct citations of that step, with new verbatim entries in citations.json. Thus no geometric branch count is inferred merely from the definition of a node, and scalar-independent invariance is applied with all its hypotheses present. Steps 1--4 retain their previously checked arguments, including the diagonal-residue quotient calculation and the separable extension k/k in the smoothness criterion. I rechecked b=1, b=2, the cusp and the tacnode; no statement change is needed. The current project-source attachment search found no full declaration under WeilConjectures, and the Sheaf theorem still ends in sorry. The delivery tool performs the rebase onto its freshly fetched current server DAG; no git command was run in the shared repository.

This renewed repair follows the repeated landing refusal that the side completion had not been promoted into the live queue DAG. I retained all four statement-only nodes, the full old argument, the prior review and duplicate comparisons, and the recorded search results. The required initial dry run completed successfully at `574e5578c02` on 2026-10-22. I then compared the sandbox parent with the current read clone: only proof, proof_deps, proof_origin and split_report differed; the statement, statement dependencies, source, blueprint ancestry, Lean and reviewed_lean records agreed. All eleven retained citation entries matched verbatim in the current cited statements. There is no changed cited hypothesis to repair in those quotations. The required delivery tool prepares the rebased commit against its freshly fetched server DAG; I made no git call or change in the read-only repository.

I nevertheless repaired the assembly itself before resubmission: Step 3 now checks the hypotheses of normalization-pair invariance explicitly, rather than leaving their application implicit. Reducedness, Noetherian locality, structural residue field, finite normalization and finite defect come from the local-data statement; the nonzero local-domain factors come from the branch-coordinate statement; the axes statement supplies the matching hypotheses for P. Step 3 now cites those first two nodes directly and citations.json contains their verbatim statements there as well. This makes the new submission a concrete proof-and-citation repair of the retained delivery. The four new statements have not changed, so their original searches and logged results are reused without inventing or rerunning queries.

I re-read Stacks varieties.tex 0C1R and 0C3V, curves.tex 0C1U and 0C1V, and algebra.tex 0C0S. In the nodal case the source criterion provides only a ring isomorphism; the ring-invariance statement compares composition lengths without scalar compatibility, and the equality criterion subsequently supplies the k-algebra presentation. For b=1 the axes ideal is empty and the defect is zero; for b=2 its quotient is one-dimensional; the cusp and tacnode still have strictly larger defect than b-1. All five assembly steps remain below 2000 characters, and their total remains below 3000. The current Lean declaration at OrdinaryPointDeltaBranches.lean:106 still ends in sorry, and the project-source attachment search found no full proof. No new source, target statement, unit route, or Lean file is introduced by this renewed repair.


The present repair addresses the later landing refusal (returned head eb8e750c088), rather than repeating the earlier work-distribution repair unchanged. The current shared DAG still contains the original eleven-step proof; comparing it with the retained delivery shows exactly four changed parent fields before this repair: proof, proof_deps, proof_origin and split_report. Its statement, stmt_deps, blueprint ancestry, source, imported fields and Lean/reviewed_lean metadata agree, and are preserved. The delivery command rebases the retained sandbox onto the current server DAG in its own worktree.

I re-read all current statements cited by the five assembly steps: the four retained new nodes, the nodal local criterion, power-series regularity, completion regularity, and separable-residue smoothness. Each existing citation quote remains an exact substring of its current statement; there is no changed hypothesis to import into the assembly. Step 1 now spells out C as the m_A-adic completion of B, its finite tensor-product description, and the local hypotheses needed later by pair invariance, eliminating the ambiguity in the old shorthand widehat B. No argument or statement has been weakened.

The first fresh dry run identified newer same-tag nodes. I opened the complete statements of lem-sfb-nodal-completed-normalization-model, lem-trf-finite-dvr-branch-completion, lem-trf-flat-birational-normalization-comparison, and lem-trf-nagata-normalization-dvr-branches. The nodal model has properness and nodality hypotheses absent here. The other three separate uncompleted normalization, completed DVR products and flat birational comparison; none supplies the complete geometric local-defect result or the structural power-series coordinates for actual fibre points. These are potential inputs for the future proofs of the retained unsplit nodes, not substitutes for their full statements. Eight explicit pair comparisons are added under Not duplicates. I re-read Stacks varieties.tex 0C1R/0C3V and curves.tex 0C1U/0C1V and checked the residue quotient and b=1 and b=2 cases again. The retained search log and recorded queries were read and reused because none of the four new statements or their search questions changed.


I read the available primary Stacks text at varieties.tex `lemma-prepare-delta-invariant` (0C1R), `lemma-normalization-same-after-completion` (0C3V), `lemma-delta-number-branches-inequality-sh` (0C42), `lemma-delta-number-branches-inequality` (0C43), and curves.tex `equation-multicross` (0C1U) with `lemma-multicross-algebra` (0C1V). I also read algebra.tex `lemma-regular-complete-containing-coefficient-field` (0C0S). These are respectively the sources for new local completion data, branch coordinates, the axes computation and the ordinary-point assembly. The pair-invariance result is marked agent-written in its source: it explicitly states the comparison the old argument needed, not a claim that 0C1U states an abstract ring-invariance theorem verbatim. Its definition of integral closure is algebra.tex 00GP.

For assembly Step 1 I read the full new local-data statement. It gives finite positive b, finite k-dimension, the exact quotient comparison and C as normalization of H, including smooth points. No singular-only conclusion is applied at a smooth point. For Step 2 I read the full branch-coordinate statement; its last sentence gives exactly the diagonal structural residue image used. The kernel P/H and surjection to k^b/Delta k follow directly from the definitions, and finite-dimensional additivity applies because Step 1 gives finite dimension. b>=1 makes the diagonal injective and its dimension one.

For Step 3 the axes statement gives the specific k-algebra isomorphism, the integral closure D and the quotient dimension; the pair-invariance statement gives the normalization extension for H isomorphic to that ring, and explicitly gives the scalar-compatible quotient map in the k-algebra case. All its hypotheses hold: H is reduced Noetherian local with residue field k by Step 1; its finite normalization is the finite completed B; the branch coordinates give nonzero local-domain factors; the axes node supplies the corresponding assertions for P. Both quotient dimensions are finite.

For Step 4 I opened the actual statements of `lem-weil-pbc-power-series-field-cohen-regular-complete`, `lem-weil-pbc-completion-regular-local` and `lem-weil-pbc-regular-local-separable-residue-smooth`. They give regularity of the one-variable field power-series ring, the equivalence of regularity with that of the Noetherian local completion, and regularity iff smoothness on a finite-type affine chart when the residue extension is separable. Here it is k/k, so that hypothesis is satisfied. The smooth-to-zero-defect direction is an explicit conclusion of the local-data node, not a hidden normality citation.

For Step 5 I opened `lem-trf-nodal-point-local-criterion`: its opening definition of a node is precisely the geometric completed ring isomorphism being used, without assuming scalar compatibility. As k is algebraically closed, no residue-field or geometric-base-extension discrepancy remains. The axes theorem gives two normalization factors and one-dimensional quotient for R_2. Pair invariance is valid for a ring isomorphism, so b=2 and delta=1 follow before using the equality criterion to obtain a k-algebra presentation. The reverse implication uses the same ring definition and invariant comparison; it does not presume that being ordinary two-fold already names the actual normalization fibre cardinality.

I read every old proof-dependency statement as well, to check that extraction preserved the specific facts rather than only their names. The singular quotient theorem is restricted to its S; normal-locus isomorphism handles its complement. The finite-algebra-completion node supplies the product with its actual local maps. The normalized-curve DVR theorem needs a separated connected curve, supplied by an affine neighbourhood in the integral normalization component. The power-series normality theorem requires a Noetherian normal domain, satisfied by the field k. The finite-length filtration node supplies the filtration only; identification of simple quotients with k is written in the retained argument, not attributed to its statement.

Small-case checks: b=1 gives P=D, empty mixed-monomial ideal, zero defect and a regular completion; b=2 gives the node, two primitive idempotents in its normalization and simple quotient; b=3 gives the three-axis ring with defect two, not the plane triple point (defect three). The cusp has one branch and positive defect, so the inequality is strict; the tacnode has two branches and defect two, again strict. An irreducible nodal curve may have two completed local branches although it has one global irreducible component; both the fibre indexing and completed product in the new nodes allow this. The empty scheme supplies no closed x, and b=0 is deliberately excluded from the axes statement. A non-k-linear ring automorphism is covered through length, not falsely treated as k-linear.

I checked delivery-errors B–E point by point: four self-contained statements with empty proofs; inline definitions or actual definition-node dependencies; proper TeX; exact local Stacks tags and labels; four genuine logged search kinds per node; searches with two semantic phrasings and inspection of the hits; no claimed Mathlib leaf without a full match; ancestor and whole-blueprint duplicate searches; every non-elementary parent input named, with verbatim quotations; no new dependency back to the item; the original clause is not moved wholesale into one node; all three smoothness hypotheses are checked explicitly. No parent step exceeds 2000 characters and its combined proof is below 3000. No compiler, Lake or local preflight was run. No repository, launcher or Lean file was written.

The existing cross-unit tools used directly by Step 4 remain declared in split_report.tool_uses as generic local algebra tools; their old accepted top-level tool_uses metadata was preserved. The new nodes inherit the same unit, so they introduce no undeclared route change. Whole-blueprint searches for coordinate axes, normalization completion, coefficient field, integral closure isomorphism, multicross, normalization quotient, complete discrete valuation and ring isomorphism found no exact statement. Source-tag collisions are compared below.

## Not duplicates

lem-trf-curve-delta-completion-data vs lem-trf-coherent-finite-support-skyscrapers: the existing theorem decomposes a coherent module whose finite closed support is assumed; it does not construct a curve normalization, its completed integral closure, or structural power-series coordinates.

lem-trf-curve-delta-completion-data vs lem-trf-curve-normalization-coherent-support: the existing theorem identifies the coherent normalization cokernel and its smooth-locus support and gives local-ring properties; it has no completion comparison, completed normalization, or branch-coordinate assertion.

lem-trf-curve-delta-completion-data vs lem-trf-finite-colength-completion-comparison: the existing algebra theorem assumes a finite ring injection and finite-length quotient and compares their completions and tensor products; it does not establish those hypotheses for a curve, normalize the completed local ring, or construct coordinates on the actual geometric branches.

lem-trf-curve-delta-completion-data vs lem-trf-finite-curve-quotient-stalk-euler: the existing theorem assumes a proper curve and a finite generically isomorphic morphism and gives a global sections and Euler-characteristic formula; it has no completed local normalization or structural branch-coordinate conclusion and properness is absent here.

lem-trf-curve-delta-completion-data vs lem-trf-split-node-component-normalization: the existing theorem assumes a fixed two-axis nodal completion and describes component membership of its two branches; the retained node applies to arbitrary reduced curve singularities, with no nodal-completion hypothesis.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-coherent-finite-support-skyscrapers: the existing theorem decomposes a coherent module whose finite closed support is assumed; it does not construct a curve normalization, its completed integral closure, or structural power-series coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-curve-normalization-coherent-support: the existing theorem identifies the coherent normalization cokernel and its smooth-locus support and gives local-ring properties; it has no completion comparison, completed normalization, or branch-coordinate assertion.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-finite-colength-completion-comparison: the existing algebra theorem assumes a finite ring injection and finite-length quotient and compares their completions and tensor products; it does not establish those hypotheses for a curve, normalize the completed local ring, or construct coordinates on the actual geometric branches.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-finite-curve-quotient-stalk-euler: the existing theorem assumes a proper curve and a finite generically isomorphic morphism and gives a global sections and Euler-characteristic formula; it has no completed local normalization or structural branch-coordinate conclusion and properness is absent here.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-split-node-component-normalization: the existing theorem assumes a fixed two-axis nodal completion and describes component membership of its two branches; the retained node applies to arbitrary reduced curve singularities, with no nodal-completion hypothesis.

lem-trf-curve-delta-completion-data vs lem-sfb-nodal-completed-normalization-model: the existing node assumes a proper curve smooth except at nodes and describes its two-branch model; the retained new node applies to arbitrary reduced finite-type pure curves and gives finite defect, length/dimension, and canonical quotient completion comparison at every closed point, including non-nodal singularities.

lem-trf-curve-delta-completion-data vs lem-trf-finite-dvr-branch-completion: the existing algebra lemma assumes a finite injection with DVR localizations and concludes a completed product and normality; it does not construct the geometric normalization or identify its finite-length defect with its completed quotient over the structural field.

lem-trf-curve-delta-completion-data vs lem-trf-flat-birational-normalization-comparison: the existing node assumes a finite birational algebra and a flat scalar extension and compares total fractions and integral closures; it does not give geometric finiteness, structural residue fields, finite defect, its k-linear completion comparison, or the smooth-point case.

lem-trf-curve-delta-completion-data vs lem-trf-nagata-normalization-dvr-branches: the existing node constructs finite normalization and local DVR branches for a Nagata local ring but expressly has no completion conclusion; it does not assert the geometric fibre or finite-defect quotient comparison of the retained new node.

lem-trf-normalized-curve-branch-coordinates vs lem-sfb-nodal-completed-normalization-model: the existing statement assumes properness and only nodes, with two power-series branches there; the retained new node constructs coordinates on every actual normalization branch of an arbitrary reduced finite-type pure curve, for all positive branch counts and arbitrary chosen uniformizers, with structural residue compatibility.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-finite-dvr-branch-completion: the existing node supplies the algebraic completed-DVR product under finite-injection and DVR hypotheses; it does not establish these hypotheses for the geometric normalization, give structural coefficient-field power-series evaluation for arbitrary uniformizers, or identify the diagonal residue image of the original completed local ring.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-flat-birational-normalization-comparison: the existing node is a total-fraction and integral-closure comparison under flat base change; it neither constructs actual normalization fibre indices and their completed DVRs nor gives structural power-series coordinates and the diagonal residue map.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-nagata-normalization-dvr-branches: the existing node gives uncompleted DVR localizations of an algebraic normalization; it provides neither the canonical completed product for the geometric fibre nor structural power-series coordinates and their common residue image.


lem-trf-coordinate-axes-normalization vs def-trf-conductor-cokernel: the existing statement concerns Normalization cokernel sheaf; the new statement proves the formal mixed-monomial kernel, actual equal-constant subring, finite normalization, total fraction ring and residue quotient for all positive b. A definition of an ordinary point does not provide these theorems.

lem-trf-coordinate-axes-normalization vs lem-trf-ordinary-point-delta-branches: the existing parent is the full branch–delta inequality and ordinary-point criterion, whereas this new statement isolates an independent input and asserts neither the inequality nor the equality characterization.

lem-trf-coordinate-axes-normalization vs def-trf-ordinary-multiple-point: the existing statement concerns Ordinary multiple points and their coordinate-axes algebras; the new statement proves the formal mixed-monomial kernel, actual equal-constant subring, finite normalization, total fraction ring and residue quotient for all positive b. A definition of an ordinary point does not provide these theorems.

lem-trf-coordinate-axes-normalization vs lem-trf-nodal-contraction-normalization-branches: the existing statement concerns Normalization branches at a nodal contraction boundary; the new statement proves the formal mixed-monomial kernel, actual equal-constant subring, finite normalization, total fraction ring and residue quotient for all positive b. A definition of an ordinary point does not provide these theorems.

lem-trf-curve-delta-completion-data vs lem-trf-stacks-nodal-closed-subcurve: the existing statement concerns Stacks lemma for a reduced closed subcurve of a nodal curve; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-trf-reduced-curve-normalization-genus: the existing statement concerns Normalization formula for the arithmetic genus of a reduced proper curve; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-trf-normalization-singular-skyscraper: the existing theorem gives a global singular-support sheaf description and the local quotient data only at nonsmooth support points; the new local task treats every closed point including smooth ones, identifies finite k-dimension with length, gives finite positive geometric fibre and its structural residues, and supplies the complete local normalization data.

lem-trf-curve-delta-completion-data vs lem-trf-ordinary-point-delta-branches: the existing parent is the full branch–delta inequality and ordinary-point criterion, whereas this new statement isolates an independent input and asserts neither the inequality nor the equality characterization.

lem-trf-curve-delta-completion-data vs lem-trf-curve-normalization-completion: the existing algebra theorem gives reducedness and integral closure after tensoring completion; it gives no geometric fibre, structural residue fields, finite-dimensional defect comparison or smooth-point assertion.

lem-trf-curve-delta-completion-data vs lem-trf-nodal-contraction-euler-defect: the existing statement concerns Euler defect of contracting a nodal subcurve to a smooth point; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-trf-nodal-curve-normalization-euler: the existing statement concerns Euler characteristic of a nodal curve from its normalization; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-trf-nodal-contraction-normalization-branches: the existing statement concerns Normalization branches at a nodal contraction boundary; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-trf-nodal-normalization-quotient: the existing statement concerns Normalization quotient at split nodes; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-sfb-nodal-local-tangent-normalization: the existing statement concerns The tangent Proj of a geometric node is its quadratic normalization residue algebra; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-sfb-section-ideal-proj-expansion: the existing statement concerns Expansion from the dual ideal of an arbitrary section; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-sfb-unpointed-stable-coarse-projective: the existing statement concerns Projectivity of the unpointed stable coarse moduli scheme; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-sfb-marked-nodal-infinitesimal-fields: the existing statement concerns Infinitesimal marked automorphisms and normalized vector fields; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-curve-delta-completion-data vs lem-per-normalization-completion-base-change: the existing statement concerns Normalization commutes with completion away from the special fibre; it does not assert the local finite-type curve data, structural fibre residues and k-linear defect-completion comparison at every closed point.

lem-trf-normalization-pair-ring-invariance vs lem-real-henselian-residue-galois-action: the existing statement concerns Equivariant reduction of algebraic constants over a henselian local ring; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-trf-normalization-completed-product-comparison: the existing statement concerns Recover normalization by intersection with normalized completed branches; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-trf-normalization-completed-branch-lift: the existing statement concerns A closed normalization point lifts to a completed branch; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs def-trf-conductor-cokernel: the existing statement concerns Normalization cokernel sheaf; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-trf-ordinary-point-delta-branches: the existing parent is the full branch–delta inequality and ordinary-point criterion, whereas this new statement isolates an independent input and asserts neither the inequality nor the equality characterization.

lem-trf-normalization-pair-ring-invariance vs def-trf-ordinary-multiple-point: the existing statement concerns Ordinary multiple points and their coordinate-axes algebras; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-trf-infinite-product-integral: the existing statement concerns Products of integral morphisms are integral; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-trf-integral-extension-noetherian-spectrum: the existing statement concerns Integral closure of a Noetherian domain in a finite fraction-field extension has Noetherian spectrum; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-trf-monomial-integrality: the existing statement concerns Integrality criterion for a monomial; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-trf-almost-finite-residue-field-degree: the existing statement concerns Finite residue-field degrees in almost finite integral extensions; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-per-complete-dvr-finite-normalization: the existing statement concerns Finite normalization of a complete discrete valuation ring; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs def-weil-pbc-integral-closure: the existing statement concerns Integral elements and integral closure; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalization-pair-ring-invariance vs lem-exc-weakly-etale-normalization-tensor: the existing statement concerns Normalization tensor decomposition for a local weakly etale map; it does not assert extension of arbitrary varying-base ring isomorphisms to normalized pairs together with scalar-independent branch count and quotient length/dimension invariance.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-stacks-nodal-closed-subcurve: the existing statement concerns Stacks lemma for a reduced closed subcurve of a nodal curve, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-bennett-normal-flat-numerical-criterion: the existing statement concerns Bennett numerical criterion for normal flatness along a regular prime, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-relative-cohen-flat-presentation: the existing statement concerns Compatible coefficient-field presentations for a flat local map with regular closed fibre, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-reduced-curve-normalization-genus: the existing statement concerns Normalization formula for the arithmetic genus of a reduced proper curve, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-normalization-singular-skyscraper: the existing statement concerns Normalization quotient is supported at singular points, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-ordinary-point-delta-branches: the existing parent is the full branch–delta inequality and ordinary-point criterion, whereas this new statement isolates an independent input and asserts neither the inequality nor the equality characterization.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-curve-normalization-completion: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-nodal-contraction-euler-defect: the existing statement concerns Euler defect of contracting a nodal subcurve to a smooth point, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-nodal-curve-normalization-euler: the existing statement concerns Euler characteristic of a nodal curve from its normalization, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-nodal-contraction-normalization-branches: the existing statement concerns Normalization branches at a nodal contraction boundary, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-relative-nodal-point-pinching: the existing statement concerns Finite smooth-point pinching on curves proper over a reference scheme, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-regular-complete-coefficient-coordinates: the existing coefficient-field theorem is an input for each already known complete regular factor; it does not identify the actual geometric normalization fibre, construct its completed product, or compare the structural residue maps from H.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-nodal-normalization-quotient: the existing statement concerns Normalization quotient at split nodes, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-taylor-normal-cone-splitting: the existing statement concerns Associated graded comparison for the local Taylor map, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-trf-generic-monotone-diagram: the existing statement concerns Generic monotone diagram and regular vertex generators, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-sfb-finite-formal-quotient-pullback: the existing statement concerns Finite representable pullbacks of a formal quotient chart, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-sfb-dm-finite-normalization-charts: the existing statement concerns Finite normalization of smooth Deligne--Mumford stacks and its charts, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-sfb-nodal-local-tangent-normalization: the existing statement concerns The tangent Proj of a geometric node is its quadratic normalization residue algebra, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-sfb-section-ideal-proj-expansion: the existing statement concerns Expansion from the dual ideal of an arbitrary section, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-sfb-unpointed-stable-coarse-projective: the existing statement concerns Projectivity of the unpointed stable coarse moduli scheme, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-sfb-marked-nodal-infinitesimal-fields: the existing statement concerns Infinitesimal marked automorphisms and normalized vector fields, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-per-inseparable-surface-differential-data: the existing statement concerns Finite differential coordinates for a prime-degree inseparable surface cover, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-per-prime-field-complete-coordinate-model: the existing statement concerns Cohen coordinate completion of an equicharacteristic regular local ring, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-per-gabber-partial-algebraization: the existing statement concerns Partial algebraization of a complete normal strictly local scheme, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-per-equivariant-marked-cylinder-algebraization: the existing statement concerns Marked invariant algebras descend to a polynomial cylinder, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-per-henselian-normal-completion-preparation: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-per-prime-field-punctual-purity: the existing statement concerns Punctual cohomological purity over a prime field, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-per-normalization-completion-base-change: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-per-normal-surface-cover-completed-degree: the existing statement concerns Normalization covers of regular surfaces and their completed local degrees, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-at-quasi-finite-prime: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-finite-quotient-data: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-localized-algebra-product-surjective: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs new-lem-weil-pbc-finite-model-formal-fiber-derivation-extension: the existing statement concerns Extending finite-model derivations to the generic formal fibre, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-tensor-local-maps-injective: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-local-tensor-quotient-power-bound: the existing statement concerns Uniform local maximal-ideal power bound, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-tensor-local-maps-surjective: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-another-helper-g-ring: the existing statement concerns Formal fibres of A[x] over nonzero primes above (0), A complete local domain of characteristic p, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs new-completion-finite-extension-tensor-bijective: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-localized-finite-quotient-charts: the existing statement concerns Canonical local charts of a positive finite-algebra quotient, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-another-helper-g-ring-noetherian-component: the existing statement concerns Noetherian component of polynomial formal fibre, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs new-completion-finite-extension-tensor-map: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-local-tensor-quotient-component-map: the existing statement concerns Injective component map for tensor quotients, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-localized-algebra-finite-quotients: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-finite-extension-tensor: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-finite-extension: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-finite-over-complete-local-product: the existing statement concerns Finite algebras over a complete Noetherian local ring are products of complete local rings, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-finite-extension-decomposition: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-another-helper-g-ring-geometric-component: the existing statement concerns Geometric component of polynomial formal fibre, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-tensor-quotient-separated: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-local-nagata-domain-analytically-unramified: the existing statement concerns A Noetherian local Nagata domain has reduced completion, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-helper-g-ring-char-p: the existing statement concerns Formal fibres over the generic point of k[[x]][y] in characteristic p are geometrically regular, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-completion-finite-quotient: the existing finite-algebra completion result is an input; it does not prove that these actual normalized curve factors are DVRs with the given structural coefficient field and power-series coordinates with identical residues.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-local-tensor-quotient-base-ideal-detection: the existing statement concerns Tensor quotient detection modulo extended base-ideal powers, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

lem-trf-normalized-curve-branch-coordinates vs lem-weil-pbc-local-tensor-quotient-detection: the existing statement concerns Finite quotient detection by sufficiently deep local reductions, not the H-compatible product of actual normalized curve branch completions with their structural k-coordinates.

## Unfinished work

No repair point remains intentionally unhandled. The four new proofs are intentionally unsplit tasks for parallel workers, exactly as the return requires. The parent assembly is complete conditional on those statements and existing cited statements. Delivery validation is recorded after the required dry run.

## Full retained argument from the returned head

The following is the old 8831-character proof, kept verbatim (with its dependency lists) as task-level proof material for the four new workers. These are not proof steps in the new unsplit node files.

### Returned step 1

Work on an affine neighbourhood of $x$; restriction of componentwise normalization is normalization of that neighbourhood. The normalization theorem makes $\nu$ finite and surjective. The finite-fibres theorem therefore gives $1\le b<\infty$. A point $y_i$ above $x$ is closed: on the finite affine inverse image its prime contains the ideal of the fibre, and the corresponding quotient of the finite-dimensional $k$-algebra of the fibre is a finite-dimensional domain, hence a field (multiplication by a nonzero element is injective, hence surjective). The closed-point residue-field theorem gives $\kappa(y_i)=k$ through the structural map. Put $A=\mathcal O_{X,x}$, $B=(\nu_*\mathcal O_{\widetilde X})_x$ and $M=B/A$. The finite-type Noetherianity theorem makes $A$ Noetherian. It is reduced, essentially of finite type over $k$, and has dimension one: a component through $x$ supplies a generic-point-to-$x$ chain, and no longer chain exists on a pure one-dimensional scheme.

Uses: lem-weil-pbc-reduced-algebraic-normalization-field-change, lem-weil-pbc-finite-closed-map-finite-fibres, def-weil-finite-integral-morphism, lem-weil-pbc-closed-point-residue-field-base, lem-weil-pbc-finite-type-over-noetherian

### Returned step 2

If $x$ is nonsmooth, the normalization-quotient theorem identifies $B$ with the integral closure of $A$ in its total ring of fractions and makes $M$ a finite-length $A$-module. If $x$ is smooth, the regularity/smoothness criterion applies to the finite-type affine chart with residue field $k$, hence $A$ is regular. Since $\dim A=1$, the regular/normal equivalence makes $A$ a normal domain. The normalization theorem's isomorphism over its open normal locus then gives $B=A$ and $M=0$. Thus in both cases $B$ is the integral closure of $A$ in its total ring of fractions and $M$ has finite length.

Uses: lem-trf-normalization-singular-skyscraper, lem-weil-pbc-regular-local-separable-residue-smooth, lem-weil-pbc-regular-local-dim-one-iff-normal, lem-weil-pbc-reduced-algebraic-normalization-field-change

### Returned step 3

The finite-length filtration theorem gives a finite filtration of $M$ with simple quotients. Each simple $A$-module is $k$: choose a nonzero element, whose cyclic submodule is the whole simple module; the resulting surjection from $A$ has maximal kernel, necessarily $\mathfrak m_A$. Adding dimensions along the filtration proves $\delta=\dim_k M<\infty$. Put $H=\widehat A$ and $C=\widehat B$, where $B$ is completed for $\mathfrak m_AB$. The local-curve normalization/completion theorem identifies $C=B\otimes_AH$ with the integral closure of the reduced one-dimensional ring $H$ in its total ring of fractions. For nonsmooth $x$, the normalization-quotient theorem gives the natural $k$-linear isomorphism $M\cong C/H$; its map is $A$-linear, hence respects the structural $k$-action. For smooth $x$, $B=A$, so $C=H$ and the same comparison is the zero-module isomorphism. Consequently $\delta=\dim_k(C/H)$.

Uses: lem-weil-pbc-finite-length-module-simple-filtration, lem-trf-curve-normalization-completion, lem-weil-pbc-completion-finite-extension, lem-trf-normalization-singular-skyscraper

### Returned step 4

The finite-algebra completion theorem, applied to the finite $A$-algebra $B$ at $\mathfrak m_A$, gives $C\cong\prod_{i=1}^b R_i$ with $R_i=\widehat{\mathcal O}_{\widetilde X,y_i}$, respecting the maps from $H$ and $B$. Each normalized irreducible component is smooth over the perfect field $k$, by the normalization-properties theorem. Choose an affine open neighbourhood of $y_i$ in that integral component; it is a smooth separated connected curve of dimension one, so the smooth-connected-curve local-ring theorem says $\mathcal O_{\widetilde X,y_i}$ is a DVR. The DVR-completion theorem makes $R_i$ a complete DVR. The local-completion residue-field theorem and Step 1 identify its residue field with $k$, with the given $k$-algebra structure. The map $H\to R_i$ is local and induces the identity on this residue field, since it is the completion of the local structural stalk map.

Uses: lem-weil-pbc-completion-finite-extension, lem-sc-normalization-properties, lem-sc-smooth-connected-curve-local-rings, lem-weil-pbc-completion-of-dvr-is-dvr, lem-weil-pbc-local-completion-local-ring

### Returned step 5

Choose a uniformizer $t_i$ of $R_i$. The local-completion residue-field theorem says the maximal ideal of $R_i$ is $\mathfrak m_{y_i}R_i$, which is $t_iR_i$ since $R_i$ is a DVR; the completion-modulo-ideal theorem makes $R_i$ complete for $\mathfrak m_{y_i}R_i=t_iR_i$. The continuous power-series evaluation theorem gives a $k$-algebra map $k[[T]]\to R_i$ sending $T$ to $t_i$. It is bijective by the following direct expansion. For $r\in R_i$, successively take its residue $a_0\in k$, divide $r-a_0$ by $t_i$, take the next residue $a_1$, and continue. Completeness gives $r=\sum_{n\ge0}a_nt_i^n$. Uniqueness follows because a nonzero series with first nonzero coefficient $a_N$ evaluates to $t_i^N$ times an element with nonzero residue; the latter is a unit and $R_i$ is a domain. Identify $C$ with $D=\prod_{i=1}^b k[[t_i]]$ by these maps; its coordinate residue maps are constant coefficients.

Uses: lem-weil-pbc-power-series-adic-evaluation, lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-mod-ideal

### Returned step 6

Let $\rho:D\to k^b$ take constant coefficients and let $\Delta k\subset k^b$ be the diagonal. By Step 4, $\rho(H)=\Delta k$: containment follows from the local residue maps, and equality from the diagonal constants in the $k$-algebra $H$. Thus, for $P=\rho^{-1}(\Delta k)$, the induced map $D/H\to k^b/\Delta k$ is surjective with kernel $P/H$. Since $\dim_k(D/H)=\delta$, this gives $\delta\ge b-1$, with equality exactly when $P/H=0$, that is $H=P$. Here $\dim_k(k^b/\Delta k)=b-1$ because $b\ge1$.

Uses: 

### Returned step 7

The ring $P$ is explicitly the coordinate-axes ring $R_b=k[[T_1,\ldots,T_b]]/(T_iT_j\mid i\ne j)$. Indeed evaluate a series on each separate coordinate axis. Its images have the same constant coefficient. Conversely a tuple $(c+t_if_i(t_i))_i$ is the image of $c+\sum_iT_if_i(T_i)$. The kernel consists exactly of the series having zero constant coefficient and zero coefficients on all monomials supported on a single variable. Every remaining monomial is divisible by $T_iT_j$ for some $i<j$. Assign each such monomial to its first two positive indices; grouping into the finitely many pairs $(i,j)$ writes the entire series as $\sum_{i<j}T_iT_jg_{ij}$, proving ideal membership even for infinite series. For $b=1$ the kernel is zero. Hence $H=P$ implies $H\cong R_b$.

Uses: 

### Returned step 8

For the converse, compute the normalization of the concrete subring $P\subset D$ from Step 7. The coordinate idempotents $e_1,\ldots,e_b$ generate $D$ as a $P$-module: a tuple equals its tuple of constants plus an element of $P$, and $1=\sum_ie_i$. Hence $D$ is integral over $P$ by the finite-algebra integrality theorem. Put $s=(t_1,\ldots,t_b)\in P$. It is a non-zero-divisor, $sD\subset P$, and $P[1/s]=D[1/s]=\prod_i k((t_i))$: every nonzero one-variable series is $t_i^n$ times a unit. A non-zero-divisor of $P$ has every coordinate nonzero (otherwise it annihilates the nonzero tuple supported in that coordinate with entry $t_i$). Therefore this product of fields is precisely $Q(P)$. Each $k[[t_i]]$ is integrally closed in its fraction field by the power-series normal-domain theorem applied to the field $k$. Projecting a monic equation shows $D$ is integrally closed in $Q(P)$. Since $D$ is integral over $P$, and every element integral over $P$ is also integral over $D$, the integral closure of $P$ is exactly $D$. Moreover $D/P\cong k^b/\Delta k$ by $\rho$.

Uses: lem-weil-pbc-finite-algebra-is-integral, lem-weil-pbc-power-series-normal-domain

### Returned step 9

If $H\cong R_b$, Step 7 identifies this ring with $P$. A ring isomorphism preserves non-zero-divisors and monic equations, so extends to the total fraction rings and identifies their integral closures. Steps 3 and 8 therefore identify the pair $(C,H)$, as $k$-algebras, with $(D,P)$. It follows that $\delta=\dim_k(C/H)=\dim_k(D/P)=b-1$. Together with Steps 6--7 this proves both directions of the claimed equality criterion.

Uses: 

### Returned step 10

When $x$ is smooth, Step 2 gives $M=0$, hence $\delta=0$; the inequality and $b\ge1$ force $b=1$, and the equality criterion gives $H\cong k[[T]]$. Conversely an ordinary one-fold point has this completed ring. A one-variable power-series ring is regular of dimension one by the power-series regularity theorem; regularity descends to $A$ by the completion-regularity theorem. On an affine finite-type chart with residue field $k$, the regularity/smoothness criterion now makes $x$ smooth. Thus ordinary one-fold points are exactly smooth points, and all have $\delta=0$.

Uses: lem-weil-pbc-power-series-field-cohen-regular-complete, lem-weil-pbc-completion-regular-local, lem-weil-pbc-regular-local-separable-residue-smooth

### Returned step 11

The completed-geometric-local-ring definition of a node, stated in the nodal-point criterion, is here a ring isomorphism $\varphi:H\cong k[[u,v]]/(uv)=R_2$, because $k$ is already algebraically closed. Its normalization has exactly two local factors by Step 8. Step 4 identifies the normalization of $H$ with a product of $b$ local domains; the number of factors is intrinsic, since their coordinate idempotents are exactly the nonzero idempotents which cannot be written as a sum of two nonzero orthogonal idempotents. As in Step 9 (which uses only ring structure), $\varphi$ carries $C$ onto $D$; so a node has $b=2$. Moreover $\varphi$ induces a bijection of $H$-submodules of $C/H$ with $P$-submodules of $D/P\cong k^2/\Delta k$, which is one-dimensional over the residue field $k$ of $P$, hence simple. So $C/H$ is a simple $H$-module; as the residue field of $H$ is $k$ via the structure map, $\delta=\dim_k(C/H)=1=b-1$, and the equality criterion of Steps 6--7 gives a $k$-algebra isomorphism $H\cong R_2$: a node is an ordinary two-fold point. Conversely a $k$-algebra isomorphism $H\cong R_2$ is in particular a ring isomorphism, so an ordinary two-fold point is a node by that definition, with $\delta=b-1=1$.

Uses: lem-trf-nodal-point-local-criterion

