# Stage-1 report: lem-sfb-simple-chamber-fold-affine-step

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-simple-chamber-fold-affine-step.json`: statement, split; unchanged statement and statement dependencies. Complete eight-step proof by shifted-coordinate substitutions, coefficient comparisons, sign cases, and integer division. No exact Mathlib match.
- `citations.json`: the sole proof citation, step 1 to def-weil-pbc-free-module, with a verbatim sentence from its statement.
- `searches.jsonl`: actual searches logged by msearch.py. The item's inherited searches remain intact, and the searches run by Q125 are appended to its mathlib_searches.
- `check_cases.py`: finite arithmetic checks of the explicit paths, supplementary to the written proof.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. Every argument is made in the item; there is no hidden statement-only node containing its conclusion. No Lean was written or compiled, and no repository or launcher file was written.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint id and for chamber folding, strong linkage, and affine reflection. There was no matching project declaration, so no attachment is claimed. Ordinary root-chain and root-base declarations in Mathlib do not assert this affine-dot folding property.

## Wanted sources

WANTED: Andersen, *The strong linkage principle*, J. Reine Angew. Math. 315 (1980), 53–59, Definition 1 and Lemma 1, printed pp.54–55, for lem-sfb-simple-chamber-fold-affine-step. The inherited path `literature/andersen-strong-linkage-principle-1980.pdf` does not exist in this read clone. An attempt to open the GDZ scan PPN243919689_0315 at image 58 through the web tool failed as inaccessible. I did not read that scan and do not attribute my calculation to a proof read there. No missing source was downloaded. The proof is explicitly marked `proof_origin.by = agent`.

## Earlier material and corrections

The live item was unsplit with an empty proof, and the sandbox contained no item or report. I copied the current item and retained its statement, source, inherited searches, provenance and blueprint chain. No repair note exists. The parent lem-sfb-affine-reflection-dominant-descent uses exactly this local edge assertion in step 6, so I have preserved all its hypotheses and conclusions, including the bound of two edges and the absence of primality or irreducibility assumptions.

The parent review's suggested rank-one construction is valid, but requires the following explicit checks now written in steps 6–7. If a > 2np and n >= 1, divide a = hp+r with 0 <= r < p. The intermediate point z=x-r alpha is reached at level h, and the final point x-np alpha at level h-n. Here h >= 2n, both levels are nonnegative, and the two lowering coefficients are r and np-r. In particular, simply trying to join x directly to its folded endpoint would incorrectly require a to be divisible by p. The two-edge proof avoids that extra hypothesis.

The nearest imported blueprint ancestor is null, exactly as `tools/blueprint_refs.py ancestor` reports. I retained the inherited null/via/place fields and made the local proof place explicit in split_report. The latest blueprint at `literature/blueprint/latest/` currently points to the 2026-10-24 snapshot (ef6f9619fdbffa59e88528fb56483d76c70258c8). I read its `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially proof (3), and the existing chapter/unit records. This is the inherited representation-theoretic prerequisite below that route, not a revision of the chapter or unit. Searches of the whole blueprint for chamber, affine reflection, and strong linkage found no matching imported node. Full-DAG searches locate this item and its parent, not another local edge-folding theorem. I introduce no nodes, so no same-tag duplicate pairs arise.

## Not duplicates

No new nodes: no new/existing node pairs require a distinction. The parent dominant-descent theorem uses chamber folding, but is not cited here and would create a cycle; its argument and review are only historical material.

## Review by Q125

I read coord/delivery-errors.md B–E in full (both copies in that file), the stage-1 brief and stage document, GOAL.md, SETUP.md's three levels, the chapter/unit records, the current item and its parent, the latest blueprint direct-image proof, and the complete statement of def-weil-pbc-free-module. I could not read Andersen because the local PDF is absent and the online scan failed; this is disclosed above, with the agent-written proof designation. There are no new-node sources to inspect. The source of the definition cited in step 1 is its existing Mathlib definition leaf, whose statement explicitly identifies a module with the direct sum on its basis. This is exactly what step 1 uses; the quote in citations.json is copied verbatim from that statement, not from its proof or metadata.

Step 1 changes coordinates by the already specified rho, writes the affine map explicitly, and obtains k >= 0 by uniqueness of the simple-root coordinates. The only external notion it invokes is the free-module definition: coordinates in its basis make the rationalization map injective. A positive nonzero root has at least one positive coefficient, so multiplying its coefficients by k detects the sign of k. The case k=0 is included.

Step 2 proves, rather than assumes as a standard Weyl-group lemma, that a simple reflection preserves the positivity of a different positive root. Reducedness rules out a positive root supported only at alpha unless it equals alpha. A positive coefficient away from alpha survives the reflection; the sign dichotomy imposed in the hypotheses forces all other coefficients of the reflected root to be nonnegative. The reflection is involutive because c_alpha(alpha)=2. These are short consequences of the explicit hypotheses, not uses of another root-system theorem.

Step 3 substitutes the given covariance c_(s_alpha beta)=c_beta composed with s_alpha and the involution identity. This establishes the precise conjugated edge, with its original nonnegative level n and its original lowering coefficient k. No unproved invariance of the dominance order under a simple reflection is invoked.

Steps 4–5 list all four signs of the two alpha pairings when beta differs from alpha. Each displayed path has its own edge formula: either the original edge, the conjugated edge of step 3, or a level-zero alpha edge with coefficient -a or a as appropriate. A pairing equal to zero goes into the nonnegative branch. The positivity of gamma is already proved in step 2. No additional cited statements are used in these steps.

Step 6 treats the excluded root beta=alpha. Lowering gives a>=np>=0, so the starting endpoint is already folded. If the final pairing b=-a+2np is nonnegative the original edge suffices. If b<0, direct expansion gives the folded endpoint x-np alpha; for n=0 it equals x. For n>=1, ordinary division by positive p supplies the quotient and remainder, and the displayed contradiction proves h>=2n. Step 7 checks both integer levels and both lowering coefficients and computes both endpoints. Thus no unmentioned divisibility, prime-characteristic, or irreducibility condition enters the calculation. The individual substitutions and inequalities are elementary; extracting a new lemma for one case would just repeat a clause of this item. All eight proof steps are shorter than 2000 characters.

Step 8 translates back and removes stationary edges, so the original dot-action formula, path direction, endpoints and bound m<=2 are all retained. An empty root/base system is vacuous because the conclusion quantifies over alpha in Delta. Additional central lattice directions cause no difficulty: none of the formulas require the roots to span X. All proof dependencies are the union of the uses lists. The only proof citation occurs in step 1; steps 2–8 use explicit hypotheses and computations established in earlier steps, with no outside theorem. The definition leaf is a notion, so no off-unit theorem use needs a tool declaration.

The supplementary Python check enumerates all constructed paths for A1, A2, B2, G2 and A1 x A1 on simple-root coordinates in [-6,6], p=1 through 7, and every allowed nonnegative level n. It also tests A1 on the weight lattice, with root 2 and coroot the identity, to include odd pairings. All 55,969 folded edges pass: each generated edge has a positive root, a nonnegative integer level and lowering coefficient, and the computed path has the required endpoint and length at most two. This includes composite p, points on the wall, equality edges, zero remainders, both crossing signs, and reducible systems. For example a=7,p=3,n=1 uses h=2,r=1 and two levels 2 and 1, whereas n=0 gives the empty path after folding. This finite check supplements the proof, which handles arbitrary ranks, rho, p and lattice points.

The B–E checklist therefore raises no missing hypothesis, wrong-object identification, uncited non-elementary input, false standard-step shortcut, circular use, duplicate node, or silent source/statement change. The mathematics is fully written, rather than deferred to a source citation or to a new copy of the assertion. No SGA source is used.

## Unfinished work

No mathematical step is left unfinished. The missing Andersen document is a literature request, not a proof dependency. Required server dry run and push are performed after this report is written; their final results will be recorded below.

## Delivery validation

The required `deliver.py Q125 lem-sfb-simple-chamber-fold-affine-step --no-push` exited 0 and printed `OK (not pushed)` at 0302c3b921c, with server preflight passed. A final dry run covers this report addition, and direct delivery follows its successful exit. The pushed commit is reported by the delivery command and the worker's final answer.
