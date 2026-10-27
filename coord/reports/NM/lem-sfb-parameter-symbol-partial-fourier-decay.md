# Stage-1 delivery: lem-sfb-parameter-symbol-partial-fourier-decay

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-parameter-symbol-partial-fourier-decay.json — existing statement, split into six argument steps; not a Mathlib leaf as a whole.
- citations.json — eleven verbatim citation entries for the six steps.
- report.md — this report. No new DAG nodes; no new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact item id, partial Fourier, and parameter-symbol terminology. No project declaration states this item. The upstream source is read-only and no Lean or compiler was used.

## Sources wanted

WANTED: literature/demailly-hodge-ams.pdf, Part I §3.B (3.4)–(3.5) and Proposition 3.7, printed pp.12–13, for the item's inherited source.
WANTED: Demailly, Differential and pseudodifferential operators on manifolds (literature/demailly-differential-pseudodifferential-operators.pdf), §2 Fourier identities, printed p.3, §3 (3.11), printed p.9, and the estimates following (3.15), printed p.11, for this item.

Neither PDF is present locally. I read the supplemental course online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf, especially the Fourier identities, the compact-spatial estimate (3.11), and the mixed differentiation after (3.15). The course explains the analytic method; the full statement with external parameters, matrix ranks possibly zero, eta derivatives, and a finite sum of input seminorms is the agent's extension. The proof is therefore explicitly marked proof_origin.by=agent, with the missing-local-source condition recorded rather than represented as a local document proof. No download was made and no SGA source was used.

## Findings and corrections

The sandbox initially contained no item or report. There is no released stage-1 repair note for the item. Its live state is unsplit. Its statement is correct and was kept verbatim, as were the inherited provenance, pointers, search records and other metadata. The proof and proof dependencies were empty. The new proof supplies the joint-smoothness argument, the mixed derivative formula, the repeated integration-by-parts identity, and the explicit uniform constant.

The newest blueprint unit was read from literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md, as were the chapter and unit JSON records and the three-level route requirements. This is an auxiliary analytic argument below the inherited amplitude-reduction/elliptic-parametrix chain, not a replacement for a chapter or unit step. Whole-DAG and whole-blueprint searches for Fourier, integration by parts and differentiation under the integral found existing generic tools and no duplicate of the entire item. tools/blueprint_refs.py ancestor returns inherited from.node=None. I preserved this upstream provenance, its detailed from.place and via chain rather than replacing it with an invented blueprint id. The tools decide whether that inherited state is admissible.

The existing Mathlib-search records were retained. The new searches were run with msearch.py and logged exactly in searches.jsonl. I read the results of both semantic phrasings, Loogle and the source grep. I read FourierTransformDeriv.lean:507–528 and :632ff, ParametricIntegral.lean:210–218, and LineDeriv/IntegrationByParts.lean:226–237. The fixed-function Fourier smoothness and decay estimates and the continuous Schwartz transform are useful inputs, but the entire jointly parameterized symbol-seminorm statement is not a one-line specialization of them. The existing dominated-integral derivative and scalar integration-by-parts nodes already represent the relevant general Mathlib facts.

## Not duplicates

No new nodes were created. I reused lem-sfb-dominated-integral-frechet-derivative, lem-sfb-scalar-integrable-integration-by-parts, lem-sfb-continuous-compact-support-integrable, lem-sfb-continuous-on-compact-integrable and lem-sfb-vector-integral-majorant-linearity. The existing bilinear Fourier moment regularity and Schwartz Fourier coordinate rules concern a fixed function or Schwartz maps; they do not provide the complete joint-parameter assertion and finite symbol-seminorm dependence of this item.

## Review by NM

I checked B–E of delivery-errors against the node files and the source. All five cited nodes are existing Mathlib leaves in the same unit. No off-unit proof tool declaration is needed, and no elementary observation or clause of the item has become a new node. The statement introduces every parameter and the explicit symbol estimates; the proof does not add assumptions or change the frequency normalization.

Step 1 uses precisely the compact-support integrability conclusion of lem-sfb-continuous-compact-support-integrable. It applies to scalar entries of the smooth integrand and its derivatives, whose supports lie in the closed compact L_z. Matrix integrability then follows by the finite coordinate sum and integral linearity from lem-sfb-vector-integral-majorant-linearity. This also makes the empty rank case explicit. Vanishing outside L_x follows directly from the zero integrand.

Step 2 uses the same entrywise integrability statement and lem-sfb-continuous-on-compact-integrable with h=1 on L_z to make the constant-on-support majorants integrable. I read the entire statement of lem-sfb-dominated-integral-frechet-derivative: it permits real Banach codomains, including the finite-dimensional spaces of multilinear maps used here; it requires an integrable derivative bound simultaneously on a whole neighborhood, not merely pointwise bounds with an exceptional set depending on the parameter. The symbol bounds and bounded z and xi give a pointwise common majorant on the whole chosen ball. Smoothness supplies all measurability and Fréchet-derivative hypotheses. The resulting derivative identity holds at every point and at every order. Step 3 explicitly gives the induction from those identities to smoothness, and uses only finite integral linearity to evaluate on coordinate vectors and obtain the displayed mixed formula. No unproved generic smooth-family integral theorem is hidden.

Step 4 uses exactly the identity in lem-sfb-scalar-integrable-integration-by-parts. With the exponential as its f and a matrix entry as its g, both differentiability hypotheses hold globally and each of its three product integrability hypotheses follows from the compact-support integrability node. I checked the signs: the first derivative has multiplier i eta_j, the second has -eta_j squared, so 1-Delta has multiplier 1+|eta| squared. Each repeated application still has compact spatial support. The vector linearity node permits the finite Laplacian sum and recombination into a matrix identity.

Step 5 is an explicit finite Leibniz expansion, not a black-box symbol lemma. It uses the compact-set integrability node only to obtain finite v_z and the vector majorant node exactly for its norm-of-integral bound. Every term has z derivative order at most 2N, fixed x derivative alpha and xi derivative beta. Polynomial differentiation changes only the bounded z factor, so the exponent r-|beta| is unchanged. Step 6 is the elementary inequality (1+u)^2 <= 2(1+u^2), followed by choosing N=ceil(L/2). Its displayed constant depends on only finitely many input constants, and hence works uniformly for common-support families.

I tested p=0, q=0, empty L_x, empty L_z, zero b, eta=0, L=0, negative r, and a separated example b(x,z,xi)=phi(x)psi(z)a(xi) with compactly supported smooth phi and psi. No division by volume or by |eta| is used, so zero-volume supports and the origin cause no failure. For a compact set with empty interior a smooth supported function is zero, also consistent with the estimate. The factor (2pi)^(-m) and the -i z multiplier are retained. All citations.json entries are copied verbatim from the actual node statements. Every proof step is shorter than 2000 characters; the non-elementary operations have cited statements, and the induction and finite expansions are written out. No statement dispute or source error was found.

## Unfinished work

None within this stage-1 split. No Lean writing or proof compilation belongs to this task. Delivery validation is performed only through the prescribed server tools.

## Earlier delivery tool failure (resolved on retry)

The prescribed srvcheck.py review_split and deliver.py --no-push were both run and polled to exit, without duplicate deliver.py invocations. They waited roughly 3500 seconds for admission. The review was admitted in server slot 2 and the dry run in slot 11. Both then failed with subprocess.TimeoutExpired: the server SSH execution timed out after 720 seconds, followed by the wrapper's automatic nocheckout.py fallback timing out after 600 seconds. Both processes exited 1 without validation diagnostics. The dry run built candidate commit 6974d41737a236b35a324083a1a40f723b1a56f2 but never printed OK. No push was attempted. That attempt was blocked on infrastructure and was not an accepted delivery. The complete split, report, citations and exact search logs remain in the sandbox for a later retry. Launcher scripts were not modified and no checks were manually run locally.

## Review by NM — resumed attempt, 2026-10-24

I retained the earlier proof, report, citation file and search log and started with the required dry run. It exited 0 and printed OK (not pushed), candidate f814d4eb959, with server preflight passed. The earlier infrastructure timeout did not recur.

I compared the sandbox item with the current read-only repository: the statement, statement dependencies, inherited source and blueprint provenance are unchanged; the live item is still unsplit and has no repair note. I repeated the project-source attachment search for the item id, partial Fourier and parameter-symbol terminology, with no matches. The whole-blueprint Fourier search has only the algebraic Fourier–Deligne material, not this analytic assertion; the DAG already has all five generic tools used here, so no new node is required. I read the current chapter and unit records and newest blueprint unit; this auxiliary input remains below their inherited analytic branch and changes no unit statement or route.

For step 2 I reread ParametricIntegral.lean:210–218 against the existing dominated-integral node, especially the common neighborhood and simultaneous domination quantifiers. For step 4 I reread LineDeriv/IntegrationByParts.lean:226–237 against the scalar integration-by-parts node, including all three integrability assumptions. For steps 1, 2 and 5 I checked LocallyIntegrable.lean:583–594 and :621–626, Bochner/Basic.lean:947–951 and L1Space/Integrable.lean:101–103 against the compact-support, compact-set and majorant leaves. Each cited node is still a Mathlib leaf. The differentiation and repeated Laplacian arguments use exactly these conclusions; the finite coordinate sums and Leibniz expansion require no additional lemma. I verified all eleven quotes against the current cited statements and exact step coverage; the six argument lengths range from 657 to 1191 characters.

I reopened Demailly's supplemental online course, §2 printed p.3 and §3 (3.11) printed p.9 and the mixed estimates after (3.15) printed p.11. Its Fourier convention uses 2π in the exponential; the item's direct integration-by-parts calculation instead consistently keeps its stated exponential and prefactor. The full external-parameter assertion remains an agent proof, with both unavailable local sources explicitly WANTED. Reading the fixed-function FourierTransformDeriv.lean estimates again confirms they do not supply the full joint parameter assertion as a one-line specialization; the logged searches therefore remain applicable and were not repeated.

I rechecked the zero-rank, empty-support and eta=0 cases and the sign of the second derivative in step 4. No correction to the mathematical split was necessary. This report update records the successful retry and retains the previous failure as history. A final dry run follows this report update before the authorized push.
