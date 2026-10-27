# Q145: lem-sfb-negative-symbol-finite-kernel

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-negative-symbol-finite-kernel.json`: statement, split; statement unchanged. Seven proof steps, no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual msearch.py results. `prepare_split.py` is sandbox-only preparation code.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint id, symbol, pseudodifferential, and negative-kernel terminology. The hits concern algebraic symbols and unrelated negative-degree kernels, not this analytic theorem. No project declaration states the item. Read the fixed-frequency Fourier derivative declarations at Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:497–529: they do not assert joint regularity of a position-dependent symbol kernel or identify its localized oscillatory action.

## Literature

WANTED: Demailly, *Differential and pseudodifferential operators on manifolds*, §3 (3.3)–(3.5), (3.8)–(3.9), (3.12), pp.6–10, for lem-sfb-negative-symbol-finite-kernel. The file named in the node's source is absent locally. I read the online primary PDF at https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf, particularly printed pp.6–8 and pp.9–10. The source gives symbol bounds, kernel quantization and the all-order regularizing assertion; the explicit finite-order proof and cutoff error estimate here are agent-written and marked accordingly. Demailly uses exponent 2πi, whereas the item uses exponent i and prefactor (2π)^(-m); the proof retains the item's convention throughout.

The exact analytic tools are existing Mathlib leaves. I read their DAG statements and their cited Mathlib source: JapaneseBracket.lean (integrable inverse bracket), ParametricIntegral.lean:210–218 (dominated Frechet derivative), DominatedConvergence.lean:57–74 (dominated convergence for countably based filters), Integral/Prod.lean:231–235,482–484 (product integrability and integral swap), Bochner/Basic.lean:934–951 and L1Space/Integrable.lean:101–103 (norm domination), and the recorded compact-support integrability and compact-minimum statements. No Stacks tag or SGA source is appropriate to these real analytic lemmas.

## Errors and changes

No statement dispute. Both stmt_deps remain needed: scalars and the symbol/quantization convention. The inherited empty proof is replaced, without changing the item statement. The statement is genuinely stronger than fixed-frequency Fourier smoothness, so it is not a Mathlib leaf despite the near semantic matches.

I read the current latest blueprint chapter and unit, and the current direct-images proof (3); this analytic prerequisite belongs to the inherited lower-level route. The historical inherited ancestry is long and blueprint_refs ancestor returns None. I preserved from.node=null, place and via rather than inventing a blueprint node. Whole-blueprint searches dominated, Fubini, integrable and pseudodifferential returned none; Fourier and kernel searches found algebraic Fourier/derived-category results, not this statement. Whole-DAG statement searches located the reusable analytic leaves. In particular I did not create an inverse-polynomial-weight lemma: `(1+t)^(r+k) ≤ (1+t²)^((r+k)/2)` reduces it directly to the existing `lem-sfb-euclidean-bracket-integrable`.

## Not duplicates

No new nodes. All analytic inputs are existing nodes. Polynomial decay, parameter differentiability, cutoff convergence and the action formula are proved as steps, not restated as new clauses.

## Unfinished work

None for this one-level split. The existing lower nodes retain their current states. No Lean written, compiler run, repository file changed, or agent started.

## Review by Q145

I checked delivery-errors B–E against the actual node statements and source rather than treating imported dependency lists as proof. There are no statement-only children to conceal the item's clauses, no new notation requiring a definition node, no duplicate node and no new Mathlib search to fabricate. The original item and inherited search results are retained; additional item and decay searches were run with msearch.py and their hits read. The cutoff proof uses only spatial derivatives, so it never introduces an unjustified derivative of the frequency cutoff.

Step 1 uses the symbol definition for estimates on the compact x-support, and the compact-minimum lemma on negative absolute values for upper bounds on smooth cutoff derivatives. The compact-minimum statement needs a nonempty compact set; the proof explicitly disposes of empty spatial supports first. Supports are compact subsets of the open chart, so zero extension is locally zero near the chart boundary. I checked that this argument applies to all spatial derivatives, not just the original cutoff values.

Step 2 uses the definition's x-derivative estimates with frequency derivative zero. The displayed Leibniz sum includes derivatives of both cutoffs, the symbol and both phase variables; each phase derivative contributes a factor of ξ with the correct sign. The exponent is at most r+k, and r+k is negative. Full Frechet derivative bounds follow from finite coordinate sums in the finite-dimensional matrix/multilinear spaces. This is an elementary calculation, not a hidden Fourier regularity lemma.

Step 3 cites the bracket-integrability node with s=-(r+k)/2>m/2, exactly its hypothesis. The vector-majorant node supplies absolute integrability and bounds, not merely a definition of integrability. The convergence node supplies continuity for arbitrary convergent parameter sequences; Euclidean spaces and real atTop have countably based filters. Its measurable and dominating hypotheses hold pointwise, hence almost everywhere. For the derivative node the bound is uniform on a full parameter neighbourhood, all frequency sections are measurable, and the base section is integrable. The induction begins with the integral itself, takes derivatives only for j<k, and uses continuity of every resulting derivative. It still works for k=0 with no differentiation call.

Step 4 uses compact minimum for the finite cutoff bound, vector-majorant linearity for subtraction and estimates, and dominated convergence with (M+1)w. The cutoff may change sign and need not be between zero and one. Only its boundedness and its value one near zero are used. The same convergence node handles the indicator tail bound. Thus absolute locally uniform convergence and uniform convergence of all claimed cutoff derivatives have an explicit scalar error tending to zero.

Step 5 uses compact-support integrability for the scalar norm of f, treated as a complex function, and vector-majorant integrability for the bound C w(ξ) h(y). The Fubini node actually states both the product integrability criterion and integral-swap identity; Lebesgue measures are sigma-finite and the target is a finite-dimensional real Banach space. I verified integrability before interchanging the integrals. This avoids invoking an unrecorded oscillatory Fubini principle.

Step 6 uses the defining limit after pairing with tests, which the cited definition explicitly states. Uniform kernel convergence bounds the output difference by sup|H_R-H| times the finite integral of ||f||. Pairing with a dual test introduces its finite integral norm, justified by the compact-support node. This proves equality of distributions for the original localized action, including both cutoffs, without treating a definition node as a theorem about kernels.

Step 7 again checks the neighbourhood derivative bound for the parameter integral in y. Its majorant is C_j times the finite integral of w times ||f(y)||. Dominated convergence gives continuity, and the derivative node gives all successive derivatives. Taking real coordinates commutes with finite-dimensional integration; for real f the identity Re(Hf)=(Re H)f is pointwise. The proof does not assert a formula for real parts of a genuinely complex f.

Small cases checked: p=0 or q=0 makes the map zero; k=0 needs only continuity; a=0, empty U and vanishing cutoffs give zero kernels. No assumption that U is bounded or has a smooth boundary is used. The strict threshold is retained: at r=-m-k the derivative majorant has logarithmically divergent radial tail, so that endpoint cannot be admitted by this argument. All seven steps are below 2000 characters, and every non-elementary invocation is a statement-level citation with an exact quotation in citations.json.
