# Q63: lem-sf-etale-chart-adjoint-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-etale-chart-adjoint-comparison.json`: statement, split into six proof steps; Mathlib verdict: no match for the ordinary-etale chart statement. The general adjunction Hom equivalence is present, but does not supply the geometric compact-support comparisons.
- `citations.json`: eleven step/node entries, quoting the precise existing statements used.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. `searches.jsonl` contains the searches actually executed for this item; the inherited searches in the original node were preserved. `prepare.py` is a sandbox-only preparation script, not a delivery file.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and the ordinary-etale chart/exceptional-adjoint notions. The tag is absent. The existing `Etale.Derived.UpperShriek` supplies an ambient adjunction, `UpperShriekBaseChange` supplies Cartesian open base change, and `Stability.UpperShriek` supplies a constructibility chart theorem; none states all the Hom-chain clauses of this item with arbitrary K. These are not attachment candidates for this node. No Lean file was written and no compiler was invoked.

## WANTED

None. The item is an agent-written formal expansion of the blueprint's opening/final locality argument, using literature already present.

## Audit of the imported node

The statement is unchanged. In particular H is bounded below, K is arbitrary, and the two Hom targets are not required to be bounded below. The imported node had no proof. Its statement dependencies named only the three large categorical inputs; I added the existing definitions of the scheme and immersion properties and of the ordinary direct image, inverse image and extension by zero that its text uses. The inherited blueprint origin and search records are retained.

The chain uses only ordinary small-etale constant-A module categories. It neither moves to a pro-etale category nor asserts an object isomorphism using restricted Yoneda. Bounded-below Hom detection is a different item of the parent split. Thus there is no statement dispute to repair here.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs. Searches of the whole DAG and `tools/blueprint_refs.py search` for compact-support composition, adjoint locality and Hom comparison found the existing tools used below, not another blueprint statement of this chart comparison. The general composition, locality and closed-support nodes were reused. The generic composition/inversion of natural bijections remains an elementary step rather than a new lemma.

## Review by Q63

I read the chapter record `sec-six-functors-basics`, the unit record `sk-prop-sf-rf-shriek-preservation`, and its current main-20261015 proof file. The opening and final paragraphs are the exact places this item serves. The chapter has two coefficient layers; this item deliberately proves the ordinary-etale comparison required by its parent, without importing a condensed or pro-etale adjunction. I also read Stacks `more-etale.tex`, Tag 0F7J (`lemma-shriek-composition`), its compactification-tower calculation and choice-independence argument, and the statement at Tag 0F7K (`lemma-pseudo-functor`). I read the open extension statement at Tag 03S5 (`proposition-describe-jshriek`) and the closed stalk calculation at Tag 04FX (`lemma-stalk-pushforward-closed-immersion`) in `etale-cohomology.tex`. I read the blueprint source and current DAG statement of `thm-amb-etale-exceptional-adjoint`. No SGA source is used. There are no new-node sources to audit.

For step 1 I opened all six cited nodes. The compact-support definition explicitly computes the chosen candidate as Rr_* Dj_!, so the compactifications (w,id) for an open w and (id,i) for a proper i give precisely the claimed normalizations. `lem-weil-pbc-closed-immersion-proper` explicitly gives properness; `lem-weil-pbc-closed-immersion-finite` explicitly gives finiteness; `lemma-weil-pbc-finite-direct-image-exact` explicitly gives exactness and Ri_*=i_* on D+. The last is stated for abelian sheaves. I therefore wrote out the extension to constant-A module sheaves rather than pretending its statement already says modules: forgetting the action leaves the same direct-image section functor, with the same underlying kernels and cokernels. This proves exactness for modules. `lem-weil-pbc-extension-by-zero-exact` already states exactness for arbitrary constant-ring module sheaves. Cohomology commuting with either exact functor is the kernel/image calculation, and shows that the lower bound of H is retained. `lem-amb-etale-compact-comparisons` gives the choice-independence on D+, so no unbounded comparison is silently used in this normalization.

For step 2 the two cited statements say exactly what is needed: `prop-weil-open-closed-recollement-adjunctions` asserts j_! adjoint to j^* on the ambient ordinary derived categories with finite constant coefficients; `thm-amb-etale-exceptional-adjoint` asserts a right adjoint to Rf_! on ordinary etale A-module derived categories. I use the Hom bijections in their inverse directions. The finiteness of A, Noetherian schemes, and the specified compactifications verify these hypotheses, with no field or invertibility assumption added.

For step 3 I checked the full statement of `lem-amb-etale-compact-comparisons`, not only its title: it provides a natural composition isomorphism on D+ for composable compactifiable separated finite-type maps between Noetherian schemes. The item assumes these conditions for all displayed morphisms and composites, so the pairs (s,f), (i,p), and (pi,v) all qualify. H, i_*H, and the subsequent compact-support outputs are in the indicated D+ domains. The formula for gamma specifies its direction. The induced Hom bijection precomposes by gamma inverse; the inverse precomposes by gamma. Since only the source of this precomposition must be bounded below, K remains arbitrary. I did not take a compositor at f^times K or at p^times v^*K.

For step 4 the same open-adjunction statement supplies the forward Hom bijection for v. For step 5 the exceptional-adjoint theorem applies to both p and i, and normalization is used only at H. The last adjunction is ambient, so no unsupported boundedness hypothesis on p^times v^*K is needed. All these references quote the actual statement clauses in `citations.json`.

Step 6 uses no additional lemma: it explicitly composes the already natural bijections and reverses their order to construct the required inverse. The naturality equation for gamma and associativity of composition give the precomposition/postcomposition squares; the squares for inverse bijections follow by applying their inverses. This is the elementary calculation, not an appeal to a new representability or uniqueness theorem.

I checked delivery-errors B through E against the resulting files. There are no new-node self-containment, search, source-tag or duplicate obligations. Every non-elementary input of each step is cited, and every citation has a verbatim statement quote. No new node restates a clause, and no dependent of this item is used. Each proof step is shorter than 2000 characters. The route still realizes composition and open locality in the specified unit. All off-unit citations are declared as generic tools in `split_report.tool_uses` with their role; the worker does not set accepted `tool_uses`.

The small cases are consistent: for H=0 all Hom sets are singletons; for zero coefficients all categories are zero; empty chart schemes give zero extensions and singletons; identity immersions reduce the normalization to identity functors and the chain to the given adjunctions. Negative lower bounds cause no change, since exact open/closed functors preserve the actual lower bound, and the composition theorem works on all D+. Arbitrarily unbounded K is allowed at every Hom and adjunction step. No noncanonical choice of an object from a mere existence assertion is introduced.

## Unfinished work

None in this stage-1 split. The reused input nodes retain their own proof obligations. Delivery validation is recorded below when completed.

## Validation

The required `deliver.py Q63 lem-sf-etale-chart-adjoint-comparison --no-push` exited successfully: `OK (not pushed)` at temporary commit `22322511355`, with server preflight passed. The direct-delivery brief authorizes this worker to push after the passing dry run; no second-worker handoff is required.
