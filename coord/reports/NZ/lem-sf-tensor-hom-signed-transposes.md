# Signed tensor-Hom transposes: stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors/lem-sf-tensor-hom-signed-transposes.json`: split statement; no exact Mathlib match. Eight steps, no new nodes, no new Mathlib leaves.
- `citations.json`: verbatim statement quotations for every step/node citation.
- `searches.jsonl`: actual Mathlib searches made with the mandated command. The existing item's earlier search records are retained.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for projection/shift and tensor-Hom declarations. `AlgebraicGeometry.Etale.commShift_derivedHomRightDerivedLowerShriekIso_app_hom` in `WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean` proves the N-variable shift square for the exchange in its etale coefficient-category setting. `LowerShriekProjectionShift.lean` provides the second-input projection shift. Neither supplies all the present item's clauses, notably the signed contravariant input and integral completion unit, so neither is an attachment for this item. I did not count a partial match or a docstring as a finished proof.

## WANTED

None. The local Stacks sources, Bhatt-Scholze paper and the specified blueprint ancestor suffice for this split.

## Problems found and changes

The imported statement is retained verbatim. Its proof was empty. I supplied the actual five-arrow calculation rather than assuming shift compatibility of a previously constructed exchange. In particular the projection arrow in the Hom chain is precomposition with the inverse projection transformation. Its inverse shift equation follows from the forward one by multiplying by inverse components; its invertibility comes from the hypothesis that the displayed Hom bijections exist on the full domains.

The source is the ancestor `fix-lem-tensor-adjunction`, its statement's shift clause and its proof's first Hom chain. I read the master file named by the item. It does not spell out this sign calculation; accordingly the proof is marked agent-written. I read Stacks `sites-cohomology.tex`, section-hom-complexes (0A8X), the tensor-Hom calculation lemma-compose (0A90), lemma-pullback-tensor-product (07A4), equation-projection-formula-map (0B56), and lemma-j-shriek-and-tensor (0GL1), as well as `derived.tex`, lemma-adjoint-is-exact (0A8D). I also read Bhatt-Scholze, PDF pages 22-23: Definition 3.4.10 and Lemmas 3.4.11-12. The categorical and sign refinements are not falsely attributed as literal assertions of those tags.

The chapter/unit records are unchanged. This is an auxiliary for the biduality unit, not its key statement; no unit realization is modified. Its ancestor is `fix-lem-tensor-adjunction`, and blueprint searches for signed transpositions, Hom complexes, completed tensor, projection and shifts produced no exact duplicate. No node was created.

## Not duplicates

There are no new-node/existing-node pairs. Existing general statements are cited instead of creating new evaluations, projection-shift clauses or completion-shift clauses. In particular the already present tensor shift descent, Hom shifts, proper mate, open projection, completed tensor shift and reduction/limit shift results are reused.

## Review by NZ

I checked the statement and every step against the relevant node statements, not their proof bodies. The full text of each statement used is copied verbatim into citations.json, so the reviewer can inspect each application with its actual hypotheses.

Step 1 uses the published two-variable derived tensor shift structure, the definition of the Hom differential, and the two unbounded derived Hom shift results. The Hom nodes assert natural isomorphisms rather than an evaluation identity; the step therefore gives the representative formulas and checks their signs. The convention is unsigned extraction in the first tensor variable, and the Koszul factor in the second. Source-Hom comparison has degree-j coefficient (-1)^(r*j); target-Hom comparison is unsigned. The ambient categories are the small ringed-site categories stipulated by the six-functor setting, and there is no boundedness assumption on these elementary model identities.

Step 2 uses the exact uncurrying normalization of `lem-sf-coefficient-tensor-curry-normalization` and the actual signed symmetry formula in `lem-pur-total-tensor-signed-coherence`. The former states compatibility for K-flat P,Q, arbitrary target I and its K-injective replacement: this is precisely the representative computation needed, and does not require the target itself to be K-injective. In the unsigned order L tensor P the source shift produces coefficient (-1)^(r*(k+r)) on both currying routes; returning to the displayed order P tensor L introduces the braiding sign. No claim that global sections of a sheaf tensor are pure tensors is made: the calculation is on the summand generators before sheafification and uses the cited representative comparison. This also avoids mistaking Mathlib's differently normalized Hom-complex shift helper for the whole assertion.

Step 3 uses the uniqueness/existence and counit clauses of `lem-weil-pbc-adjunction-shift-compatibility-unique`, and the actual ordinary/exceptional adjunctions in `fix-prop-adjunctions`. The conditional exceptional admissibility is expressly present in the item. The elementary substitution in eta and epsilon is written out as the two adjunct formulas, so no unstated theorem about exact mates is used. The right shifts are fixed by transposition, as required by the item.

Step 4 checks the precise beta and pi formulas against `def-exchange-projection`. `lem-weil-pbc-pullback-tensor-canonical-shift-unit` states both normalized tensor comparison shift equations, not merely existence of a tensor comparison. The arbitrary-arrow tensor-mate node states the second-input beta/alpha equations, and is applied with c equal to epsilon_E. It does not state a first-input equation; that one is explicitly obtained by substituting the counit shift and naturality of the first tensor shift. Thus neither input's square is inferred from a node that only handles the other input. The generic categorical argument uses no projection invertibility.

Step 5 reads the degreewise exactness assertion of `lem-cbc-proetale-extension-zero`, the canonical open projection statement, and the termwise resolving-model formula in the pullback-composition node. Their finite-coefficient hypotheses match this stage of the proof. The open shift calculation is written out in bidegrees; it is not hidden behind the word canonical. The composition/whiskering node asserts exactly the closure operations used to paste these maps. The finite argument is kept separate from the later integral argument, so a finite-ring lemma is never silently applied to the integral coefficient sheaf.

Step 6 uses the actual quotient/total-limit definition, the existing completed right-tensor shift statement (which includes transitions), the first-variable tensor descent statement, and the signed injective-tower Roos comparison. The latter gives the cone sign and preservation of the actual limit inclusion. The reduction-limit adjunction shift node states compatibility of both unit and counit. All towers use the same positive index set and quotient transitions as those statements. The proof needs neither ordinary exact products on an arbitrary ringed site nor equality detection by finite reduction. The completion unit is checked as the specified quotient augmentation.

Step 7 uses the expression-substitution node only for tensor, pullback, their compositors and their normalized systems, exactly the operations in its statement. It does not claim this node gives a theorem about an arbitrary proper direct image. The proper projection is treated again by its actual adjunction formula; the right-adjoint shift is fixed as in step 3. The item's complete constructible inputs provide the reduction/limit realization, and the displayed Hom-bijection domain hypothesis is maintained at every intermediate object. The integral Hom remains ordinary derived internal Hom into the complete target, as the integral-operation definition explicitly says; the tensor transpose precomposes with the completion unit. The unit shift check prevents an independent or unnormalized completed comparison from entering the argument.

Step 8 is elementary assembly. I listed the N-shift intermediate Hom groups to verify that the final test object is L[-r]; for a source M-shift the test object is L[r], giving A[-r] and B[-r] at the endpoints. Pasting the five commuting squares cancels intermediate vertical bijections and gives the two stated equations on arbitrary test morphisms. This does not use a pre-existing exchange isomorphism's shift property.

I checked the zero complex, r=0, r=1, r=-1, the identity morphism, and the empty-open case. The parity equations use integer exponents, so the same calculation covers all negative shifts. At r=1 and an odd first-factor degree, the second-tensor shift has a minus sign; omitting it would fail the tensor differential equation. The source shift reverses the Hom shift, as required. I also checked that the reused nodes have no dependency path back to this item. Every non-elementary step is below 2000 characters; no hidden standalone lemma is moved to an oversized step. Each imported or pre-existing metadata field is preserved, and no Lean source, compiler, repository file or launcher file was changed.

The off-unit statements are generic tools for normalized tensor, internal Hom, adjunctions, extension by zero and reduction/limit constructions, rather than replacements for the biduality unit's route. Their node ids and reasons are declared in split_report.tool_uses. No new node duplicates a clause of this item, and no new search claim is unlogged. No unfinished mathematical branch remains at this one-level split; the cited unsplit general results remain their own DAG tasks.

## Unfinished work

None for this stage-1 split. Maintainer independent review and the downstream cited tasks remain part of the project process.

The first dry run required a self-contained reference to the displayed Hom-bijection hypothesis in Step 5. I replaced the external-sounding phrase and replaced plain-text arrows in proof steps with TeX arrows before rerunning the dry run.
