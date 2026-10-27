# Stage-1 delivery: lem-sfb-ringed-strict-perfect-relative-tensor

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-strict-perfect-relative-tensor.json`: statement, split into nine proof steps; no Mathlib match for the full statement.
- `citations.json`: 25 step/node entries, quoting the cited statements verbatim.
- `searches.jsonl`: actual searches made through the required msearch command. Existing Mathlib search records in the item were retained and the new searches appended.

There are **0 new nodes and 0 new Mathlib leaves**. `prepare.py` is a sandbox-only preparation script, not part of the DAG delivery.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint id and for strict-perfect relative-tensor terminology. I read `AlgebraicGeometry/StrictPerfectRelativeTensorModel.lean`, `StrictPerfectRelativeTensorTermsFlat.lean` and the relative tensor retract-flat source. The scheme declarations use the Zariski open site of a scheme, the inverse image of its base structure sheaf, and relative-flatness hypotheses on affine sections. They do not state the general arbitrary ringed-site assertion here. No attachment is claimed. The item has no Lean audit entry giving a proof of its statement.

## WANTED

None. All proof sources used are present in `literature/stacks-project/`.

## What was wrong or missing

The item was statement-only, with an empty proof. Its statement is unchanged. I added statement dependencies for the localized ringed site, scalar restriction, and the specified K-flat derived tensor construction. Its exact local model, finite-summand description, strict degree bounds, scalar-restricted K-flatness and final tensor comparison are all proved separately in the steps.

The provenance chain already has `blueprint.from.node = null`: `tools/blueprint_refs.py ancestor lem-sfb-ringed-strict-perfect-relative-tensor` prints `None`. I retained that field and its detailed existing `place` and `via` chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image proof, rather than an older snapshot. The original creation chain places this calculation beneath the proper direct-image/alteration inputs of step (3); the current blueprint's steps (1),(2) also explicitly describe total tensor of bounded flat models. This is a generic tensor prerequisite, not a new argument for the geometric direct-image theorem. The report does not claim that the small-site assertion is a scheme-only statement or that it proves coherence or proper support.

## Not duplicates

No new nodes were created. The whole-DAG and imported-blueprint searches for K-flatness, bounded flat complexes, restriction/tensor, conservative flatness and strict-perfect tensor found existing reusable ingredients. In particular I reused `lem-sfb-ringed-site-conservative-flatness` (05VC), `lem-weil-pbc-slice-restriction-flat` (0E8J), `lem-pc-bounded-above-flat-kflat-site` (06YQ), and the existing one-sided derived tensor and slice restriction nodes. Existing scheme-specific local strict-perfect tensor models have stronger geometric hypotheses and are not substitutes for this item. The blueprint keyword searches did not reveal another blueprint node with this full arbitrary-ringed-site statement; `same_as` remains empty.

## Review by NF

I read the source local calculation in `spaces-perfect.tex`, Tag 0DKJ (`lemma-tensor-perfect`), including the displayed finite sums and its last sentence on relative Tor dimension. I checked the machinery in `sites-cohomology.tex`: Tag 06YQ (`lemma-bounded-flat-K-flat`), Tag 06YU (`definition-derived-tor`) and its preceding K-flat resolution/one-sided-computation construction, Tag 0E8K (`lemma-restriction-K-flat`), and Tag 0DEN (`lemma-check-K-flat-stalks`). I read `sites-modules.tex` Tag 05VC (`lemma-check-flat-stalks`), Tag 0E8J (`lemma-restriction-flat`), and the change-of-rings construction. The proof actually uses 05VC for termwise flatness rather than citing 0DEN for a claim about flat terms, which 0DEN alone would not give. There are no new-node sources to review.

For step 1 I opened the conservative flatness criterion and flat slice restriction statements. The former works for a nonconstant ring sheaf on a small site with the supplied conservative family; the latter is a general ringed-site statement, not an open-of-a-scheme lemma. Applied to the underlying R-module of each M term, they give exactly the flatness required. The scalar restriction definition confirms the equality of underlying restricted sections and actions.

For step 2 I checked that the bounded-above flat-complex node is stated for arbitrary ringed sites. The finite free retract argument is written out: tensor is a direct summand of a finite sum of identity functors, and kernels/images split. This uses the supplied global splitting on the slice, not projectivity of global sections. Boundedness above by b supplies the lemma's remaining hypothesis.

For step 3 I read every cited statement: the site-derived-tensor descent node gives the K-flat localization equivalence and two-sided comparison, the one-sided normalization node permits an arbitrary second complex, and the two restriction nodes preserve K-flatness and flat terms respectively. The localized tensor comparison is natural and acts by identity on sheafified pure tensors, exactly as the chain comparison needs. There are only finitely many q in [c,d] in any total degree, so exact restriction suffices to preserve these finite sums; no assertion about arbitrary coproduct preservation is hidden here. The formula explicitly checks both differentials and the sign. Thus this is the assembly of the cited comparisons, with all its hypotheses checked, not an invocation of a definition for a missing derived comparison.

Step 4 uses the one-sided comparison again after applying the derived tensor bifunctor to the *given* isomorphism from the local L model. I checked that L has both properties required by that node (flat terms and K-flatness) and that M need not be flat over A. This is the key distinction between A-flatness of L and R-flatness of M.

In step 5 I checked the signed total-tensor definition and the sheafified tensor definition. The written splitting maps really tensor to a splitting, the finite-free identification and its inverse are explicit, and p+q=n gives precisely [a+c,b+d], with no sign or homological-degree reversal. Step 6 proves finite-sum and retract flatness directly using the definition of sheaf flatness and splitting of kernels/images. It uses the R-flatness established in step 1 and never assumes R to A is flat. These elementary calculations are steps, not extra nodes repeating parts of the item.

In step 7 the bounded-above lemma is now applied over R_U, with upper bound b+d. I checked the scalar-restriction node's opening general clause, which says termwise restriction preserves quasi-isomorphisms and identifies localized complexes. Its ring parameters specialize to B=A=R_U and S=A_U, so its clause applies to this precise map; none of its later special change-of-rings conclusions is being borrowed. Scalar restriction and slice restriction have the same underlying sections in either order.

Step 8 repeats the actual first-factor K-flat calculation from step 3 over R, now with second complex F[0]. I checked that F is arbitrary, with no flatness hypothesis: the one-sided comparison is the result that licenses this. After restriction, the already-proved K-flat model T gives the asserted complex. Step 9 uses the explicit total terms and the definition of cohomology in the derived category: outside the interval the degree term is zero, so both its cohomology and that of the isomorphic derived object vanish. The final citation of `def-weil-abstract-derived-category` supplies the factoring cohomology functor, not a separate unquoted theorem.

I tested the zero complex, rank-zero retract, a single-degree L, a single-degree M, empty slice and the zero-ring case. For the single-degree case the interval endpoint is the sum of the actual cochain degrees. The flatness proof only uses R-flatness of M, so it also allows a nonflat map R to A whenever the specified M exists. Nothing requires coherence, Noetherianity, proper support, a geometric morphism between geometric spaces, or compactness. The conservative-point hypothesis is used only to turn the stated stalk-flatness into sheaf flatness.

I checked delivery-errors B through E against the files: no new or duplicate statements, no copied clause used as a replacement proof, no cycle through a descendant, no non-elementary fact cited merely by a tag, and every used node's actual statement supports the claimed operation. All 25 citation quotes are verbatim; `proof_deps` is the union of `uses`; every elementary flag is Boolean. All proof steps are shorter than 2000 characters. Generic off-unit statements are declared in `split_report.tool_uses`, preserving the unit's route. No SGA source is used, no Lean was written, and no compiler, Lake or build was run.

## What could not be finished

Nothing in the requested stage-1 split remains unfinished. The existing dependency nodes retain their own proof status; this delivery creates none. The first server-only `review_split` check passed. Required final dry-run and push results are recorded below when available.

## Validation

The required `deliver.py NF lem-sfb-ringed-strict-perfect-relative-tensor --no-push` exited successfully and printed `OK (not pushed) ... at 8705e840c8c: preflight passed`. The independent server `review_split` also printed PASS, with 0 new nodes and the generic tool uses recognized. This report addition records that result; it changes no mathematical content.
