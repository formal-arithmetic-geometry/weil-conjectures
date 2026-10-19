# Stage-1 report: lem-sf-finite-field-sheaf-scalar-extension

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-finite-field-sheaf-scalar-extension.json — existing statement, split into six steps; no Mathlib match for the complete statement.
- citations.json — ten entries, one verbatim statement excerpt for each cited node in each step.
- report.md — this report.

No new nodes and no new Mathlib leaves. prepare.py is sandbox-only preparation code. Searches are logged in searches.jsonl. No Lean was written, no compiler or build was run, and the shared project and launcher were not edited.

## Attachments

None. I searched WeilConjectures/ of the read-only slopmaster2 source for the exact blueprint tag and for scalar extension / extendScalars / finite-field / constructibility notions. The source's adic and derived constructions have different interfaces; no project declaration states all the finite-field, intrinsic finite-stratum, target-action and cohomological clauses here. The upstream master is reference only. The node has no recorded own Lean declaration to inspect.

## WANTED

None. All sources used are already present.

## Audit of the imported item and blueprint

The item was unsplit, with no proof steps. Its statement is retained byte for byte, as are stmt_deps, the source, creation data, chapter, unit and blueprint ancestry. There is no statement dispute. The source's Tag 093V asserts local constancy only and explicitly omits the proof: by itself it does not assert exactness, the coefficient action, finite stalks, or the unbounded termwise cohomology comparison. The split makes those arguments explicit using the smaller existing statements below.

The current main-20261015 text of def-weil-rationalization-karoubi, last paragraph, defines scalar extension on integral representatives before rationalization. This item serves the finite residue layers in the existing parent lem-weil-integral-scalar-extension-constructible; it does not change the ambient-operations unit or its route. I read the chapter and sk-def-sf-operations unit records. This is not the key node of that unit, so its realized fields are not edited.

I searched the whole DAG's titles/statements for finite fields, constant module tensors, exactness, locally constant tensors and tensor/pullback comparisons. I used blueprint_refs.py ancestor and searched the blueprint for finite-field scalar extension, tensor product locally constant, scalar extension constructible, locally constant tensor and exact functor homology. No imported blueprint node states the complete item in another form; same_as remains []. The generic lem-pod-lisse-tensor-and-scalar-extension is etale, not the required pro-etale result; lem-weil-pbc-locally-constant-tensor gives derived local constancy over a single Noetherian coefficient ring and not the target coefficient action. Neither was misused as the complete answer. No new node was needed.

The sandbox initially held only search logs, no item or report. I read those logs and retained all prior searches already recorded in the repository node. The additional searches recorded in the item were actually run by msearch.py and their results read. LeanSearch's ordinary ModuleCat.preservesFiniteLimits_extendScalars_of_flat candidate was inspected in Mathlib/Algebra/Category/ModuleCat/Descent.lean, lines 42–47: it proves ordinary module exactness, with no intrinsic pro-etale constructibility clauses. Loogle's generic presheaf tensors and cartesian sheaf tensors, LeanFinder's condensed locally constant module functors, and grep's constructible subset / Chevalley declarations do not state the item. No search-service failure was called a negative result.

## Tool uses

The three off-unit generic tools are declared in split_report.tool_uses for the maintainer's judgment: lem-pc-sites-module-sheafification-tensor (constant tensor and finite-sum descriptions), lem-pe-constant-left-module-inverse-image (constant ring coefficients on strata and localized sites), and lem-weil-pbc-ringed-topoi-module-pullback-tensor (underived tensor comparison). They are categorical tools, not replacement proof routes. Other off-unit facts used are already Mathlib leaves. I checked their full statement/proof-dependency closures do not reach this item.

## Not duplicates

No new nodes: there are no new/existing-node pairs to distinguish.

## Unfinished work

None in the mathematical split. All generic ingredients already have DAG nodes; their own subsequent work belongs to those nodes. Required remote checks and delivery results are recorded below as they complete.

## Review by Q137

I read Stacks sites-modules.tex Tag 093V (lemma-tensor-product-locally-constant), whose proof is omitted, and expanded it rather than treating the reference as a proof. I also read Tag 0GMW (lemma-sheafification-tensor), Tag 03EL (lemma-tensor-product-pullback), sites.tex Tag 00WJ (lemma-sheafification-exact), sites.tex Tag 00YV (proposition-functoriality-algebraic-structures-topoi), and homology.tex Tag 010N (lemma-exact-functor). No SGA source is used. There are no new nodes requiring separate sources.

Step 1 uses the exact statement that a module over a field has a basis, from lem-weil-pbc-module-over-field-flat. Finiteness of the basis is immediate from its injective inclusion into finite k'. The sheafification/tensor node explicitly applies to presheaves over a presheaf of rings, and its second clause explicitly allows one factor to be an already existing sheaf. Thus taking the constant presheaf k, F restricted to constant k-scalars, and constant k' meets its hypotheses. I wrote both coordinate maps and checked restriction and naturality; the finite product presheaf is already a sheaf. I did not pretend the section rings k_Y(U) were fields.

Step 2 uses the abelian-category and exact-sheafification clauses of lem-weil-pbc-site-module-presheaf-sheafification-exact. The finite kernel/cokernel argument is written componentwise. The target k' action is retained: kernels inherit it and cokernels carry it by quotient, so the underlying isomorphism check suffices. This is a few-line finite-sum calculation from the cited statement, not an uncited flat-sheaf theorem or a new node.

Step 3 uses def-weil-proetale-inverse-image only for the geometric morphism it explicitly constructs; I did not cite that definition for a tensor theorem. The constant-ring isomorphisms and their compatibility with localization come from the explicit statement of lem-pe-constant-left-module-inverse-image. The canonical underived tensor isomorphism is exactly lem-weil-pbc-ringed-topoi-module-pullback-tensor. Both have the needed small-site/universe convention, already part of the item's site definition; the stratum is an arbitrary scheme morphism, so no etaleness of the immersion is assumed. Multiplication on the right tensor factor checks the comparison is k'-linear, including locally represented coefficients.

Step 4 applies the actual sheafification/tensor statement again to two constant presheaves on the localized site, so it proves the stated constant model V tensor_k k' on the same cover. It is valid even for infinite V. The displayed generator calculation proves finiteness when V is finite, and the right-factor formula proves target linearity; neither assertion was inferred from merely local constancy over k.

Step 5 uses the exact intrinsic definition def-weil-proetale-constructible-sheaf, which asks for a finite global stratification and finite geometric stalks, and def-weil-proetale-geometric-stalk, which explicitly gives the module colimit construction. I keep the original stratification. Applying the finite-sum description on each stratum and the elementary universal-property calculation for finite sums and colimits gives finite stalks without any assertion that every initial constant model on an empty object must be finite. This avoids needing an etale-only finite-value theorem or a noetherian hypothesis on Y.

Step 6 uses clause (c) of lem-sp-exact-functor-preserves-homology, whose statement gives the natural comparison in the target abelian category with its cycles and image maps. Exactness was proved in step 2 and the module categories were checked abelian. Applying it to three consecutive terms requires no upper or lower bound on C. The same constructibility and vanishing interval then follow directly, with no derived Tor-amplitude hypothesis.

I tested the identity field map, zero F and zero complex, empty Y or an empty stratum, a stratum with infinite local models on unused empty site objects, r=s, and a complex unbounded in both directions. For a nontrivial example F the constant k-module k and k'=F_(q^d), the model is the constant k' module k', while its forgotten k sheaf is d copies of k, as required. No hypothesis about ell-invertibility, noetherian schemes, enough points or finite Tor dimension is used. Each step is under 2000 characters; I checked there is no hidden lemma in any long step. Citations.json quotes were checked against the current node statements, and proof_deps is exactly the union of uses. I corrected the source label for 010N to lemma-exact-functor while preparing the report. No mathematical correction to the statement was needed.
