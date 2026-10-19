# Stage-1 report: lem-trf-flat-ml-minimal-support

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-ml-minimal-support.json`: statement, now split into five proof steps; no Mathlib match for the full statement.
- `citations.json`: every step/node pair, with a verbatim quotation of the statement actually used.
- `report.md`: this report.
- `searches.jsonl`: real results recorded by the prescribed search command, retained intact.

There are zero new nodes and zero new Mathlib leaves. The existing Mathlib leaf `lem-weil-pbc-flat-tensor-exact` supplies the one non-elementary theorem needed in the proof.

## Attachments

None. Searched the complete read-only slopmaster2 `WeilConjectures/` tree for the exact item id, Mittag/mittag, least submodule, and minimal support. No project declaration states this item. The sole incidental minimal-support hit is about linear dependence in SemilinearFrobenius, not tensor support. No Lean was written or compiled. The upstream master is not treated as evidence of a closed proof.

## WANTED

None: the entire argument and its auxiliary exactness result are in the local Stacks algebra source.

## Corrections and scope

The imported statement is correct as written. Its hypotheses and conclusion were preserved, including arbitrary E and finite generation of the least submodule. Only the source place was normalized to the literal TeX label `lemma-minimal-contains`, Tag 0AS6. The item originally had no proof; the split now spells out the quotient-product map, the factor-swap comparison required by the definition's tensor orientation, componentwise vanishing, and the finite-generation argument. In particular the map E to the product of quotients is not assumed surjective.

Read the chapter and unit records, the current main-20261015 blueprint proof of `lem-trf-local-term-locality`, and the parent `lem-trf-flat-mittag-leffler-criterion`. This is supporting algebra for the inherited flatification/projectivity ancestry; it does not restate or reroute the chapter or unit. It is not a unit key node, so no unit record was changed. All writes are confined to this item's sandbox.

## Unfinished work

None at stage 1. The proof is complete using existing nodes; no new obligations were created.

## Not duplicates

No new nodes were created. Searches of the complete DAG for Tag 0AS6, `minimal-contains`, smallest/least submodule, and the relevant tensor-intersection concepts found this item and its existing parent, but no separate replacement lemma. Whole-blueprint searches for `Mittag`, `0AS6`, `smallest submodule`, and `least submodule` found no blueprint statement of this result. The inverse-system Mittag-Leffler node is about a different notion. The parent only states the finite-free criterion, depends on this item for its forward implication, and cannot be used here without circularity.

## Review by Q75

I read the statement and entire proof of Stacks Tag 0AS6 (`algebra.tex`, label `lemma-minimal-contains`, lines 21533 onward). I also read Tag 00HB (`definition-flat`) and Tag 00HD (`lemma-flat`), including the equivalence of tensor exactness with preservation of injections. For the Mittag-Leffler input I read the existing definition node, which explicitly uses condition (2) of Stacks Tag 059M; its tensor comparison is precisely the hypothesis needed here. I read the complete statements of all four nodes used in the five steps: the flatness definition, tensor-product definition, module Mittag-Leffler definition, and flat-tensor exactness lemma. There are no new nodes requiring a separate source review.

Step 1 uses `def-weil-pbc-flat-ring-map` only for injectivity after tensoring an inclusion, which its statement explicitly provides, and `def-weil-pbc-module-tensor-product` for the identity map. I checked that the collection of supports is a set, contains E, and that the displayed map q is linear. The kernel calculation is pointwise: q(e)=0 exactly when e belongs to each supporting submodule. It does not require the intersection to be finitely generated, the ring to be Noetherian, or the product map to be onto.

Step 2 uses `def-trf-mittag-leffler-module` for injectivity with the set I of supports and the family E/N. I checked that the definition has all set-indexed families, not only finite products. It uses `def-weil-pbc-module-tensor-product` to construct the reversed-order comparison and factor swaps by bilinearity, and to check identities on generators. The formula shows explicitly why this beta is conjugate to the injective map in the definition, so no uncited theorem about arbitrary intersections is hidden here.

Step 3 uses the tensor definition's explicit functoriality, zero-map identity, and pure-tensor generation. For each supporting N there is a lift by definition of image; q_N composed with its inclusion is zero. The Nth component of beta(q tensor 1) is q_N tensor 1 on generators. These formulas establish zero image under beta, and its injectivity from Step 2 then establishes zero image under q tensor 1. This is an elementary calculation, not an additional exactness assertion.

Step 4 uses the statement of `lem-weil-pbc-flat-tensor-exact`, specifically its last sentence about a sequence beginning with zero. It gives exactly the kernel/image equality for K to E to P after tensoring. R is commutative, M is flat, and Step 1 established exactness at E and injectivity at K; those are all its hypotheses. Neither surjectivity to P nor finite presentation is required. The resulting lift proves K is itself a support, and the elementary intersection inclusion proves it is least. This is the only non-elementary step and has an explicit theorem citation. The cited theorem is already a Mathlib leaf, so its use from another unit is allowed as a tool without altering the unit route.

Step 5 uses the tensor definition's explicit statement that pure tensors generate, together with its bilinearity and induced-map formula. A finite linear combination is a finite sum of pure tensors after absorbing scalars into the K coefficients. The submodule L generated by these coefficients supports x by the displayed lift. Since L is contained in K and Step 4 makes K least, equality follows. This is the source's few-line finite-generation argument, fully written in the item; creating a separate finite-support node would be unnecessary. I inspected the Mathlib hits `Submodule.exists_fg_le_eq_rTensor_subtype` at `Mathlib/RingTheory/TensorProduct/Finite.lean:35` and `Submodule.exists_fg_le_eq_rTensor_inclusion` at line 59: they supply finite supports, not least ones, and do not make the full item a Mathlib leaf. I also inspected `Module.Flat` and its injection lemmas in `RingTheory/Flat/Basic.lean` and the `Functor.IsMittagLeffler` definition in `CategoryTheory/CofilteredSystem.lean`; the latter concerns image stabilization for functors to types and cannot attach to the module-level assertion.

I checked the small cases: for x=0 the zero submodule is a support, so K=0 and the empty generating list suffices; E=0, M=0 and the zero ring reduce to the same case. For M=R the tensor/unit identification sends x to an element e of E, and the least support is Re, consistent with the proof. For a field and a finite sum with independent M coefficients the construction gives their coefficient span. Nothing assumes E is finite, or that a submodule of a finite module is finite; finite generation is obtained only after taking a tensor lift in K.

Against delivery-errors B I checked definition coverage, literal TeX, the exact Stacks tag/label, inherited blueprint fields, and searches made by the prescribed command; no new node can be a duplicate, elementary over-split, or a restated clause. Against C I checked each dependency's actual statement and provided exact quotation coverage for every use; the full tensor-definition quotation covers the different clauses used by different steps. Against D the argument stays in the item's proof and depends on no child restating its assertion; the parent criterion is not cited. Against E I checked every hypothesis, the two tensor orders, arbitrary product indexing, the actual quotient-product kernel, and the distinction between a lift in K tensor M and a mere ambient tensor expression. No source or statement dispute was found. Every proof step has fewer than 2000 characters, and none hides a separate non-elementary lemma. No SGA source is cited.
