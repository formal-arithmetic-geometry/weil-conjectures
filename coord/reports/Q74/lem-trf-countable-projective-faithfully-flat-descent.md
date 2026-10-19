# Worker report: lem-trf-countable-projective-faithfully-flat-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-countable-projective-faithfully-flat-descent.json: item split in five steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-mittag-leffler-faithfully-flat-descent.json: one new statement-only node, Stacks 05A5; no Mathlib match.
- citations.json: verbatim statement evidence for every step citation.
- report.md: this report. The wrapper owns searches.jsonl.

Delivery has 1 new node, 0 new Mathlib leaves. No Lean was written or compiled, and no agent was started.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint tag and the phrases countably generated projective, ffdescent-countable, Mittag and mittag; no matching declaration occurs. The read-only master's statements are not treated as finished proofs. Read WeilConjectures/Mathlib/RingTheory/Finiteness/Descent.lean: its proved finite-presentation descent theorem requires finite presentation and does not attach to this item or to the general Mittag-Leffler descent node.

## WANTED

None: all sources needed are in literature/stacks-project/algebra.tex.

## Problems found and corrected

The starting item was a correct statement-only refinement of Stacks 05A6. There is no statement dispute and the statement and its three statement dependencies are unchanged. The source writes M tensor S and the item writes S tensor M: swapping factors gives the canonical S-linear isomorphism, with the action in both cases on S, so this is the same statement. Kept the inherited blueprint ancestry and historical flattening/semistable-alteration locator rather than rewriting parent metadata. The current main blueprint has no separate countable-projectivity or module-Mittag-Leffler statement; blueprint_refs search for Mittag returns only the inverse-system theorem discussed below.

During my self-review I removed a draft helper for countable-generation descent: it was an elementary argument and also a clause of the item, hence not a valid new node under D1 and the brief. Step 1 now carries its complete generator/faithful-exactness argument. I also replaced a draft citation of only the projective definition for flatness by the actual existing projective-flat lemma, and expanded projectivity implies Mittag-Leffler into the finite-support coordinate calculation plus a retract calculation in Step 3. This removes the uncited projectivity-characterization implication. Corrected the source tag references against tags/tags: countable-generation descent is 0GVD, countable flat ML implies projective is 059X, and projectivity characterization is 059Z. No source error remains.

## Unfinished work

None for this one-level split. The general Mittag-Leffler descent node is deliberately unsplit, with a complete standalone statement and recorded searches, as the brief requires. Its source proof uses finitely presented directed presentations, domination/pushouts and faithfully flat descent of universal injectivity; that proof is work for the new node, not an implicit proof step of the item.

## Searches and reuse

The item's inherited Q96 searches and their actual returned records are retained. Added fresh wrapper searches under Q74 for the item using leanfinder, loogle, grep and leansearch, including a second natural-language phrasing. The new 05A5 node records only five wrapper queries actually run under this item: leanfinder with the named ML condition and again with tensor-to-products injectivity, loogle for Module.FaithfullyFlat with Mittag, grep for Mittag|mittag|ffdescent in RingTheory, and leansearch with the full descent assertion. The results are copied as the wrapper's JSON log entries, preserving exact tool/query text. All services answered successfully. No invented queries or unavailable-service claims are recorded.

Read the hits: Module.Flat.of_flat_tensorProduct / iff_flat_tensorProduct concern flatness only; Module.FaithfullyFlat.tensorProduct_mk_injective concerns M to S tensor M; lTensor_injective_iff_injective reflects injectivity of an already specified map; none establishes the tensor-to-arbitrary-products condition for M from that condition on its scalar extension. The grep hit is only AdicCompletion/Exactness.lean:27, a comment about avoiding Mittag-Leffler inverse systems. The item search's Module.Flat.projective_of_finitePresentation requires finite presentation, absent here. Read the existing flatness-descent and projective-flat leaves and their Mathlib source signatures. Reuse those leaves rather than create replacements.

Before creating the sole new node, searched the full DAG by 05A5, lemma-ffdescent-ML, Mittag-Leffler, countably generated projective, and their key-word variants, and searched the whole blueprint using blueprint_refs.py. Also searched both read-only source trees for Mittag/ffdescent/countable projectivity. None states this general descent lemma. The new statement is not a projectivity conclusion, so it is neither the item nor a clause of the item. It does not require countable generation, projectivity or flatness of M; its eventual proof is a different substantive lemma.

## Not duplicates

lem-trf-mittag-leffler-faithfully-flat-descent vs lem-weil-pbc-mittag-leffler: the existing blueprint node concerns inverse systems of finite abelian groups and R^1 lim, whereas the new node concerns the tensor-to-products property of a single module and faithfully flat scalar extension.
lem-trf-mittag-leffler-faithfully-flat-descent vs lem-trf-countable-flat-mittag-leffler-projective: the existing node concludes projectivity from flatness, countable generation and ML over one ring; the new node descends ML over two rings and assumes none of the other properties.
lem-trf-mittag-leffler-faithfully-flat-descent vs lem-trf-completion-flat-mittag-leffler: the existing node constructs the completion of a flat module over a complete Noetherian ring and proves properties of that completion; the new node concerns arbitrary faithfully flat ring maps with no completion or Noetherian assumptions.
lem-trf-mittag-leffler-faithfully-flat-descent vs lem-trf-local-projective-faithfully-flat-descent: the existing node descends projectivity and depends on this item; citing it here would be circular. The new node instead descends only ML and has no dependency on that theorem or this item.

No existing node carries Tag 05A5 in its source, so there are no same-tag pairs requiring a difference explanation beyond these conceptually close nodes.

## Review by Q74

I read the full statement and proof of Stacks Algebra lemma-ffdescent-countable-projectivity (05A6), lemma-ffdescent-countable (0GVD), lemma-ffdescent-ML (05A5), lemma-countgen-projective (059X), and theorem-projectivity-characterization (059Z). I checked tags/tags for the labels, and read the tensor-to-products definition node using Stacks 059M. The item agrees with 05A6 for arbitrary commutative rings and arbitrary modules, retaining faithful flatness and at most countable generation and excluding no zero or finite case. The new node is exactly 05A5, with the canonical factor swap explicitly noted in its source and the first-factor scalar action stated. The introductory prose in Stacks mentions flatness, but the actual lemma statement and proof impose no flatness on M; I followed that precise statement and did not add a hypothesis.

Step 1 uses the actual tensor definition's finite pure-tensor generation and the faithfully-flat definition's equivalence of exactness. The finite supports of countably many chosen generators give countably many elements of P. The image of tensoring their span is B-linear, contains every generator, and is therefore the entire scalar extension. Exactness of P0 to P to zero after tensoring is precisely the surjectivity test to which faithful exactness applies. This is an explicit routine generator argument, not an uncited countable-descent theorem. No quotient exactness or injectivity claim is needed. I checked the original complex has composite zero and tensor of zero is zero from bilinearity.

Step 2 cites lem-weil-pbc-projective-module-flat, whose statement really says any projective module is flat, and lem-weil-pbc-flatness-descends-faithfully-flat, whose statement really compares flatness over A with flatness over B of B tensor_A P. I opened both complete nodes and their Mathlib declarations. The ring is commutative as required, B is faithfully flat by the given ring map, and the scalar action is the exact first-factor action of the item. No finite-presentation hypothesis is introduced.

Step 3 uses def-weil-pbc-projective-module for a retract of a free module, not for any unstated ML theorem. It uses the tensor definition for the explicit mutually inverse coordinate maps between F tensor Q and finitely supported Q-valued families. For a product family the coefficient array has only finitely many nonzero rows, and vanishing of every output coordinate makes every entry vanish, proving injectivity. Naturality with the retract inclusion is checked on a pure tensor, and tensoring the retraction supplies a left inverse. These are routine calculations from the three cited definitions; no tensor-product/product commutation is asserted. This proof works for arbitrary index sets and arbitrary test modules, and thus proves precisely the ML condition in def-trf-mittag-leffler-module. It is kept elementary rather than made into a redundant lemma node.

Step 4 uses exactly the new node's statement: the same A to B is faithfully flat, P is an A-module, and Step 3 gives that its B-scalar extension is ML. Step 5 uses exactly the statement of the existing lem-trf-countable-flat-mittag-leffler-projective, with its three hypotheses supplied by Steps 1, 2 and 4. I read its full node and Stacks 059X. No stronger general projectivity-descent theorem is cited; in particular there is no cycle through the parent 05A9. All citations have a verbatim statement quote in citations.json; none borrows from a cited node's proof.

I tested the item and new statement at M=0 (empty generators), R=S (identity), zero rings, and S=R[t] (faithfully flat, infinitely generated extension). For the new node I also tested nonflat M=Z/2 over R=Z and S=Z[t]: finitely presented modules satisfy the tensor ML condition, so the absence of a flatness hypothesis is consistent. Faithfulness cannot be dropped: Z to Q with M=Q gives an ML scalar extension but Q is not ML over Z, as in Stacks' example-Q-not-ML (tensor with the family Z/n). The final criterion is used only after flatness and countable generation have both been established; arbitrary flat modules are not assumed projective. Free-basis and product families may be empty: the coordinate proof and retract calculation still give zero as needed. These checks address E1-E4, and the explicit coordinate/retract maps and faithful exactness test address E5-E6.

Against B1-B10: the only new node is statement-only, introduces all objects, names its three notion dependencies, uses single-escaped TeX, gives the exact Stacks tag/label, has actual logged searches of every required kind with two phrasings, and has complete blueprint from/place/via and same_as fields. It is not Mathlib and no leaf declaration is invented. Against C and D: cited statements were opened and match each use; the two elementary arguments are written out; proof_deps equals the union of uses; the one new lemma is a strictly intermediate property, not a relabelled projectivity conclusion. The same-unit existing criterion is reused; the two cross-unit theorem citations are Mathlib leaves, and all remaining cross-unit citations are notion definitions. There is no off-unit route replacement. Against E: hypotheses were checked at the steps just described; the item statement is unchanged and no source error was found. Every proof step is under 2000 characters, with no hidden comparison theorem: the only comparison map in Step 3 has both formulas written out. No SGA source is cited. The review corrected the draft helper/citation issues described above before submission.
