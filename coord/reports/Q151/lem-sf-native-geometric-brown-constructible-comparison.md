# Stage-1 delivery: lem-sf-native-geometric-brown-constructible-comparison

## Files written

- dag/nodes/sec-six-functors/lem-sf-native-geometric-brown-constructible-comparison.json: statement node, now split in five steps; not a Mathlib leaf. Statement and statement dependencies unchanged.
- citations.json: nine verbatim statement excerpts, one for each step/node citation.
- report.md and searches.jsonl: review and actual search log. write_split.py is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched all of lean/WeilConjectures for the exact blueprint tag, Brown, and native locally finite coefficient terminology, then read the finite-coefficient localizing exceptional-adjoint file. The latter concerns constant finite coefficients and does not give this item's native locally finite algebraic-closure statement. The existing generator test has a proved Sheaf declaration, which I inspected as support for reusing that node; it is not an attachment of this item.

## WANTED

None. The applicable blueprint, Stacks categories.tex and derived.tex, and all cited DAG statements are locally available. coord/dag-sync.md named in the historical standing brief is absent; the explicit current shared-repository/direct-delivery instructions govern this run.

## Changes and source audit

The item was unsplit, with no sandbox copy, no repair note and no project declaration of its full statement. I retained its complete statement, native coefficient sheaf, nonseparated base-scheme allowance, chosen compactification, common finite coefficient-field stage, and distinction between ordinary derived equivariant objects and fixed pairs after derivation. The free-induction and Frobenius data are retained because they occur in the statement's common setup, although the geometric comparison itself does not use them.

I read the six-functors chapter and sk-prop-sf-biduality-general unit. The item's actual source is the final sentence of main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md. That sentence does not itself prove an ambient comparison. The item already records the extra comparison as agent-formulated. Accordingly proof_origin remains agent, with the explicit categorical argument, rather than attributing that argument to the blueprint. No SGA source is used.

The blueprint ancestor command reports None for this created branch. I retained the item's supplied null anchor and its inherited via/place, which already identify the actual source sentence. Whole-DAG statement searches and blueprint searches for orthogonal, adjunction and localizing found the existing abstract generator test and natural-Hom-bijection adjunction leaf. They do not supply another statement of the full item. same_as remains []. No unit realized field changes: this item is not the unit's key proposition.

Actual Mathlib searches used leanfinder (two different phrasings), loogle, grep and leansearch. I read every hit: generic localization/adjunction and orthogonal results do not assert the native sheaf realization comparison. The grep hits identify mkOfHomEquiv and its counit formulas; the existing node lem-weil-pbc-adjunction-of-natural-bijection already states exactly that tool, so no new leaf was created. I read Adjunction/Basic.lean at the named definitions/formulas. An invalid Loogle identifier returned zero hits with an explicit diagnostic, which is preserved; it is not offered as evidence of absence. The independent semantic and grep searches supply that evidence.

## Not duplicates

No new nodes. In particular, I reused lem-sf-localizing-hom-test rather than creating a specialized Brown/constructible comparison lemma, a cone-orthogonality node, or another generator detector. A separately packaged transport lemma would only repeat the elementary Hom-composition calculation here.

## Review by Q151

I reviewed delivery-errors B through E against the actual JSON and the local source passages, not just their file names. Every proof citation is to a statement I opened; citations.json excerpts were checked as literal substrings of those statements. There are no statement-only additions, hidden proofs in new statements, new definitions, new Stacks-tag duplicates or potential elementary new nodes. The proof stays inside ordinary categories and keeps every hypothesis of the realization and stage adjunction nodes.

For step 1 I read the statements of lem-sf-locally-finite-adic-constructible-realization, lem-sf-locally-finite-adic-compact-support-realization and lem-sf-constructible-exceptional-adjunction-coefficients. They give, respectively, a fully faithful triangulated equivalence on derived morphisms, precisely the alpha comparison for the chosen compactification and constructible preservation, and the common-stage exceptional Hom adjunction. They allow finite-type schemes that are not separated over k; f itself is separated finite type. The current qc/lft hypotheses express finite type, and the specified geometric base changes and compactification are exactly the inputs already fixed in the item's statement. No individual finite-E category is identified with the native category. I wrote every arrow in the transported Hom chain, including the direction of alpha, postcomposition with e inverse, and the inverse J_X used only to extend from the essential image. The natural-bijection adjunction leaf supplies the adjunction and triangle identities; Stacks 0037 and its following paragraph give the relevant unit/counit definitions.

For step 2 I followed the identity backwards along that chain. The resulting alpha inverse, stage counit and e occur in the order printed in the item's formula. Naturality in the source cancels the auxiliary equivalence counit d, so no compatibility of arbitrary inverse-equivalence choices is being silently assumed. The adjunction leaf explicitly identifies the counit as the inverse image of the identity. This calculation is elementary once step 1 has established the chain.

For step 3 I checked the actual inverse-transpose formula from the same leaf and Stacks 0037. The defining equation for t, both inverse transposes in the naturality square, and the formula for postcomposition by t are written explicitly. The realization node states an equivalence of ordinary triangulated categories, so every integer shift of a constructible input is available. No assertion that G is constructible is used here: its target need only lie in the localizing hull.

For step 4 I opened the full statement of lem-sf-localizing-hom-test and inspected its proved Sheaf source. It applies to an arbitrary class without compactness or essential smallness. Its two endpoints belong to the same localizing hull: one by the definition of G_c, the other by the supplied codomain of G. Its exact bijectivity hypothesis is step 3, for every integer n. The full replete triangulated closure and its coproduct universe are the ones fixed in the item. Thus no assertion of compactness of these native constructible objects, no existence of a new ambient adjoint, and no coproduct indexed by a proper class is smuggled into the argument. This is a generic off-unit tool use, declared in split_report.tool_uses; it does not replace any geometric step of the unit.

For step 5 I read Stacks derived.tex, lemma-third-object-zero (05QR), and lem-kun-distinguished-cone-zero, which states the iff needed in this direction. It applies to every distinguished cone of the now-invertible t; a zero target has only the zero map from any shifted object. The orthogonality assertion for all objects of the localizing hull is thus a consequence of the proved isomorphism, with no compactness or Hom-continuity assumption. There is no cycle: the reused detector and zero-cone leaf do not depend on this item.

I tested the zero object M, A=0, f=id, an empty source scheme, n=0 and negative n. The Hom composites still consist of bijections, the counit-transpose equation still determines t, and every cone is zero. These cases also check that no nonzero rank, global rank bound, nonempty generator family or separated structure morphism is required. All five proof steps are below 2000 characters; none hides a separate comparison theorem. No statement dispute or correction was necessary.

## Unfinished work

None for this one-level split. Its substantive geometric realizations remain the already existing dependency nodes, not new claims hidden in this proof.
