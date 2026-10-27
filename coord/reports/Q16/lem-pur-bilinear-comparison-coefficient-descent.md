## Files written

- dag/nodes/sec-smooth-purity/lem-pur-bilinear-comparison-coefficient-descent.json: statement, split into 13 explicit steps; no exact Mathlib match.
- citations.json: one verbatim statement quotation for every step/node citation.

No new nodes and no new Mathlib leaves. Searches of the project by blueprint tag and by bilinear/localization/common-stage concepts found no declaration giving the entire item. The existing StageSystem functor descent source is unary and does not give the raw bilinear rationalization theorem.

## Attachments

None.

## WANTED

None. This is an agent proof, as the item's own source already says, elaborating the two blueprint constructions rather than attributing a nonexistent bilinear descent theorem to them.

## Statement correction

STATEMENT-DISPUTED: the literal phrase “finite fields E contained in Omega” is impossible: Omega is an algebraic closure of Q_l, has characteristic zero, and has no finite subfield (a finite field has positive characteristic). The immediately following valuation ring, uniformizer and coefficient-extension reference show the intended objects are finite intermediate extensions Q_l ⊆ E ⊂ Omega. I replaced only that phrase. This is faithful to both displayed blueprint sources and to def-weil-finite-subextension-directed-set. No hypotheses on Hom torsion or on injectivity of transition functors were added.

The recorded blueprint ancestor says “Clause 5” in the earlier created-node metadata. The current main-20261015 Frobenius coefficient-twists source is a paragraph, whose final sentence is compatibility with coefficient extension. I retained the inherited provenance, and explained its actual textual anchor in split_report. This item is not the statement of its unit, so no unit realization file is changed.

## Not duplicates

No new nodes. I searched all DAG statements and the blueprint for bilinear extension, scalar localization and common-stage comparisons. def-weil-module-base-change already includes exactly the needed bilinear Hom-module extension and is reused as a Mathlib leaf. lem-pur-semilinear-scalar-localization already gives transition functor extension and component equations and is reused. lem-sf-framework-common-stage-descent and prop-weil-pbc-descent-functors concern exact unary functors on framework geometric categories; lem-sbc-coherent-pair-functor-descent assumes additive categories and normalized transitions, whereas the item assumes merely linear categories and specified unit isomorphisms. None is cited with hypotheses absent here. lem-sf-tensor-comparison-localization-descent has monoidal/perfect-complex hypotheses and is not the present abstract statement. The present item's assembly writes the common-stage calculation instead of adding a node restating one of its clauses.

## Review by Q16

I read coord/brief-stage1.md, both versions of delivery-errors B through E, the three levels in SETUP.md, GOAL.md, the item chapter and unit, the current raw rationalization and algebraically closed coefficient definition texts, and the Frobenius coefficient-twists ancestor paragraph. I read Stacks algebra.tex at section-tensor-product (Tag 00CV), definition-base-change (05G3), lemma-universal-property-localization-module (07K0) and lemma-tensor-localization (00DK). The source's Hom tensor formula and common-field colimit motivate this construction; the proof of the abstract bilinear assertion is explicitly marked agent-written.

For step 1 I opened def-weil-module-base-change: its statement actually includes the unique scalar extension of a bilinear map, not merely the name of module base change. def-weil-linear-category supplies bilinear composition, which makes U(f,g) bilinear via its factorization into the two partial functors. Step 2 uses the statement of lem-weil-linear-scalar-localization-category for the category structure and composition formula; its own calculation checks the bifunctor laws. Step 3 uses the formula and identities in def-weil-linear-scalar-localization to check naturality on pure tensors and both inverse equations. Finite sums of pure tensors suffice, so no torsion-free assumption is hidden.

For step 4 I read the whole statement of lem-pur-semilinear-scalar-localization: its unital-ring-map condition and invertibility condition are satisfied by O_E to O_L, since a nonzero element of O_E remains nonzero in the extension field L. I read lem-weil-l-adic-integers-localization-uniformizer, which states O_E[1/varpi_E]=E, and use it for both fields. The semilinear theorem covers unary functors and transformations. I do not apply it to an unlinearized product category: the bilinear scalar-comparison naturality is checked directly on pairs of pure tensors, and its equations are checked componentwise. I declare this generic localization result as a tool use in split_report, not as a top-level approval.

Steps 5 and 6 use def-weil-finite-subextension-directed-set and def-weil-directed-colimit-abelian-groups exactly for finite common bounds, representatives, and the later-stage equality criterion. I opened those statements. The latter actually states the criterion; it is not merely a universal-property definition. The general-category transport is written with the item's supplied unit and tower maps. I check its transitivity using the two endpoint associators and their naturality. The geometric common-stage definition is cited as the model being copied; no geometric theorem is silently specialized to arbitrary linear categories. Identity representatives live on S_{E/E}X, so nontrivial unit isomorphisms cause no normalization assumption.

Step 7 writes the output endpoint identifications d explicitly, including both input associators. Step 8 proves their field-change identity by expanding d, the naturality of lambda and the two associator cocycles, then cancels the comparison maps to obtain the transported-arrow formula. These are direct calculations with supplied hypotheses, not external comparisons left uncited. Step 9 uses the colimit equality criterion again to establish representative independence and writes identity and composition cancellations. No transition Hom map is assumed faithful.

Step 10 derives exactly the requested eta representative from the supplied scalar square and then rewrites it using d and eta naturality. Its inverse is the corresponding formula for eta inverse. Step 11 writes the naturality equation at the same field and gives the comparison between different initial output fields as d_new inverse followed by d_old. The initial-field comparison cocycle is cancellation of three such factors, rather than literal equality of differently based objects. Step 12 checks identities, composition and whiskering by evaluating the scalar comparisons on transformation components; their naturality supplies the remaining outside conjugations. Step 13 uses only the cited finite-common-field and equality criterion plus those established cancellations for finite equations. Signed symmetry uses additivity, so the minus sign is preserved. All named coherence laws in the conclusion are supplied equations, not structures asserted to exist for arbitrary bifunctors.

I checked every B–E requirement against the actual files. There are no new nodes needing separate notion dependencies, source tags, searches or duplicate-pair lines. Every quoted citation is copied from its node statement; proof_deps is exactly the union of uses. The proof has no circular citation or helper that restates its conclusion. Every elementary step is a tensor-generator calculation, a substitution of supplied cocycles, or cancellation of the displayed isomorphisms. None exceeds 2000 characters. I did not use SGA or change a target, the chapter route, the unit, or any Lean file.

Edge cases checked: empty source category (the corresponding bifunctor and transformation assertions are vacuous); zero Hom modules and pure torsion Hom modules (tensoring may give zero identities on zero objects and the proof still works); E=F=L and repeated fields with nonidentity unit comparisons (the unit cocycle supplies the identifications); noninjective transition Hom maps (only eventual equality is used); ramified field extensions (no equality between uniformizers is required); input objects at different fields (both input associators occur in d); identical and vertically composite transformations (middle conjugations cancel); signed equations (negatives pass through every linear map). The finite-field wording was the only mathematical correction.

## What could not be finished

Nothing remains in the stage-1 split. The required dry run and delivery are executed after this report is written; their output is the delivery evidence.
