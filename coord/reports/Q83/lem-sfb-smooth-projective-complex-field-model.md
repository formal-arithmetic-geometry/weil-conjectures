# Q83 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-projective-complex-field-model.json: item, split in seven steps. Reuses finite-presentation descent, closed-immersion descent, smoothness descent and base-change nodes already in the DAG.
- dag/nodes/sec-six-functors-basics/lem-sfb-countable-simple-extension-embedding.json: new statement-only lemma, unsplit; no exact Mathlib match. It concerns a specified embedding and one arbitrary generator, rather than descent of schemes or a finitely generated characteristic-zero field as a whole.
- citations.json: one verbatim statement quotation for every step/node pair.
- searches.jsonl: actual msearch.py records; searches were read, not invented. The supplementary write_split.py only assembles these sandbox JSON artifacts.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by smooth/projective model and field-embedding terminology did not find a declaration stating the entire item. PadicAlgCl.nonempty_ringHom_complex embeds a particular algebraic closure of a p-adic field, not every finitely generated characteristic-zero field, and cannot attach this item. Mathlib smooth-algebra descent concerns affine rings, not this global projective model.

## WANTED

None. The source used is locally present: literature/stacks-project/limits.tex, fields.tex and morphisms.tex, with tags checked in literature/stacks-project/tags/tags. The current blueprint is literature/blueprint/latest, snapshot main-20261024.

## Corrections and scope

The mathematical statement is unchanged. Its doubled TeX backslashes were normalized to single escapes, and the title now says “finitely generated field model” rather than the misleading “finite field model.” No statement dispute was found.

The original source only suggested the complex embedding argument; the delivered proof specifies a finite-generator induction and introduces a supporting lemma for a single generator. The new lemma is not a restatement of the item's embedding clause: it assumes a given embedding of an arbitrary countable field into an arbitrary uncountable algebraically closed field, permits arbitrary characteristic and nonalgebraic generators, and asserts extension of that specified embedding together with countability of the enlarged source. The item constructs its embedding by iterating this smaller result.

The blueprint creation chain is broken above this item: blueprint_refs.py ancestor reports None. I retained the existing null ancestor and full via chain rather than fabricating a blueprint id. I read the latest sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The field-model assertion is a subsidiary lemma of the inherited Hodge/Kodaira descendant branch, not something stated in the current direct-image paragraph itself. No chapter/unit route or unit record was edited.

## Search assessment

For the new lemma I ran LeanFinder with two phrasings, LeanSearch, Loogle and source grep using msearch.py. The returned algebraic-extension parametrization IntermediateField.algHomAdjoinIntegralEquiv (Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:600), its quotient presentation adjoinRootEquivAdjoin (:396), and RatFunc.algEquivOfTranscendental (Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:225) handle branches of the argument, but none gives the combination of extension of a specified embedding and countability for an arbitrary generator. I read those source statements, as well as mem_adjoin_simple_iff (:61). This is not a one-line specialization of any hit. The statement-only node therefore remains unsplit rather than being falsely labeled a Mathlib leaf.

Whole-DAG statement/title/source searches and blueprint_refs.py searches for “embedding,” “embedding extension,” “countable field,” “simple extension,” “09G1,” “01ZM,” and “projective model” found no existing statement of the new lemma. The existing minimal-polynomial node handles only its algebraic presentation. The existing countability-of-algebraic-elements lemma does not extend an embedding and does not cover transcendental simple extensions. The embedding-extension blueprint theorem concerns number-field subfields in a fixed p-adic algebraic closure, not an arbitrary simple extension of a countable field. Existing scheme-limit nodes are cited rather than duplicated.

## Not duplicates

lem-sfb-countable-simple-extension-embedding vs lem-weil-pbc-simple-algebraic-extension-power-basis: the latter uses 09G1 only for an algebraic extension's finite power basis; it neither assumes a countable base nor extends a prescribed embedding and excludes transcendental generators.
lem-sfb-countable-simple-extension-embedding vs lem-weil-pbc-minimal-polynomial-quotient-field-iso: the latter gives the quotient presentation in the algebraic case, not extension of a specified embedding in both cases or countability of a simple extension.
lem-sfb-countable-simple-extension-embedding vs lem-weil-pbc-algebraic-tower-triangular-relations: the latter gives finite triangular polynomial relations and linear independence for an integral tuple, not the countability/embedding extension theorem for an arbitrary generator.

## Argument reserved for the new statement-only node

This is explanatory report material, not a proof attached to the unsplit node. Stacks 09G1 (fields.tex, lemma-field-extension-generated-by-one-element) presents E(a) as E[T]/(P) in the algebraic case, and E(T) in the transcendental case. In either case every element is represented by a pair of polynomials over E, so it is countable: polynomials are finite lists over a countable set, and pairs of such lists are countable.

For algebraic a, choose a root b in Omega of the polynomial obtained by applying tau to the irreducible minimal polynomial P. Evaluation factors E[T]/(P) into Omega. The resulting unital map from a field is injective and agrees with tau on E. For transcendental a, the set of elements of Omega algebraic over tau(E) is countable: there are countably many nonzero polynomials, each has finitely many roots. Uncountability of Omega gives b transcendental over tau(E). Map p(a)/q(a) to tau(p)(b)/tau(q)(b). Transcendence ensures nonzero denominators remain nonzero, and the criterion p/q=p'/q' iff pq'=p'q proves well-definedness. The formula preserves field operations and constants. This explains precisely the two smaller branches the new node must eventually split; they are not assumed algebraic in the item's induction.

## Review by Q83

I checked the item against Limits tags 01ZM, 01ZP and 0C0C and their setup situation-descent-property. I read each cited node's statement; citations.json quotes those actual statements, not arguments hidden in their proofs. In particular, thm-pd-spreading-out contains both object descent and morphism descent, and the closed-immersion and smoothness nodes contain the local finite-type/presentation and qcqs hypotheses actually used.

Step 1 builds a small nonempty directed set of finite subsets of F. The union is the actual ring colimit by the displayed compatible-map argument, not just a union asserted to be a scheme limit. lem-weil-pbc-limit-affine-transition explicitly gives Spec of the ring colimit for affine stages, lem-weil-pbc-affine-scheme-qcqs supplies qcqs, and the affine-morphism definition applies directly to the two opens of a field spectrum. No algebraic or finite extension condition is imposed on F/k_A.

Step 2 uses exactly the H-projective convention of def-pc-projective-morphism. lem-pc-projective-proper gives properness, and def-weil-proper-morphism gives finite type and separatedness. def-sbc-smooth-morphisms gives local finite presentation, so the finite-presentation definition applies to X. For projective space, lemma-nagata-projective-space-base-change-proper gives properness; pqf-lem-lft-fp-locnoeth supplies local finite presentation. Its locally Noetherian base hypothesis is checked directly using the two possible ideals of a field and the affine-cover definition, cited as pqf-def-locnoeth and def-weil-pbc-noetherian-ring. This avoids a hidden blanket noetherianity assertion.

Step 3 applies both clauses (1) and (2) of thm-pd-spreading-out to finite-presentation objects over qcqs affine stages. The projective-space identification is supplied by lemma-nagata-projective-space-base-change-pullback, not by a definition of projective space alone. lem-weil-pbc-qcqs-morphism-permanence explicitly gives base-change preservation of finite presentation and qcqs of the source over a qcqs base. All sources and targets entering 01ZP/0C0C therefore satisfy their hypotheses.

Step 4 is a short elementary finite-type check, not a new node: restrict a finite-type affine chart by a principal open, add its inverse as one generator, then use the same generators over the larger coefficient ring B. The cited finite-type definition is precisely the affine-local condition it verifies. It does not assume a nonaffine overlap is affine.

Step 5 uses the full statement of lem-weil-pbc-descend-smooth-qcqs, which provides persistence at every later stage, so I first find a smooth stage and then apply lem-weil-pbc-descend-closed-immersion there. This avoids silently assuming the closed-immersion node itself asserts persistence. The morphism descended by 01ZP is the actual projective embedding, with qcqs source/target and local finite type verified in steps 3–4. The two desired properties occur on the same final model. Finite presentation retains quasi-compactness, so the convention “H-projective and quasi-compact” is met.

Step 6 has an explicit induction with a base case and induction hypotheses (both countability and a specified embedding). The new lemma is used only for one step E_j to E_j(b). lem-weil-complex-algebraically-closed states the required algebraic closedness, and lem-weil-complex-cardinality gives continuum cardinality; Cantor's diagonal argument supplies uncountability. Rational countability is justified by integer numerator/denominator representatives. No assertion that an arbitrary characteristic-zero F embeds in C is used.

Step 7 uses clause (2) of lem-pc-proper-base-change, which explicitly states smooth base-change stability, and lem-pc-projective-base-change, which explicitly uses the same projective convention. I checked morphisms.tex labels lemma-base-change-smooth (tag 01VB) and lemma-H-projective-base-change (tag 01WF); I corrected a preliminary incorrect smooth-base-change tag before writing this report.

For the new node I read fields.tex 09G1 in full, including both proof branches. Its hypotheses and notation are introduced within its own statement; its two definition dependencies define field extension and algebraic closedness. I tested a already in E, a algebraic but not separable (positive characteristic), and a transcendental, as well as finite and countably infinite E. There is no separability requirement: the target is algebraically closed, so repeated-root minimal polynomials still have a root. A countable target would invalidate the transcendental branch, which is why the uncountable hypothesis is explicit. I also checked the item for X empty, X disconnected, zero generators k=Q, and arbitrarily large F. No step chooses a point or assumes integrality or connectedness. All proof steps are below 2000 characters; no non-elementary subclaim was hidden inside a long step.

Against delivery-errors B–E: the new node carries a self-contained statement only; sources use checked tags/labels, TeX is escaped once, searches are actual logs, and same-tag nodes are distinguished above. The item uses existing nodes for every non-elementary descent and base-change input. Its proof is an assembly of object descent, arrow descent, property descent and finite-generator induction, not an application of a new node restating the item. The only new node is the strictly smaller one-generator embedding input. No cycle or library modification was introduced. Off-unit generic tools are declared in split_report.tool_uses for maintainer review, not written as accepted tool_uses.

## Unfinished work

The new supporting statement remains unsplit by the one-level stage-1 contract. No Lean was written and no compiler, Lake or build tool was run. Required server dry run and push results are recorded below when complete.

## Validation and delivery

The initial required deliver.py --no-push exited successfully: OK (not pushed), commit 7c0d946dcc4, preflight passed. The separate server review_split check also passed. A stray typographic backslash before the apostrophe in “Cantor's” was removed after this dry run; the final dry run below verifies the corrected artifact.
