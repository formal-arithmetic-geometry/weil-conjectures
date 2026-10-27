# Stage 1 report: lem-sfb-scheme-assassin-open-constructible

Group Q37, direct delivery, 2026-10-24. Only stage 1; no Lean files were written and no compiler, Lake or build was run. All worker writes are in this item's sandbox.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-assassin-open-constructible.json: item, split into seven steps following the affine part of Stacks 05KR. Statement unchanged; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-fibre-assassin-containment-base-change.json: statement, unsplit; Stacks 05KQ; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-generic-fibre-assassin-containment-spreads.json: statement, unsplit; Stacks 05KP; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-generic-fibre-assassin-noncontainment-spreads.json: statement, unsplit; Stacks 05KN; no Mathlib match.
- citations.json: 22 verbatim statement quotations, one for every citation in every item proof step. Full cited statements preserve all hypotheses and make the used clauses reviewable.
- report.md, searches.jsonl and search-result-*.json: review and actual search records. search-plan.json and write_split.py are sandbox working material, not delivery files; the delivered JSON includes the subsequent source-tag, affine-stability and prime-notation corrections.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, assassin, associated points and generic associated-point terminology found no declaration stating the item or any of the three new lemmas. The nearby depth/restriction declarations do not give fibre-assassin containment constructibility.

## WANTED

None. The Stacks sources used are present locally.

## Errors and corrections

The item is a correct affine specialization of Tag 05KR (more-morphisms.tex, lemma-relative-assassin-constructible). Its finite-presentation hypothesis includes quasi-separatedness, and its sheaf has an explicit local finite presentation. No statement change or STATEMENT-DISPUTED marking is needed. The imported proof was empty.

I followed the latest blueprint (COMMITS.txt: main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), reading sec-six-functors-basics/_section.md and sk-thm-sf-ctf-stability/_section.md and its proof. This auxiliary input belongs to the inherited direct-image/compactification chain through 0CXB, 0CX1 and 0CVV; it does not replace a unit step. tools/blueprint_refs.py ancestor returns None for this created-node chain, so the inherited null ancestor is retained and each new from.place names the precise 05KR subinput. The unit and chapter files were read and not edited.

The source-tag audit corrected a draft reference to 01IQ: reduced induced closed subschemes are 01J3 (lemma-reduced-closed-subscheme), with definition 01J4. The final item has 01J3. I also added the existing affine-morphism-permanence leaf to Step 2 so that stability of affine transitions is an explicit statement citation, not an uncited fact.

## Source error

The local proof of Tag 05KN (more-morphisms.tex, lemma-bad-case) is wrong, although its statement is the intended valid generic noncontainment theorem. It starts with the scheme-theoretic support Z of F and infers Z_eta intersect U_eta is empty from Ass(F_eta) not being contained in U_eta. Take Y=Spec(k), X=Spec(k times k), F=O_X and U the first component. The associated points are the two points, so the hypothesis holds, but Z_eta intersect U_eta is the nonempty first component. Its subsequent assertion that T_eta is empty is also false: T is the second component.

The correction for the future split of 05KN is to choose an associated point xi outside U and use the closure of xi, which is contained in the closed complement of U, rather than the entire support of F. Tag 05F1 (lemma-relative-assassin-in-neighbourhood, immediately preceding 05KN) gives a nonempty open in that closure whose fibre generic points are relative associated points. Its image contains the base generic point; the finite-type generic-image argument gives a nonempty base open in that image. On every fibre over that open there is therefore an associated point outside U. This explains the valid statement without reproducing the invalid support argument. The new 05KN node is statement-only and leaves this genuine propagation lemma to its subsequent worker; it has no fabricated proof. The item cites only its statement. No false source inference is used in the seven-step proof.

## Mathlib and duplicate searches

Before creating nodes I searched the entire DAG by title, associated-point/assassin terminology, and Tags 05KN, 05KP and 05KQ. I also ran blueprint_refs.py search for those three tags, 05KR, assassin, associated points, generic fibre, 01Z4 and 01ZR; I searched latest/blueprint for the same associated-point tags. None states a new lemma. Existing noetherian approximation, scheme/module/open descent, base-change permanence, prime/closed-scheme topology and constructibility nodes were reused.

For each new node msearch.py ran two distinct LeanFinder phrasings, Loogle, Mathlib grep and LeanSearch, all recorded with their exact query and output. The item was also searched and its earlier searches preserved. All services returned actual results. Semantic hits concern generic points, scheme fibres, dominant/open maps, Chevalley constructibility and associated primes of localized modules. In particular I read Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean: its IsLocalization and IsLocalizedModule hypotheses cover localization, not extension of a residue field or scheme-fibre base change. Loogle's associatedPrimes hits cover definitions, products, injective maps and primary quotients; none is 05KQ. The generic-spreading searches have no match. A supplementary recorded grep for associatedPrimes|Assassin|assassin in AlgebraicGeometry returned zero hits. Chevalley is not a one-line solution to the item's relative-assassin locus. The existing constructible-preimage leaf was checked at Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:172.

## Not duplicates

lem-sfb-fibre-assassin-containment-base-change vs lem-trf-relative-assassin-base-change: the existing 05DC statement characterizes whether a specified point upstairs is relatively associated, with a generic-component condition in a residue-field tensor fibre. The new 05KQ statement is an equivalence of universal containment in an arbitrary open on an entire fibre; its converse also needs existence of associated lifts. It neither repeats 05DC's pointwise characterization nor follows solely by substituting its variables.

lem-sfb-generic-fibre-assassin-containment-spreads vs lem-sfb-scheme-assassin-open-constructible: 05KP gives a nonempty base open of good fibres from the good generic fibre over an irreducible base, for finite type morphisms and sheaves. It does not assert constructibility on an arbitrary affine base, needs no finite-presentation hypothesis, and is one of two inputs to the irreducible-closed criterion.

lem-sfb-generic-fibre-assassin-noncontainment-spreads vs lem-sfb-scheme-assassin-open-constructible: 05KN instead propagates a bad generic fibre, also over an irreducible base and with finite type data. It supplies the other generic alternative; it does not restate the item's conclusion or a clause of it.

lem-sfb-fibre-assassin-containment-base-change vs lem-sfb-space-assassin-containment-constructible: the latter is the parent algebraic-space constructibility theorem, which already depends on the item; it cannot be used without a cycle. The new node is scheme-level invariance of an individual fibre condition, without constructibility.

No existing node has any of the three new source tags. The new nodes are genuine intermediate theorems, not elementary statements about finite intersections or notation. All elementary singleton-family, finite-generation, reindexing and inverse-image identifications remain within the item proof.

## Review by Q37

I read more-morphisms.tex 05KR in full and the statements and proofs of 05KQ, 05KP and 05KN. I checked their tag-to-label mapping in stacks-project/tags/tags. For the new 05KQ node I checked locally finite type of the scheme morphism, finite type of the quasi-coherent sheaf, arbitrary base change, the pulled-back open and module, and the two specified base points. For each generic-spreading node I checked finite type (not flatness), an irreducible base with its generic point, the good or bad generic condition and the nonempty-open conclusion. In particular no Noetherian or quasi-compact-open hypothesis was smuggled into these statements. I read the generic-flatness statement in algebra.tex as a check on 05KP's generality. The error in 05KN's proof is separated above from its valid statement.

For Step 1 I opened the affine inverse-system node, affine qcqs node, integer-polynomial Noetherianity leaf and finite-type-algebra Noetherianity leaf. Their statements give respectively the actual system and limit, the qcqs terms and the ring Noetherianity required later. The system is a set, directed and nonempty, not a large category. No assumption that the original A is Noetherian is used. Algebra 00FN and the n=0 polynomial statement justify the ring hypothesis, rather than inferring it from a definition.

For Step 2 I opened the finite-family descent, qcqs-morphism permanence, affine-morphism permanence and fibre-product-limit nodes. The singleton family is finitely presented as required. Permanence clause (3) gives finite presentation after base change and clause (2) gives qcqs total spaces over the affine bases; the separate affine-permanence statement supplies the transition property. The general fibre-product-limit statement applies to the constant T_i and B_i diagrams and the base diagram, whose limits exist. Constant-diagram limits here are checked directly from directedness, so no non-small limit is assumed.

For Step 3 I opened the quasi-compact morphism definition, the three-clause quasi-compact-open descent node and the module-map-descent node. The first gives quasi-compactness of H since B is affine; open descent applies to the qcqs T_j system. Clause (1) of the module node explicitly supplies a quasi-coherent, finitely presented module and its pullback isomorphism, not merely an abstract sheaf or a statement about morphisms. Its Noetherian affine base rings were proved in Step 1. Descending H before F avoids needing finite-presentation preservation while advancing an already chosen module model. The new H_i need not be relatively quasi-compact for the later generic lemmas.

For Step 4 I checked the complete new 05KQ statement against the actual model. Finite presentation gives finite type of the morphism and the sheaf; p_i is allowed to be arbitrary. The pointwise equivalences give E=p_i inverse-image(E_i), not just an inclusion. No surjectivity of the approximation projection is assumed.

For Step 5 I opened the prime/irreducible-closed correspondence and reduced-induced-closed-subscheme nodes. Their statements give V(p), the actual Spec(A_i/p) scheme, and the generic-point closure formula. I read algebra.tex 00ES and schemes.tex 01J3 for those claims. The qcqs-permanence node and the two separate module-pullback statements supply finite presentation and quasi-coherence of the restricted data. I read modules.tex 01BG and 01BQ to check that neither needs flatness. Applying 05KQ again gives the exact restricted locus, so the base used by the generic lemmas is the correct irreducible scheme, not just an unstructured subset.

For Step 6 I checked the good and bad generic hypotheses separately and used precisely the conclusions of 05KP and 05KN. I opened the noetherian-constructible-subset-criterion node: its statement asks for a nonempty relatively open subset wholly inside or wholly outside E for every irreducible closed subset, and for a finite affine cover by Noetherian rings. Steps 1 and 5 supply exactly these hypotheses. The single chart B_i suffices. I read topology.tex 053Z as the criterion's source. This step proves constructibility; it does not use the constructibility of the entire relative assassin as an uncited theorem.

For Step 7 I opened the constructible-preimage leaf and checked its arbitrary-scheme-morphism statement and the source declaration. It applies to p_i without quasi-compactness or finite type. Together with Step 4 it gives the target set, and no topological form of 'locally constructible implies constructible' needs to be silently added.

Small cases: B empty gives E empty; T empty or F=0 gives all of B; H=T gives all of B; H empty makes the condition the absence of associated points in each fibre and is preserved by 05KQ. A singleton approximation system and identity base change do nothing. A nonreduced irreducible closed subset is replaced by its reduced induced structure, whose underlying subset is unchanged; 05KQ handles the fibres. The two-point X example distinguishes bad generic containment from total-support disjointness. Neither generic lemma requires the original base to be Noetherian. I found no false statement among the new nodes.

All non-elementary facts used in the proof are explicit node citations; the verbatim quotations were regenerated after the final citation edits. The proof-dependency list is exactly the union of step uses. No step exceeds 2000 characters. New nodes have no proof or proof dependencies; no node restates constructibility, and no edge points back to the parent. Off-unit non-leaf auxiliary citations are declared with their specific uses in split_report.tool_uses: they are general approximation, module, topology or permanence tools and preserve the inherited unit route. No maintainer-owned metadata was changed.

## Validation

The initial server review_split check passed. The first full deliver.py --no-push exited successfully with preflight passed at c33f7e6048f. A final tag-index check then corrected two reference-only typos: 01YZ for lemma-scheme-over-limit and 05F1 for lemma-relative-assassin-in-neighbourhood. The final dry run is rerun on those corrected files before pushing.

## What remains

The three new statement-only inputs deliberately remain unsplit for future stage 1 work. Nothing else in the assigned item is left incomplete. Delivery checks and commit are recorded by the delivery tool.
