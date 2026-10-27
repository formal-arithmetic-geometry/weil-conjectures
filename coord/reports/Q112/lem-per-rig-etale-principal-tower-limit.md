# Stage 1 report — Q112

Item: lem-per-rig-etale-principal-tower-limit. Date: 2026-10-24.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-rig-etale-principal-tower-limit.json: statement, split; statement unchanged; six proof steps; no new nodes and no new Mathlib leaves.
- citations.json: eleven verbatim statement quotations, one for every step/node citation.
- report.md: this report. searches.jsonl retains the genuine msearch results. write_split.py is a sandbox-only preparation script, not a DAG delivery file.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by principal towers, quotient towers, and topological finite type. No declaration there states the complete item. The existing completion-Noetherian theorem was read in WeilConjectures/RingTheory/AdicCompletionNoetherian.lean; it is only a component, already represented by its existing node.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Findings and changes

The original item had a valid statement but no proof. I retained its statement, statement dependencies, original citations and earlier search records. There was no earlier sandbox split or report and no repair note. Fresh msearch runs use two semantic phrasings, Loogle, LeanSearch, and source grep; completion structures, flatness, evaluation maps, finite-type Noetherianity and Weierstrass results do not give the entire statement. The source grep identified the complete-source surjectivity criterion, whose actual signature was read, and a DAG search found its existing node.

The Stacks argument uses the general module theorem 09B8. The DAG already has exactly that theorem as lem-pod-adic-tower-reconstruction; it applies to arbitrary modules and does not require module finiteness. In particular, the finite type algebras here need not be finite A-modules. I reused it instead of creating a new ring-tower node. The completed evaluation is constructed coordinatewise, its surjectivity uses the existing complete-source criterion, and Noetherianity uses three existing nodes. No argument was moved into a new node.

The latest blueprint ancestor and unit were read from literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/. The ancestor has the perverse/duality argument and no separate formal-algebraization sentence. The inherited provenance of this auxiliary ring lemma is through lem-per-rig-etale-principal-reduction and its local-duality algebraization branch. The split_report says this explicitly and does not claim that the current ancestor directly states this ring theorem. No chapter or unit field is changed. Generic off-unit inputs are declared in split_report.tool_uses, as required by the later tool-use rule.

## Not duplicates

No new nodes. DAG searches for 0AJP, 0AJQ, 09B8, completed polynomial presentations, completion Noetherianity and complete-source surjectivity located the existing supporting nodes. Blueprint searches for topologically finite type, completed polynomial, adic tower, 09B8 and 0316 produced no alternative blueprint statement for the item. lem-per-principal-formal-coefficient-presentation was read: it lifts a characteristic-zero residue coefficient field under quite different hypotheses, so is not a general quotient-tower reconstruction theorem. No duplicate is introduced.

## Review by Q112

I read Stacks restricted.tex, equation-C and equation-C-prime, the full statement and proof of 0AJP (lemma-topologically-finite-type), and the statement and proof of 0AJQ (lemma-topologically-finite-type-Noetherian). I also read algebra.tex, 09B8 (lemma-limit-complete), 0315 (lemma-completion-generalities), 0316 (lemma-completion-Noetherian-Noetherian), and 00FN (lemma-Noetherian-permanence). There are no new-node sources to audit.

For Step 1 I opened lem-pod-adic-tower-reconstruction and checked that its statement gives both the quotient identifications and completeness/separatedness for arbitrary A/I^m-modules with precisely our transition hypothesis. I=(a) is finitely generated regardless of whether a is zero, nilpotent or a zero divisor. C_m has the required module structure because it is an A/(a^m)-algebra. The extra ring and A-algebra compatibility is proved by the actual coordinate projections, not inferred from an abstract module isomorphism. The cited completion definition explicitly gives componentwise operations.

For Step 2 I opened both the finite type and multivariate polynomial definition nodes. Their statements give a finite generator list and the evaluation universal property. The lifts exist by Step 1. Surjectivity onto the closed fibre follows by lifting the finitely many coefficients of each polynomial; no Nakayama theorem or unproved finiteness implication is used here.

For Step 3 I checked again the full statement of the module theorem, this time over the ring R=A[z_1,...,z_q], with its principal ideal aR and its actual quotient modules. Quotienting R/a^(m+1)R by a^m gives R/a^mR. The completion definition supplies P as compatible residue sequences. The maps e_m and their compatibility are written out. Completeness of F supplies the element with those coordinates, and injectivity of the comparison to its completion checks preservation of sums, products, constants and one. This is the routine inverse-limit construction, not a hidden comparison theorem.

For Step 4 I read the statement of lem-weil-pbc-complete-source-surjective-mod-ideal and Mathlib/RingTheory/AdicCompletion/Functoriality.lean:447–459. It needs precompleteness only in the source, Hausdorffness for the image ideal in the target, and surjectivity after taking that quotient. Step 3 supplies completeness of P for aP, Step 1 supplies separatedness of F, the image ideal is aF because phi preserves a, and the polynomial map of Step 2 factors through P. Thus every hypothesis is checked. The criterion does not require the source or target to be local and does not require a nonzerodivisor.

Step 5 is elementary: the kernel quotient map is defined, its well-definedness, injectivity and surjectivity are all checked. It uses the already constructed phi rather than a new theorem. Step 6 cites the statements of finite-type-algebra-noetherian, adic-completion-noetherian, and surjective-image-noetherian, each of which I opened. They respectively apply to R over the given Noetherian A, P as the completion of that Noetherian R at any ideal, and the surjection P to F. No Noetherian hypothesis on F is assumed earlier. The completion-Noetherian result is not used to assert anything about an arbitrary inverse limit.

Against delivery-errors B–E: no new statement-only nodes, no new notation requiring a missing definition, no fabricated searches, no new duplicate, no node that merely restates a clause, and no source-only citation standing in for a proof. Every non-elementary input is a cited node and every citation has its complete statement quoted verbatim in citations.json. The dependency closure of every cited theorem was searched and does not reach this item, so there is no introduced cycle. Each proof step is below 2000 characters. Off-unit inputs are generic algebra tools and declared as such; no unit route is replaced.

I tested the statement and arguments on a=0 (the tower is constant up to its transition isomorphisms and F is a finite type quotient of ordinary polynomials), a a unit (all C_m and F are the zero ring), nilpotent a (eventual stabilization), and a zero divisor (no cancellation is used). The zero algebra and q=0 are allowed throughout. For noncomplete A, for example A=Z and a=p, P is the actual a-adic completion of A[z], not a formal power-series ring over an assumed complete coefficient ring. The item does not assume A complete, injective transition maps, finite A-module rank, or a nonzero ring. No statement dispute or source error was found.

## Unfinished work

None in this split. Existing supporting unsplit proof obligations remain their own DAG items; this delivery creates none.
