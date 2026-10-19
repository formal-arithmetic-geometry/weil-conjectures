# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-complete-base-algebraic-dualizing-existence.json`: split, seven proof steps, original statement and statement dependencies retained.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-algebraic-dualizing-polynomial.json`: new statement-only node, Stacks 0A7J; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-algebraic-dualizing-localization.json`: new statement-only node, Stacks 0A7G; no Mathlib match.
- `citations.json`: a verbatim statement quotation for each of the 17 step/node citations.

## Attachments

None. Searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag, algebraic dualizing, dualizing complexes, polynomial preservation and localization preservation. The results concern etale/pro-etale dualizing objects, not ordinary algebraic dualizing complexes. No project declaration supplies the item or either new node. The upstream master was also searched as reference material, without treating its sorry declarations as finished proofs.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## What was wrong or incomplete

The item was an unsplit, true existence statement citing Stacks 0BFR (2),(5). Its original searches were retained. The new Q74 searches are recorded by msearch.py in searches.jsonl; I read the returned signatures. They give ordinary polynomial-module tensor equivalences, cotangent spaces, flat ring maps, numerical injective-dimension bounds, or generic localization-preservation predicates, not the algebraic-dualizing assertions. A second semantic phrasing was run for the item and each new node, together with Loogle, LeanSearch and grep. Nothing was declared a Mathlib leaf merely because a related notion was returned.

There is no statement dispute or change. In particular the word “normalized” in the definition node's identifier does not impose normalization in this item: that node explicitly defines the global algebraic-dualizing predicate before giving the extra local normalization predicate. No locality of A, excellence of C, Cohen–Macaulay assumption or dimension hypothesis was added.

The existing complete-local coherent-duality node was inspected, but its statement supplies an anti-equivalence, not explicitly a bounded injective representative of its dualizing object. I do not extract that property from its proof. Instead I use the existing Cohen-presentation, regular-local bounded-injective and finite-map-transfer statements directly. Likewise the existing normalized-local quotient lemma cannot be applied to the possibly nonlocal polynomial quotient; the general finite-map-transfer theorem is used.

The chapter and unit records were read. This is a supporting commutative-algebra input below the ancestor's existing surface-resolution branch, not the unit's statement node; no realization fields or chapter/unit routes are changed. The three non-Mathlib facts from other units are explicitly declared as generic tools in split_report.tool_uses.

## Unfinished work

None for this one-level stage-1 split. The two new nodes intentionally have statements only and remain unsplit. No Lean was written, and no compiler, Lake or build was run.

## Not duplicates

lem-per-algebraic-dualizing-localization vs lem-per-normal-surface-canonical-module: the latter cites 0A7G in its source, but its statement concerns canonical modules on normal two-dimensional local domains and proper birational surfaces. It does not state preservation of arbitrary algebraic dualizing complexes under arbitrary multiplicative localization.

lem-per-algebraic-dualizing-localization vs lem-per-algebraic-dualizing-generic-degree: 0A7G occurs in the latter's reviewed proof discussion, but its statement is a nonvanishing criterion at minimal primes for a normalized local dualizing complex. It does not supply the general localization theorem.

No existing node has 0A7J in its source or states polynomial preservation of an algebraic dualizing complex. The existing lem-trf-finite-map-dualizing-transfer concerns finite ring maps: R to R[t] is not a finite module map for nonzero R, so it does not subsume this new node. The coherent-relative-dualizing and smooth-etale dualizing nodes concern different predicates.

Searches included whole-DAG Stacks tags 0A7G/0A7J, dualizing-polynomial/dualizing-localize labels, polynomial/localization/complete-dualizing keywords, and blueprint_refs.py searches for “dualizing complex”, “algebraic dualizing”, “dualizing polynomial”, “dualizing localization”, “dualizing localize”, “Polynomial extension” and “Localization of dualizing”. None of the blueprint nodes states either new lemma. The new ids did not exist. Both inherit the confirmed ancestor lem-per-artin-gabber-affine-curve with the item prepended to the existing via chain.

## Review by Q74

I read dualizing.tex, lemma-ubiquity-dualizing (0BFR), including its proof, and the three preservation lemmas used by proposition-dualizing-essentially-finite-type (0A7K): polynomial 0A7J, quotient 0A7I and localization 0A7G. I checked the labels against tags/tags. I also read the Cohen structure theorem 032A in algebra.tex and the regular-Gorenstein proof 0AWX in dualizing.tex. The item's complete Noetherian local base and arbitrary localization of a finite type algebra are exactly cases (2) and (5) of 0BFR. Neither base field nor equicharacteristic is assumed.

For the new polynomial node, 0A7J states precisely that tensoring an algebraic dualizing complex with R[t] is dualizing. I wrote scalar extension term by term, with the differential specified, so that no unidentified derived coefficient functor is needed. Its definition dependencies supply Noetherian rings, polynomial rings, the three dualizing conditions, and ordinary tensor/change of rings on the one-object ringed site. For the new localization node, 0A7G applies to every multiplicative subset, with no nonzero-localization hypothesis. Termwise localization is exactly the source construction. Both new nodes are statements without hidden proof sketches, proof dependencies or proof origins; neither simply renames existence over the complete base.

I opened each cited node's statement. In Step 1 the finite-type definition expressly supplies a finite polynomial surjection; the module-localization definition supplies the multiplicative-set localization. Choosing these presentations is elementary. Step 2 uses the Cohen-presentation statement's surjective local map from a complete Noetherian regular local ring and then exactly the bounded-injective representative in the regular-local node's statement. Maximal-ideal completeness matches the given adic-completion definition.

In Step 3 the K-injective node states that a bounded-below injective complex is K-injective, so the bounded representative meets its hypotheses. The internal-Hom and Hom-complex statements give its model and differential. Evaluation at 1 and its written inverse commute with those differentials. The scalar map corresponds to the quasi-isomorphism representing R[0], not an unspecified isomorphism of objects. Finite cohomology is the cyclic degree-zero module. This is a short explicit verification of the dualizing definition, not a new lemma.

In Step 4 the general finite-map-transfer statement supplies all three conditions, including the B-action, without normalization. The map R to C is surjective and C is cyclic as an R-module; both rings are Noetherian. In Step 5 the finite-type-Noetherian node states exactly that a finite type algebra over a Noetherian ring is Noetherian. I use it at each polynomial stage. The new polynomial statement takes the already constructed representative, so induction has an explicit base, inductive claim and step, including n=0. This does not rely on associativity of several derived scalar functors: successive termwise extensions themselves define the representatives.

In Step 6 the same Noetherian theorem applies to B over C, and the polynomial quotient is cyclic as a P-module. The finite-map theorem is therefore applicable even when B is nonlocal or zero. Its conclusion is read through the global definition, not through the normalized quotient lemma. In Step 7 the new localization statement has exactly the Noetherian B and multiplicative subset already chosen. I also wrote the ideal-contraction argument establishing Noetherianity of A, directly from the Noetherian definition; it is a few-line elementary observation inside the application step, not a separate node.

I tested the new statements with R a field and K=R[0], with a shift K=R[3], with an Artinian nonregular ring admitting a dualizing complex, with R=0, and with multiplicative subsets {1}, powers of a zero divisor, and subsets containing 0. Polynomial preservation does not claim normalization (for a one-variable local polynomial ring a normalized choice may require a shift). Localization at 0 gives the zero ring and zero complex; scalar action is 0 to 0, an isomorphism. The item also covers n=0, B=C, B=0, and A=0. No field characteristic is excluded by the Cohen-ring presentation. All seven steps are under 1000 characters, hence no long step conceals an unextracted lemma.

The review against delivery-errors B–E corrected two tempting but invalid citations before writing: I did not infer finite injective dimension from the complete-local anti-equivalence node's statement, and I did not use normalized quotient transfer for a nonlocal quotient. Existing finite-map transfer was reused instead of adding a duplicate quotient node. Every citation has its actual statement in citations.json, with no quotation invented to fit a step. No SGA source is used.
