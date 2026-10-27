# Stage-1 delivery: lem-sfb-normalization-affine-total-fractions

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normalization-affine-total-fractions.json: item, statement, split; no exact Mathlib match. The original statement and all its historical searches are retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-weakass-minimal.json: new statement-only lemma, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and source grep, including a second semantic formulation. This is the only new node; there are no new Mathlib leaves.
- citations.json: every step/node citation, with its exact statement as the verbatim quote.

## Attachments

None. Searched lean/WeilConjectures for the item id, total fractions/quotients, componentwise normalization and affine normalization. The reduced-Noetherian total-fraction declarations impose Noetherianity, and the Artinian relative-normalization chart declaration concerns a supplied relative normalization, not this absolute componentwise normalization. No exact project attachment was found. The Mathlib normalization sources recorded in the inherited searches were read at Normalization.lean:46-74, 184-190 and 259-266: those concern relative normalization in a supplied qcqs morphism. Identification with this componentwise normalization requires a genuine argument.

## WANTED

None. All sources used are available locally. No SGA source is used.

## Audit of the imported item and route

The item's statement is correct; no statement change or STATEMENT-DISPUTED is needed. Its proof was empty. In particular, the existing reduced-Noetherian total-fraction decomposition and locally Noetherian componentwise chart lemma cannot be applied under the item's weaker hypotheses. Instead I use the existing generic-residue affine charts and the existing total-quotient decomposition whose actual hypothesis is that all weakly associated primes are minimal. Stacks 0EMA supplies that hypothesis from reducedness, and is the only new node needed.

The chapter and unit records were read. This is an auxiliary normalization calculation on the existing alteration/nodal-model route underlying direct images, not the unit's key statement. Neither the unit nor chapter is changed. The four generic tools from other units are declared individually in split_report.tool_uses: components/minimal primes, total fractions, minimal-prime localizations, and affine stalk localization. These implement the recorded normalization calculation without replacing the unit's route.

The ancestry tool reports blueprint.from.node = None for this inherited chain; I preserve that result and the complete existing via chain rather than invent an imported ancestor. The new lemma has the item prepended to via and an explicit place explaining the weakly-associated-prime hypothesis. Whole-blueprint searches for normalization, total ring of fractions, generic residue, 02LX, weakly associated and 0EMA found no statement duplicating the new lemma. The item's same_as remains empty.

## Not duplicates

lem-sfb-reduced-weakass-minimal vs lem-sc-affine-totalquotient-minimal-product: the new node identifies weakly associated primes of any reduced ring; the existing node assumes that identification and proves a total-quotient product decomposition. Neither restates the other.

lem-sfb-reduced-weakass-minimal vs lem-weil-pbc-reduced-zerodivisors-union-minimal-primes: the existing node identifies the union of minimal primes with the zerodivisors, not the individual primes minimal over element annihilators. The new node is what the existing total-quotient theorem's statement actually asks for.

lem-sfb-reduced-weakass-minimal vs lem-weil-pbc-reduced-noetherian-total-ring-fractions: the latter is a product decomposition under a Noetherian hypothesis, not the general weakly associated prime assertion. No existing node cites Tag 0EMA in its source or statement.

## Review by Q152

I read Morphisms, Tag 035P (lemma-description-normalization), statement and proof of parts (1), (2), (4), and Tag 0CDV (lemma-normalization-in-terms-of-components). They give exactly the route used here: finite components give finite minimal primes; total fractions become the product of the fields at those primes; integral closure in that product supplies the normalization chart. I also read Algebra Tags 02LX (lemma-total-ring-fractions-no-embedded-points), 00EU (lemma-minimal-prime-reduced-ring), 00ES (lemma-irreducible), the adjacent reduced-ring discussion, and Schemes Tag 01HV (lemma-spec-sheaves), especially (1) and (6).

For the new lemma I read Algebra Tag 0EMA (lemma-reduced-weakly-ass-minimal), including its proof. It applies to any reduced ring and has no finiteness assumption. Its argument localizes at a weakly associated prime: in the reduced local ring an element whose annihilator has maximal-ideal radical must be a unit, since otherwise it is in that radical and some positive power is zero. Consequently the maximal ideal is zero and the prime was minimal. Conversely every minimal prime is minimal over Ann(1)=0. This argument is source material for the future split and is not hidden inside the new node's statement or proof fields.

In step 1, I opened the full statements of def-pc-reduced-scheme, lem-sfb-normalization-generic-residue-affine-charts and lem-weil-pbc-spec-irreducible-components-minimal-primes. Reducedness of sections is explicit in the first. The chart lemma explicitly gives a finite set of component generic points under exactly the quasi-compact-open assumption of this item; the spectrum lemma says the components are precisely V(p) for minimal p. The elementary closure relation for prime points identifies the two finite indexing sets. Thus I do not sneak a Noetherian finiteness theorem into this step.

In step 2, the new lemma gives precisely the weakly associated prime condition of lem-sc-affine-totalquotient-minimal-product. I read that existing node's statement in full, not only its proof: it explicitly permits an arbitrary commutative ring with finitely many minimal primes, and gives the canonical fraction map into their localizations. This is stronger than merely an abstract ring isomorphism and fixes compatibility with A. Its hypotheses are verified in step 1 and by 0EMA.

In step 3, I read the statements of lem-weil-pbc-minimal-prime-reduced-localization-field, lem-weil-pbc-affine-open-stalk-localization and def-weil-residue-field. The first gives both fieldness and vanishing of the extended minimal prime for a reduced ring. The second gives an isomorphism with the actual ambient stalk, with the explicit germ/fraction formula. The residue-field definition then takes the quotient by the zero maximal ideal. This proves that the map from A into the product is the tuple of germs followed by residue classes, exactly the algebra structure in the chart lemma; no unnamed comparison theorem is used.

In step 4, I reopened the generic-residue chart statement: it gives an isomorphism over U, with its structural ring map explicitly specified. I checked integrality by applying e and its inverse to the full monic polynomial equation, using def-weil-pbc-integral-closure, so the restriction to integral closures is justified in both directions. Contravariance and functoriality are in def-weil-affine-spectrum. The resulting map on A is explicitly a -> a/1. This assembly is elementary relative to its cited statements, rather than a new normalization lemma or a clause restatement.

In step 5, I used the exact empty-case clause of the chart lemma. The sheaf axiom gives A=0; localization preserves 0=1, and a subring of that ring is again the zero ring, whose spectrum has no prime ideals. All zero-ring conventions agree. I also tested the new lemma on a field, a product of two fields, and the reduced crossing ring k[x,y]/(xy); it asserts exactly their minimal primes, without requiring irreducibility or normality. The zero ring has no prime ideals, so both sides of the new lemma's equality are empty. A non-Noetherian domain still has only the minimal prime (0), so the assertions do not use hidden Noetherianity.

Against delivery-errors B--E: the new node is self-contained and statement-only, with reducedness, annihilators and minimality all defined inline; its source uses the verified Stacks tag and label; its searches are copied from the actual command log and their hits were read. Mathlib's radical-annihilator IsAssociatedPrime is not silently equated with all primes minimal over annihilators in a non-Noetherian ring. No citation takes more than its node's statement says, no definition is cited for a theorem, and all non-elementary facts have nodes. The only new node is a general algebra prerequisite, not an affine-normalization clause. Each proof step is shorter than 2000 characters; the fraction and integral-closure comparisons and structural equation are written explicitly. I have made no edits outside the sandbox and run no Lean compiler or Lake command.

## Unfinished work

None for this one-level split. The new lemma remains intentionally unsplit for the subsequent stage-1 queue, as required. Delivery validation follows below.

## Validation

The first server preflight required at least one notion reference in the new node. I added the existing element-annihilator definition reference def-weil-pbc-annihilator-associated-primes, explicitly specialized to M=R, while retaining the full inline formula. Its exact-annihilator associated-prime predicate is not identified with weak association: the new statement still separately defines weak association by minimality over that annihilator. I read that definition node and added it to stmt_deps; the corresponding verbatim citation quote was refreshed.


## Repair of returned delivery 46ea0f3abd8

The 2026-10-23 return approved the mathematics and refused the landing because the side completion had not been promoted into the live DAG. I retained the returned sandbox proof, its one new node, report, citations and all logged searches. The required initial dry run completed successfully at 45b54b9a264 against the delivery tool's freshly fetched current server base. This is evidence of packaging and preflight only; it is not a claim that the maintainer has promoted the completion.

I compared the retained item against the current shared DAG: its statement, statement dependencies, source, blueprint ancestry and historical searches agree; the differences are exactly the completed proof, proof dependencies, proof origin, split status and split report. I reconstructed the sandbox item from the current node with only these stage-1 fields overlaid, retaining current metadata. The delivery tool rebases the actual commit onto freshly fetched origin/sheaf-dag and preserves maintainer-owned fields. No git command was run in the shared repository.

I reopened every current proof dependency and each statement dependency. Every full-statement quote retained in citations.json is still exactly the corresponding current statement, rather than merely a surviving substring. Thus no changed cited statement requires a new hypothesis or replacement node. In particular the total-quotient theorem still assumes finite minimal primes and weak association, not Noetherianity; the generic-residue chart still provides the canonical structural map; the affine stalk comparison still gives the explicit fraction-to-germ formula. The new node is still absent from the shared DAG. The current Tag 0EMA keyword hit in the vertical-principal-ideal fibre-detection proof is not a node stating weak association equals minimality, so it supplies no duplicate to reuse.

On rereading Algebra's lemma-irreducible and the tags table, I corrected the inherited reference in step 1 and this report from 00ER to 00ES. The cited existing spectrum-components node already carries the correct 00ES source. The actual statement and argument are unchanged. I also re-read Morphisms 035P and 0CDV and Algebra 0EMA, 02LX and 00EU, and checked the retained Mathlib hits in Normalization.lean, AssociatedPrime/Basic.lean and MinimalPrime/Basic.lean. These still do not give an exact project attachment or a one-line Mathlib specialization. No search question or statement changed, so the recorded searches were reused rather than invented or repeated.

The Review by Q152 above remains my source and hypothesis review for this repair: steps 1--3 cite exactly the reducedness, component/minimal-prime, weak-association, fraction-product and stalk statements read again here; step 4 writes both directions of transport of the monic equation and the structural map; step 5 handles the zero ring. The longest non-elementary step is below 2000 characters. I preserved the one statement-only algebra prerequisite and made no Lean, unit, chapter, shared-repository or launcher edits. A final dry run and push of this repaired report and corrected source follow.
