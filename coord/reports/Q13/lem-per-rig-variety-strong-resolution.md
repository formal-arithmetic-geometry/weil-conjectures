# Worker report

Group Q13; item lem-per-rig-variety-strong-resolution; stage 1; 2026-10-24.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-rig-variety-strong-resolution.json: statement retained, split into twelve assembly steps.
- dag/nodes/sec-deligne-laumon-a1/lem-per-generically-reduced-rational-invariant-calculus.json: statement-only input, unsplit; no Mathlib match. A local invariant/marked-ideal calculus, including embedded nilpotents, not the global theorem.
- dag/nodes/sec-deligne-laumon-a1/lem-per-variety-rational-smooth-limit-models.json: statement-only input, unsplit; no Mathlib match. Rational approximation and smooth finite-stage lifting, with no resolution assertion.
- citations.json: one verbatim statement excerpt for each step/node citation.
- report.md. searches.jsonl contains the actual wrapper search records. No Lean written or compiled.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag, desingularization, strong resolution, and geometric blowup terminology; no complete project declaration states this item. Existing smooth-limit descent declarations are different theorems. No compiler or git command was run in the shared repository.

## Literature wanted

WANTED: Temkin, Non-embedded desingularization of quasi-excellent schemes in characteristic zero: the strong case, arXiv:0904.1592v2, §§2.3.1--2.3.4 and Theorem 2.3.5, pp.11--14, for lem-per-rig-variety-strong-resolution. Read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf; no download to the repository.

WANTED: Bierstone--Milman--Temkin, Q-universal desingularization, arXiv:0905.3580v1, Theorem/Addendum 6.1, §§6.1--6.3 and §§7.2--7.5, pp.12--21, for both new nodes and the assembly proof. Read the primary PDF online at https://arxiv.org/pdf/0905.3580. The JSON's literature/bierstone-milman-temkin/Q-universal-desingularization.pdf is a requested archival location, not a claim that the file exists.

WANTED: Bierstone--Milman, Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant, Invent. Math. 128 (1997), Chapters II--III, and Functoriality in resolution of singularities, Publ. RIMS 44 (2008), §7, for the later split of lem-per-generically-reduced-rational-invariant-calculus. BMT §§6.1--6.3 explain the construction and dimension correction, and reference these fuller constructions; this delivery does not claim to have split that input.

## Corrections and limitations

The item's imported statement is faithful to Temkin; no STATEMENT-DISPUTED correction was needed. It means generically reduced, not reduced, and regular maps without any chosen-field compatibility. The already existing reduced-only rational algorithms cannot discharge it. Two temporary exploratory factorization/invariance drafts were removed before delivery; neither is a dependency or a delivered node. The final proof uses the approximation route explicitly offered by BMT §7 and Temkin's introduction, rather than assuming compatible coefficient fields.

I corrected a tempting truncation argument: stopping a resolution at the first globally regular stage need not commute with an open restriction. The new calculus allows the original-singular-locus-supported exceptional cleanup in Theorem 6.1. It requires only that an exhausted history is regular; it does not assert that every regular point has the inactive value at every transformed history. I also corrected cover independence to use a genuine common finite affine refinement of the intersections, with surjective maps to both covers; there is no presumed projection between unrelated covers.

No unit realization fields are changed: this is a supporting node of the existing regular-resolution branch for the ancestor's duality step, not the key Fourier/perverse target. The latest blueprint ancestor and its proof were read, and the from/via chain is retained. Generic blowup, ideal gluing and commutative-algebra citations from other units are explicitly declared as tool uses.

## Not duplicates

lem-per-generically-reduced-rational-invariant-calculus vs lem-trf-hilbert-samuel-resolution-invariant-calculus: the existing calculus assumes reduced input, forces its inactive value exactly at current regular points, and excludes cleanup. The new local input permits generically reduced schemes with embedded nilpotents and retains original-singularity-supported cleanup. It is needed before the arbitrary-field and regular-map extension.

lem-per-generically-reduced-rational-invariant-calculus vs lem-trf-embedded-resolution-ambient-comparison: the existing algorithm assumes reduced schemes and stops when regular. The new node concerns local functions/strata on finite histories, including nonreduced inputs; it does not assert the global variety theorem.

lem-per-generically-reduced-rational-invariant-calculus vs lem-trf-normalized-resolution-word-gluing: that word-gluing theorem is expressly for reduced schemes and gives no nonreduced center construction or termination.

lem-per-generically-reduced-rational-invariant-calculus vs lem-trf-resolution-word-maximum-center-descent: that theorem assumes reduced current transforms and proves a maximum-center assertion for the particular reduced-only word assignment, not the calculus for generically reduced schemes.

lem-per-generically-reduced-rational-invariant-calculus vs lem-trf-smooth-functorial-ordinary-resolution: that global rational algorithm is reduced-only; it is not an algorithm on the item's larger category.

lem-per-generically-reduced-rational-invariant-calculus vs def-trf-hilbert-samuel-presentation: the existing node defines marked data/test conditions and explicitly supplies no existence or resolution assertion.

lem-per-variety-rational-smooth-limit-models vs prop-nagata-noetherian-inverse-system: the existing approximation has affine transitions, not smooth transitions or regular projections, and does not lift arbitrary regular maps to smooth finite-stage maps. Ordinary Noetherian approximation cannot be substituted here.

lem-per-variety-rational-smooth-limit-models vs lem-per-rig-variety-strong-resolution: the new node has no blowup, center, or resolution conclusion. The item still constructs and compares all towers.

The whole DAG and blueprint were searched for desingularization/resolution, Hilbert--Samuel, smooth affine transitions and inverse limits. The geometric reduced-calculus hits above were read. Most inverse-limit blueprint hits concern coefficients and are unrelated. Lean SmoothLimit.lean descends smooth finite-presentation schemes over a given limit; it supplies neither these models nor a regular-map comparison. Mathlib AffineTransitionLimit.lean:690 is equality descent of existing morphisms, and Smooth/NoetherianDescent.lean:268 spreads an already smooth algebra, so neither is a one-line specialization giving the model lemma. Every Mathlib search recorded on new nodes was run with msearch.py and its results read; both node questions were tried with a second natural-language formulation. Invalid Loogle queries in preserved historical searches are not evidence of absence; valid quoted substring queries were also run.

## Review by Q13

I read Temkin's definitions of a strong original-singularity-supported contracted tower, compatibility with regular morphisms, and the finite-disjoint-union synchronization arguments (Lemmas 2.3.1 and 2.3.3). This fixes what the item's ordered centers must mean. I read BMT Theorem/Addendum 6.1 and §§6.1--6.3 for the first new node: the Hilbert--Samuel presentations and marked-ideal process, comparison after adding smooth factors, correction for nonconstant relative dimension, and the distinction between initial-singularity support and current singularity. The new calculus is a genuine local technical input, left unsplit. It is not an invocation of a new node restating FVar. For the second new node I read Definition 7.2, both smooth-locus factorizations in the proof of 7.4, and the schematic-image and flattening construction in 7.5. The directed systems are small, nonempty and affine, and the limits Noetherian. The generically reduced refinement retains the scheme structure rather than reducing: flat schematically dominant projections meet the generic components, and generic reducedness descends there; it does not require the original scheme to be reduced everywhere. The comparison is between any two presentations, including the identity and different chosen fields.

Step 1 uses the new calculus for local invariant/ideal independence and the existing finite-type-ideal gluing statement for its actual conclusion. I checked the latter's qcqs and quasi-compact-open hypotheses on the Noetherian blowup levels. Step 2 cites both the definition specifying the flat blowup comparison and the theorem that it is an isomorphism; it also cites both the strict-transform comparison datum and its identifying theorem. These statements really concern ordinary scheme-theoretic blowups/strict transforms. The finite-cover termination argument is written out and takes its terminating local process from clause (3) of the calculus, rather than assuming an arbitrary decreasing order is well founded. Step 3 uses precisely the finite-history smooth/embedding comparisons, stratum ideals, and termination clauses; it distinguishes a target stratum absent from the source from the next stratum met by it.

Step 4 uses the model lemma for regular projections, both flat blowup interfaces for base change, and Cartier-ideal blowup isomorphism only to delete UNIT ideals. It pulls back one finite tower, so no inverse-limit existence statement for an unbounded blowup diagram is hidden. Step 5 uses the proper-blowup statement and definition of proper to obtain finite type, regular-base-change with its finite-type base-change hypothesis, and regular ascent with Noetherian target and regular fibres. The centers are closed in Noetherian levels, hence finite type; the final base-change schemes are finite type over each original field. Step 6 uses flat-under-regular for the actual flat LOCAL stalk map between Noetherian local rings, obtaining original-singular-locus support even during cleanup. These cited statements were opened and read; regular ascent alone would not give the converse needed in Step 6.

Steps 7 and 8 use the model lemma's finite-stage smooth map, with identity in Step 7 and arbitrary regular h in Step 8. The statements explicitly include all presentations and no field compatibility. The ideal-extension/deletion induction is written out; no unsourced assertion that every regular map is smooth appears. Step 9 uses surjective base change at each level of the two disjoint-union-with-identity maps, exactly as Temkin 2.3.1; this preserves positions of nonempty centers. Step 10 again uses actual finite-type-ideal gluing and flat-blowup comparison, checking overlap equality on affine refinements, not assuming affine intersections. Step 11 uses a finite common refinement, surjective base change to exclude deletion on the full covers, and the scheme-morphism gluing theorem's uniqueness conclusion. Step 12 checks composition on coefficient/fraction charts of the cited flat comparison and then uses the same gluing uniqueness. All cited step/node pairs have literal excerpts in citations.json. No step exceeds 2000 characters or contains a hidden separate long comparison proof.

Small cases checked: the empty scheme uses a nonempty index set of empty models and has a zero-length tower; a regular initial scheme has no active centers, and flat local descent ensures that a regular affine limit misses all model centers. For embedded nilpotents I considered Spec(Q[x,e]/(e^2,xe)): it is generically reduced but not reduced at the origin, so taking its reduction or applying the trace-formula reduced calculus would be invalid. The local input retains its actual ideal and scheme-theoretic transforms. A nonempty Cartier center is never deleted merely because its blowup is an identity. Open maps missing an early maximum delete only that empty center and retain the remaining order. Finite disjoint unions of different dimensions need the normalized common invariant and the identity-summand argument; independent per-component stage numbering would not work. Nonseparated schemes are covered by the same finite affine gluing argument. Different ground-field choices, including a deformed coefficient-field section on a nonreduced algebra, are handled by identity comparisons of presentations rather than identifying their scalar maps.

## Unfinished work

No assembly step remains unfinished. The two new hard inputs are intentionally statement-only stage-1 leaves to be split later. Their archival sources are requested above. The maintainer's independent review must judge these mathematical inputs and the assembly after delivery.
