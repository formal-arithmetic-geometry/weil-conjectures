# Worker report

Item: lem-sfb-artinian-ring-finite-local-product. Group: Q43. Stage 1 only.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-artinian-ring-finite-local-product.json — complete item is a Mathlib leaf; statement unchanged; no proof steps.
- citations.json — empty list, because a Mathlib leaf has no proof steps or step citations.
- report.md — this report.
- searches.jsonl — genuine search-command log. No new DAG nodes; one Mathlib leaf (the item itself).

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for Artinian product/local-factor terminology. LocalTensorQuotientDetection and ReducedArtinianTensorNormalizationCharts mention product decompositions but state different theorems. Neither supplies an attachment for this complete item; Mathlib is the match. Sorry declarations were not treated as completed proofs.

## Literature wanted

None. I read literature/stacks-project/algebra.tex, Tag 00KJ (proposition-dimension-zero-ring), equivalence (1) and (4), and its cited ingredients: 00J7 (lemma-artinian-finite-nr-max), 00J8 (lemma-artinian-radical-nilpotent), 00JA (lemma-product-local), and 00JB (lemma-artinian-finite-length). They agree with the item's Artinian finite-local-product assertion.

## Findings and changes

The item was unsplit, without a proof; there was no earlier sandbox split to preserve or dry-run. The statement, source, statement dependencies, original search history, candidate and creation/provenance records are retained. Set status to mathlib, fill mathlib_match with the full clause-wise correspondence and exact files/lines, and leave proof and proof_deps empty; proof_origin records the Stacks source, as required by the item preflight. No new node, statement correction or route change.

The inherited candidate and search verdicts focused on quotNilradicalPowEquivPi: that result requires selecting a nilpotence exponent and identifying the quotient with R. Those original search records remain historical evidence. The successful match uses a different equivalence: MaximalSpectrum.toPiLocalizationEquiv. Its discrete-spectrum hypothesis is supplied by an existing instance for Artinian rings, so no new mathematical lemma is needed. This is precisely the allowed Mathlib-leaf case of an instance-inferred hypothesis and one declaration per clause.

I read the chapter/unit JSON records and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images proof. The item is a generic algebra prerequisite of the inherited component-count chain, not the unit's key statement. The inherited blueprint.from.node is null, as blueprint_refs.py ancestor also returns None. I retain that metadata limitation, the complete from.place and via list, and explain it in split_report.blueprint rather than inventing an ancestor. The latest direct-images narrative has changed from the inherited alteration narrative, but this ring-theory leaf and its parent's component-algebra application require no replacement route. No unit record is edited.

## Mathlib match and searches

Take I = MaximalSpectrum R and R_i = Localization.AtPrime i.asIdeal.

- Canonical ring isomorphism: (MaximalSpectrum.toPiLocalizationEquiv R).toRingEquiv, Mathlib/RingTheory/Spectrum/Prime/Topology.lean:772–775, with component formula at 783–785.
- Its sole additional topological hypothesis is inferred: Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean:54–55 supplies DiscreteTopology (PrimeSpectrum R) under [CommRing R] [IsArtinianRing R] (line 50). No separate comparison or derivation is needed.
- Finite index set: IsArtinianRing.instFiniteMaximalSpectrum, Artinian/Module.lean:525–527, with finiteness of maximal ideals at 518–523.
- Artinian factors: IsArtinianRing.localization_artinian, Artinian/Ring.lean:92–93; the concrete localization instance at 97–98 applies to the definition of Localization.AtPrime directly.
- Local factors: Localization.AtPrime.isLocalRing, Localization/AtPrime/Basic.lean:107–108. Nonzero factors are explicit in IsLocalization.AtPrime.nontrivial at 62–67; the local-ring instance invokes the same localness result at 69–70.

I read those source lines rather than relying on search-service summaries. Each clause specializes directly; the only object choices are the stated maximal spectrum and its localizations. An R-algebra equivalence gives a unital ring equivalence by forgetting its algebra structure. No extra assumption is introduced.

I ran the prescribed msearch.py command for LeanFinder with two phrasings, Loogle, LeanSearch, and several grep patterns; exact tool/query strings and actual logged answers are in mathlib_searches and searches.jsonl. All services used were available. One grep incorrectly named Spectrum/Prime/Noetherian without the .lean suffix and returned zero hits; I recorded that outcome accurately and corrected the search to the containing directory. The corrected grep locates the Artinian discrete-spectrum instance at line 54. The semantic searches primarily returned the quotient decomposition and finiteness/localization facts; the source search found the complete match. Every search record is an actual command invocation; earlier Q27 records are preserved.

## Not duplicates

No new nodes. I searched the whole DAG for 00KJ, 00J7, 00JB, radical nilpotence, and Artinian products, and the whole blueprint with blueprint_refs.py for Artinian ring, 00KJ and Artinian local. The latter two searches report no matches. Existing nodes for finite spectrum, the radical theorem and the localization-product criterion are not duplicated. lem-sfb-reduced-artinian-residue-product assumes reducedness and gives residue fields, so it does not replace the present theorem for nonreduced rings. lem-weil-pbc-artinian-ring-self-finite-length states only finite length. The present node's status records a direct Mathlib match without changing any other DAG node.

## Review by Q43

I checked the unchanged statement against Stacks 00KJ (1) and (4), opening the actual proofs of 00J7, 00J8, 00JA and 00JB. The hypothesis is the descending chain condition on ideals of a commutative unital ring, exactly the commutative specialization of Mathlib's IsArtinianRing. Locality means a unique maximal ideal and includes nontriviality, as the item's existing statement dependency explicitly records.

There are no proof steps and hence no step/node quotations to audit: citations.json is correctly empty. Instead I audited every clause against the declarations above. The product equivalence is stated for precisely the chosen family, its topological hypothesis is an inferred Artinian instance, the finite-index instance has no Nontrivial hypothesis, and both localization properties have exactly the Artinian or prime-localization hypotheses available here. Localizations at maximal ideals are localizations at prime ideals; maximal ideals carry their prime instance. Locality and nontriviality are provided by actual theorems, rather than inferred from the product's shape. Every required statement is supplied by a declaration or inferred instance, not by extracting an argument from its docstring. There is no uncited non-elementary proof step, off-unit non-leaf dependency, cycle, hidden comparison, induction or step longer than 2000 characters. No SGA source is used.

For B1–B9, the leaf has no proof or proof dependencies, no new statement with missing objects or definitions, a complete match with file/line evidence, genuine searches, and retained blueprint metadata. For C1–C8, the status avoids unsupported step citations; for D1–D5, no clause has been moved into a new node and no broad prerequisite was invented. The direct Mathlib match is the permitted stopping condition, rather than a relabelled split.

For E1–E7 I tested R = 0: it has no maximal ideals, the index type is empty, and the same canonical equivalence gives the one-element empty product; the factor conditions are vacuous. A field gives one factor. The nonreduced ring k[e]/(e^2) also gives one factor, retaining its nilpotents. A product of two such rings gives two nonzero local factors; no reduction is taken anywhere. An infinite product of fields is excluded by the Artinian hypothesis. Thus neither a field condition, reducedness, positive number of factors, finite-dimensional base algebra nor injectivity of individual localization maps is used. No statement dispute or correction is required.

## Unfinished work

None for stage 1. The pre-existing null blueprint ancestor is reported above. The delivery tool supplies the final dry-run and push results.
