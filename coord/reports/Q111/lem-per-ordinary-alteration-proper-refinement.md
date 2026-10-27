# Stage-1 delivery: lem-per-ordinary-alteration-proper-refinement

Group Q111, 2026-10-24. Direct delivery by the assigned worker; no second worker or subagent was started.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-ordinary-alteration-proper-refinement.json: existing statement unchanged; split into eight proof steps. Earlier source, blueprint provenance, imported searches and metadata retained, with additional searches appended.
- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-cover-finite-zariski-refinement.json: new statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, corrected Loogle and source grep.
- dag/nodes/sec-deligne-laumon-a1/lem-per-zariski-proper-surjection-interchange.json: new statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- citations.json: one verbatim statement quotation for each citation in each numbered proof step. report.md and the searches.jsonl log accompany the delivery.

Two new nodes; zero new Mathlib leaves. Scratch source extracts, scripts and search-results.json remain in this item's sandbox only.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag and alteration/refinement terminology found no declaration proving this item; searches in lean/Sheaf found no matching refinement lemma either. The existing generic covering-sieve criterion lem-per-generated-precoverage-covering-sieve is reused as a Mathlib leaf; it is not recreated.

## WANTED

None for this split. The ILO volume supplying the item and both new statements is present. Proposition II 3.1.1 itself references Orgogozo's Lemma 10.3 for the ordinary Zariski refinement; that deeper proof is deferred to the new unsplit etale-generator node, whose source is the available ILO proposition.

## Findings and changes

The imported item had no proof. Its statement is exactly the ordinary case of ILO II Theorem 3.2.1, with finite extraction; it is not regular uniformization and not the prime-to-ell theorem. No statement dispute or statement correction was needed. Quasi-excellence is retained even though the elementary ordinary-case construction does not use it.

Read the latest blueprint, commit ef6f9619fdbffa59e88528fb56483d76c70258c8: chapter sec-deligne-laumon-a1, unit sk-p-dl-a1-perverse and ancestor lem-per-artin-gabber-affine-curve. The current ancestor is the affine-pushforward/perverse bound; this is an auxiliary regular-local-model/purity input down the inherited weak-uniformization branch, not a change to the chapter or unit route. No unit file is modified. The existing blueprint.from.node and via chain are retained, and the new nodes add this item to that chain. Whole-blueprint searches with tools/blueprint_refs.py for alteration, Zariski refinement, finite Zariski, proper surjection and etale Zariski gave no node stating either new lemma. The proper-surjection hits are Chow refinements with projective targets, not either assertion here. DAG searches included the ILO theorem/proposition numbers and the words alteration, finite surjective, Zariski, compactification, proper surjection, dominant component and generated precoverage. Matching existing component, permanence, dominant-part and topology lemmas are cited.

The proof uses the class K of presieves admitting proper/open refinements, proves the precoverage axioms, identifies its generated topology, and only then applies the existing covering-sieve membership criterion. This avoids assuming that an arbitrary covering family is a single generator or replacing the item by a restatement. The two new nodes are restricted to the etale-generator case and the explicit local-proper interchange, respectively; neither mentions an arbitrary alteration covering sieve.

## Not duplicates

lem-per-etale-cover-finite-zariski-refinement vs lem-per-ordinary-alteration-proper-refinement: the new lemma treats only a jointly surjective etale generator, with a finite rather than merely proper map; the item must prove closure under composition/base change and passage to all covering sieves.

lem-per-etale-cover-finite-zariski-refinement vs lem-per-alteration-cover-proper-normal-form: the existing node assumes an invertible prime and a prime-to-ell alteration cover and gives a completely decomposed etale final cover. It does not provide the ordinary finite-surjective/Zariski refinement of an arbitrary etale generator, on possibly reducible reduced bases.

lem-per-etale-cover-finite-zariski-refinement vs lem-per-alteration-finite-normal-generator-tree: that node gives a finite tree for a prime-to-ell covering family, with normal integral vertices and completely decomposed etale edges; it neither includes the parameter 1 nor replaces an etale generator by a finite map and open cover.

lem-per-etale-cover-finite-zariski-refinement vs lem-sbc-integral-etale-cover-disjoint-refinement: the latter assumes an existing integral morphism and gives a local disjoint-open refinement; the new statement constructs a global finite surjective map to the target of the given etale covering.

lem-per-zariski-proper-surjection-interchange vs lem-per-ordinary-alteration-proper-refinement: the new statement has an explicit two-stage finite open/proper input and produces restriction maps to those local sources. It contains no assertion about all covers of a generated topology, which is the assembly proved in the item.

lem-per-zariski-proper-surjection-interchange vs lem-per-dominant-part-coreflection: the existing lemma constructs dominant parts and preserves a given proper surjection; it does not extend local proper maps over an open cover to a common global proper source.

lem-per-zariski-proper-surjection-interchange vs thm-nagata-compactification: compactification only embeds each separated finite-type map into a proper one; it does not give the common surjective object of alt/S or the restriction maps for all local maps. Compactification is an input to the new lemma's future proof.

No new source has a Stacks tag colliding with an existing source: the new statements are precisely located in ILO II 3.1.1 and the ordinary proof of 3.2.1. The Stacks tags in the assembly identify existing nodes, not new ones.

## Review by Q111

I read ILO Expose II, printed pp.23--29: the definition of alt/S, generic-fibre finiteness (1.1.7), the observation about its arrows (1.1.10), dominant parts and fibre products (1.2.5--1.2.8), the ordinary topology (2.3.1 and 2.3.3), the finite-surjective Zariski refinement in the last clause of Proposition 3.1.1, and the full proof of Theorem 3.2.1 for parameter 1. These are the sources of the item and of both new nodes; I did not use the later prime-to-ell flattening/Sylow argument. I also read Stacks 00ZC, 01S1, and the generic-point/reduced-closed-subscheme sources, and checked tag-label correspondence in the local tags table. No SGA source is used.

For Step 1 I checked that the ordinary-topology definition really describes objects and arrows, that finite type over the Noetherian base supplies Noetherian sources, and that the generic-fibre criterion applies to every object. I added component-cover and sobriety citations rather than leaving the existence of a component-generic generalization implicit. An image and any generic generalization lie over the same generic base point, so finite fibres force equality; the finite residue extension then passes to an intermediate field. Finite type of arrows is written on affine charts, not silently assumed. I also cited the existing affine-Noetherian-space lemma for quasi-compactness of preimages, with the finite-union argument written explicitly.

For Step 2 I read the entire statement of lem-per-dominant-part-coreflection: it gives the Hom bijection, functoriality, the generic-fibre reduction formula, the etale comparison and proper-surjection preservation. These are the exact clauses used in Steps 2--3. The fibre-product finiteness argument is the elementary tensor-basis argument written in the proof; it does not assert that ordinary fibre products are already objects of alt/X. I checked that the finite-type composition/base-change node states both required permanence properties.

For Step 3 the proper-base-change node actually asserts properness of the base-changed scheme map, and the surjective-base-change node asserts surjectivity with no flatness assumption. Their hypotheses hold for the proper witness and the arbitrary arrow in alt/X. The dominant-part statement then preserves the proper surjection to the reduced new target. The open-immersion/etale node explicitly says an open immersion is etale, allowing the etale comparison to identify the categorical inverse-image opens. Their union covers by the definition of inverse images of an open covering. Isomorphisms have the identity witness.

For Step 4 I checked the interchange lemma is applied over the proper witness Y, not over an unrelated original base: the V_a really cover Y, and each Q_a is proper surjective over V_a and an object of alt/Y by Step 1. Taking inverse images of the finite open covers of Q_a produces the composite covering presieve, and proper composition is exactly the assertion of the cited existing node. This is the only substantial interchange and it is its own statement-only node.

For Step 5 the new etale lemma requires only a reduced Noetherian target and finite-type etale sources; objects of alt/X supply these conditions, even for an infinite indexing family. It supplies a finite surjective object of alt/T and a finite open cover, exactly the K-witness required. The finite-proper leaf has no extra hypotheses. Conversely every proper/open witness is a composite of the ordinary generators. The minimality argument is written in both directions. This avoids using prime-to-ell lemmas with an unjustified choice of prime.

For Step 6 I read the statement of the existing generated-precoverage Mathlib leaf and its Mathlib type: the proof verifies all four assumptions (isos, composition, pullbacks, base-change stability) before applying it. It gives a covering presieve contained in the particular given covering sieve, not merely an equivalence of sheaf categories. Factoring its arrows through the original T_b is precisely what the ordinary definition says. citations.json quotes these actual statements verbatim.

For Step 7 I checked every component and closed-subscheme citation against its statement. The closed-immersion-proper node includes composition with an already proper map, and the closed-image leaf gives closedness of the image. Selecting a component meeting the generic fibre guarantees that its image contains eta; closedness then guarantees surjectivity. The component is reduced and nonempty, hence integral. I made residue-field preservation under the reduced closed immersion explicit by the prime-quotient calculation; the finite function-field extension is then the object condition of Q, not an unsupported claim about arbitrary components. Finite type over the original Noetherian X supplies Noetherianity of P. Step 8 is only restriction to inverse-image opens and composition of X-morphisms; this is correctly marked elementary.

I tested the new etale assertion for S empty, the identity covering and a field with a nontrivial finite separable covering: allowing a finite surjection rather than a Zariski refinement of S itself is essential. For the interchange assertion I tested empty S, a singleton open S, the identity local maps, disconnected S with opens on separate components, and overlapping opens. The disconnected example explains the explicit complement correction in its source note: compactifying Z_i alone need not cover all of S. To prove the stated version, compactify each Z_i over S with dense image, add the reduced closed complement of U_i to that compactification, take the product, then the dominant reduced part. Above U_i the complement vanishes and properness of Z_i over U_i makes the compactification restrict to Z_i; the projections give the stated restriction maps. Every factor now covers S and has finite generic fibres. This is the same ordinary compactification route, with its reducible-base edge case made explicit; the new statement itself contains no proof sketch.

I read the hits of every logged Mathlib search. General Zariski/etale pretopologies, normalization open covers, finite-implies-proper and properness local at the target do not prove either new lemma. The first etale Loogle query used an invalid IsEtale identifier; I recorded the diagnostic and corrected it to Etale. The corrected hit exists_etale_isCompl_of_quasiFiniteAt was read at Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:49--57: it is a local finite-piece theorem for a separated quasi-finite map after an etale base change, not the finite-surjective Zariski refinement here. Both semantic services and grep succeeded for each new node. Every recorded query was actually run with msearch.py; earlier item searches were retained. All eight steps are under 2000 characters, and every substantial hidden claim was either promoted to a new node or supplied by an existing statement. I checked delivery-errors B--E for self-contained statements, inline/cited definitions, source places, duplicates, clause-restatement, elementary flags, missing hypotheses, incorrect objects and cycles.

## Unfinished work

Only the future proofs of the two new statement-only nodes remain, as intended for a one-level stage-1 split. No Lean was written or compiled. The repository and launcher scripts were not edited; all authored files are in the assigned sandbox. Required server checks and delivery results are recorded below after completion.

## Validation

The server review_split check passed. The first complete deliver.py --no-push invocation exited successfully at 9cacd0adfe2 with preflight passed, including check_dag and review_split. After adding the explicit affine-Noetherian-space citation and recording this result, I rerun the full required dry run before push. No local DAG/preflight checker, compiler or Lake command was run.
