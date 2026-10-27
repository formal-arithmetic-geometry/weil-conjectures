# Stage-1 report: lem-trf-continuous-precomposition-injective-module-cech

## Files written

- dag/nodes/sec-trace-formula/lem-trf-continuous-precomposition-injective-module-cech.json: statement item, split; not a Mathlib leaf. Statement and statement dependencies unchanged.
- citations.json: nine entries, covering each cited node in each proof step, with verbatim statement quotations.
- searches.jsonl: actual msearch command records; prior searches already in the imported item were retained.

Zero new nodes; zero new Mathlib leaves. The sandbox initially contained no item or report. No Lean was written, no compiler was run, and the shared repository and launcher files were not modified.

## Attachments

None. Searches of WeilConjectures for the exact blueprint tag, continuous precomposition, and injective-module Cech results found no declaration giving every clause. SiteContinuousPushforwardSheaf.lean supplies only the sheaf-condition part. CechInjectiveModule.lean concerns constant ring coefficients and does not give the continuous-cover comparison for a varying ring sheaf. Sheaf/CategoryTheory/Sites/InjectiveModuleCechAcyclic.lean supplies an existing dependency, not the item.

## WANTED

None. Read Stacks sites.tex, Definition 00WV (definition-continuous) and Lemma 00WW (lemma-pushforward-sheaf); sites-cohomology.tex, Tag 0D6X (lemma-pullback-injective-pre-limp), including its proof, and Tag 03FC (lemma-injective-module-trivial-cech), including its proof. The latter uses module injectivity and makes no claim that the underlying abelian sheaf is injective.

## Problems found and corrected

The imported statement is correct under its existing common-universe convention. Its proof was empty. I filled the proof using the existing, more general fixed-cover nerve lemma lem-trf-continuous-cover-nerve-comparison and the existing ringed-site module-injective vanishing lemma lem-weil-pbc-ringed-site-injective-module-cech-acyclic. I did not create another nerve or acyclicity node. The generic transport node lem-trf-cover-nerve-cech-vanishing-transport states only vanishing transport, whereas this item also asks for a specified derived isomorphism; I wrote the cochain construction directly.

The whole imported blueprint was searched using blueprint_refs.py search with precomposition, 03FC, injective Cech, and nerve, in addition to DAG keyword searches. No imported blueprint node states this item in another form; same_as remains []. I read the current latest blueprint chapter/unit and the lem-trf-local-term-locality statement and proof. The existing long ancestry places this input below the specialization branch; this split changes no unit or chapter route and does not invoke an SGA source.

Mathlib searches used msearch for all four required services and a second LeanFinder phrasing. LeanSearch supplies sheafPushforwardContinuous and op_comp_isSheaf; these are sheaf-condition results, not the comparison and module-injective vanishing. The two LeanFinder searches returned local-injectivity results, a Mayer-Vietoris short complex, and topological sheaf-condition diagram comparisons. Loogle returned zero hits; grep returned Stone-Cech topology. I read Continuous.lean and ModuleCat/Sheaf/PushforwardContinuous.lean for the genuine sheaf-condition candidates. No result is an exact or one-line match to all clauses of the item. Every newly recorded query is copied from the actual msearch log, with its actual output digest and verdict.

## Unfinished work

None in the requested one-level split. Existing unsplit dependencies remain their owners' work. No new statement-only nodes were necessary.

## Not duplicates

No new nodes. Existing fixed-cover nerve comparison and ringed-site injective-module vanishing were reused instead of duplicated.

## Review by NH

I checked delivery-errors B through E against the actual statements and the Stacks proofs. Step 1 uses the continuous-pushforward node's set and abelian sheaf conclusions, then the algebraic-sheaf/underlying-set equivalence for rings. The module-category definition says precisely that a module structure on each abelian section group with semilinear restrictions is the required module sheaf; the displayed restriction equality verifies that condition. No theorem about preservation of injectives is used here.

Step 2 uses the statement of the existing continuous-cover-nerve-comparison node, not its proof: for our fixed covering continuity supplies both of its hypotheses, and its conclusion gives canonical isomorphisms and compatibility with every index map. Its own statement requires neither preservation of arbitrary pullbacks nor cocontinuity. Taking an omitting-factor index map proves exactly the item's compatibility formula. I opened that node and checked all quantifiers, including arbitrary tuple length and repeated indices.

Step 3 uses only the alternating Cech complex definition after step 2. I checked the direction of the inverse restriction map carefully: I(c inverse) goes from I(uW) to I(P), because I is contravariant. The explicit equation u(delta_W)c_t inverse = c_r inverse delta_P gives equality of the individual signed summands; summing yields the chain-map equation. The displayed inverse I(c) makes both composites identities, and multiplying the chain equation by the inverse proves its chain equation. This is a direct calculation, not a hidden comparison lemma.

Step 4 uses precisely the localization functor in def-weil-abstract-derived-category and the zero negative terms in def-weil-pbc-site-cech-complex. A functor preserves the two inverse equations, so the cochain isomorphism represents the asserted derived isomorphism; boundedness below is immediate from the definition. Canonicity follows from the projection characterization already supplied by step 2.

Step 5 uses the ringed-site module-injective vanishing node's actual statement. I checked that its site is D, ring is the varying sheaf R, module is I, and covering is the image covering uU; the continuity assumption supplies the last hypothesis. The item's existing common universe aligns objects, homs, indices and coefficient values, matching the dependency's repaired size condition; no independently smaller coefficient category is used. Its four precoverage hypotheses are exactly the site axioms. For a small site the additive sheafification and locally-bijective comparison used in its Lean encoding are available in the same universe: I read the concrete sheafification instance in Sites/LeftExact.lean:308 and the generic WEqualsLocallyBijective instance in Sites/LocallyBijective.lean:152. These are implementation instances for the ordinary small-site sheaf theory, not additional geometric assumptions or a change of coefficient category. The source Tag 03FC itself states the theorem for any ringed site. Finally the inverse cochain maps induce inverse maps of the kernel/image quotients, giving the desired vanishing without injectivity of I_ab.

I tested the empty covering (all products indexed by positive-length tuples over the empty set are zero groups), a singleton identity covering (comparison maps are the canonical identities and the differentials alternate between zero and identity), repeated covering indices (no division or antisymmetrization), zero coefficients, degree zero (an isomorphism is asserted but no vanishing), and degree one (the positive vanishing applies). Arbitrary chosen fibre products are handled by the projection-characterized comparisons. All proof steps are below 2000 characters. No new statement or dispute was introduced. I checked every citation against a verbatim part of the corresponding live node statement and included the full relevant statements for the two sheaf lemmas and nerve lemma in citations.json.

The continuous-pushforward lemma and ringed-site vanishing lemma are generic tools outside this trace-formula unit. Their use is declared in split_report.tool_uses with an explanation; no maintainer-owned top-level tool_uses was added.
