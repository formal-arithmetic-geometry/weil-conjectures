# Q52: lem-trf-separated-lqf-fppf-effective-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-separated-lqf-fppf-effective-descent.json: item, split in six steps; not a Mathlib leaf.
- dag/nodes/sec-trace-formula/lem-trf-fppf-family-affine-effectivity-reduction.json: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and grep.
- dag/nodes/sec-trace-formula/lem-trf-quasi-affine-fpqc-effective-descent.json: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and grep.
- citations.json: every cited node for every step, with text copied verbatim from its statement.

Two new nodes, zero new Mathlib leaves. All existing metadata and searches on the item are retained. No Lean, unit, chapter, live project or launcher file was written. The script write_split.py is a sandbox helper, not a delivery file.

## Attachments

No attachment for the item or either new node. Searching the blueprint tag and effective-descent/quasi-affine vocabulary in WeilConjectures found only the finite locally free quasi-projective effectivity theorem in AlgebraicGeometry/EffectiveDescent.lean (line 62, itself sorry) and the specialized quasi-affine etale descent construction in Sites/EtaleTopologicalInvariance/Descent.lean. Neither has these hypotheses or this conclusion. The existing node lemma-nagata-quasi-affine-morphism-of-quasi-finite already records the closed declaration AlgebraicGeometry.IsQuasiAffineHom.of_locallyQuasiFinite, QuasiAffine.lean:106, which is reused, not re-created or split.

## WANTED

None. All mathematical sources used are present under literature/stacks-project/.

## Problems found and corrections

The imported item statement agrees with Tag 02W8 and is unchanged. In particular, neither quasi-compactness nor local finite presentation of the object morphisms may be inserted. The source requires a finite-presentation hypothesis only on the singleton covering after reduction.

The existing lem-galois-fpqc-descending-types-morphisms is insufficient for this application: it concludes only for singleton fpqc covers, and its affine hypothesis asks effectiveness for ALL flat surjective affine maps. Here the proof needs finite presentation of the affine covering map to make the saturation open. The new fppf-family reduction is the different specialization of 02W3 needed here, not a reuse of the stronger affine hypothesis without proof.

During self-review I replaced an informal claim about shrinking affine witnesses for local quasi-finiteness by the existing exact restriction theorem lem-weil-pbc-lqf-restriction-to-opens. That theorem is not just the existential definition in pqf-def-quasifinite. I also wrote out the saturation invariance using surjective base change, rather than assuming that a pointwise image can be transported without lifting it. There is no statement dispute or source error in this item.

## Not duplicates

lem-trf-fppf-family-affine-effectivity-reduction vs lem-trf-separated-lqf-fppf-effective-descent: 02W3 is a conditional reduction theorem for an arbitrary base-change/coproduct-stable morphism property; the item is the unconditional 02W8 theorem for separated locally quasi-finite objects. The reduction supplies no effectivity of the affine case, whose saturation argument is proved in item steps 3-6. The shared 02W8 tag in the source field only records where this generic reduction is used.

lem-trf-quasi-affine-fpqc-effective-descent vs lem-trf-separated-lqf-fppf-effective-descent: 0247 covers quasi-affine morphisms of arbitrary relative dimension, such as a punctured affine plane, along fpqc covers; 02W8 covers separated locally quasi-finite morphisms which need not be quasi-compact or quasi-affine, along fppf covers. The item must construct invariant quasi-compact quasi-affine opens before 0247 applies. Thus this tool is neither a clause nor a restatement of the item.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-descending-types-morphisms: the new node is 02W3 for arbitrary fppf families and assumes the affine case only for flat surjective finite-presentation covers; the existing node has only a singleton fpqc conclusion and needs the affine case for all flat surjective affine maps, so it cannot supply this reduction.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-affine-model-transitions: this existing 02W3 proof input constructs a Cartesian comparison of already effective models, not a reduction for a general morphism property and fppf families.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-effectivity-open-local: this existing 02W3 input assumes effective restrictions to affine base opens for a singleton fpqc cover; it does not reduce fppf families to finite-presentation affine covers.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-affine-descent-effective: this is effectivity for affine object morphisms under a singleton fpqc cover, not a reduction for arbitrary morphism properties.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-refinement-reflects-effectivity: this compares singleton fpqc refinements; it neither constructs standard fppf refinements nor gives the arbitrary-family reduction.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-affine-model-transition-cartesian: this verifies a reconstructed transition square, not the affine-reduction theorem.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-effectivity-affine-base-gluing: this glues effective affine-base restrictions for a singleton fpqc cover; it does not assert the new reduction.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-affine-model-transition-reconstruction: this checks the overlap equation for a restricted model projection, not the new reduction.

lem-trf-fppf-family-affine-effectivity-reduction vs lem-galois-fpqc-affine-models-glue: this glues supplied models for affine opens in a singleton fpqc setting, not arbitrary fppf-family descent from the finite-presentation affine case.

lem-trf-quasi-affine-fpqc-effective-descent vs lem-galois-fpqc-affine-descent-effective: the new node permits quasi-affine object morphisms, such as a punctured affine plane; the existing theorem requires affine object morphisms.

lem-trf-quasi-affine-fpqc-effective-descent vs lem-pd-effective-invariant-open-cover: the latter glues already effective restricted data, without proving effectivity of a quasi-affine datum. It is reused for gluing, not duplicated.

lem-trf-quasi-affine-fpqc-effective-descent vs det-lem-stratified-lattice-scheme: the existing statement constructs a lattice scheme, although its imported proof mentions quasi-affine descent. It does not state the generic 0247 theorem.

lem-trf-quasi-affine-fpqc-effective-descent vs lemma-weil-pbc-universal-homeomorphism-site-equivalence: the existing node is etale topological invariance for a universal homeomorphism; its proof mentions an affine-hull descent construction but its statement gives no generic effective descent for quasi-affine morphisms.

Whole-DAG searches by tag, quasi-affine/effectivity vocabulary, the literal proposed ids and Lean declaration concepts, and whole-blueprint searches for 0247, 02W3, descending types, quasi-affine, and effective quasi-affine found no node that states either new fact. The two new facts are non-elementary independent tools: 02W3 includes refinement, fully faithful descent and general-base gluing; 0247 includes affine-hull construction and descent of its invariant open. Neither restates a clause of this item, whose substance is carried by the saturation construction and its geometry.

## Review by Q52

I read Stacks more-morphisms.tex Tag 02W8 (lemma-separated-locally-quasi-finite-morphisms-fppf-descend), including the entire proof, and checked the statement against the family form of 023V. I read descent.tex Tag 02W3 (lemma-descending-types-morphisms), both the reduction hypotheses and its affine-refinement/general-base proof, for the first new node. I read descent.tex Tag 0247 (lemma-quasi-affine), including its affine-hull, flat base-change and invariant-open proof, for the second new node. I also read more-morphisms.tex Tag 02LR and descent.tex Tag 0AP4 to check the exact tools used after constructing the saturations. The current main-20261015 unit is the curve-zero/local-term unit; the inherited quotient-presentation support chain and blueprint ancestry are preserved. There is no SGA route.

For step 1 I opened the statements of separated-lqf-base-change, scheme-coproduct-family, pqf-def-quasifinite and proper-morphism. The first supplies precisely both base-change conclusions; the coproduct node supplies disjoint clopen summands. The clopen diagonal calculation and the unchanged affine local rings verify coproduct stability directly. In particular the empty coproduct causes no omitted condition.

For step 2 I compared every hypothesis of the new 02W3 statement with step 1 and the affine case that steps 3-6 actually prove. The finite-presentation assumption is on A to B alone. I opened fppf-affine-refinement and fpqc-covering: the former provides finitely many affine opens over any restricted affine base whose images cover it, which is exactly the latter's finite-image-cover condition. The current fppf-site statement explicitly includes joint surjectivity and the site structure gives base-change coverings. This avoids assuming that every singleton fppf cover is quasi-compact.

For step 3 I opened flat-lfp-open, affine fibre-product spectra, affine-scheme-qcqs, affine-opens-basis and descent-datum. The affine fibre-product node applies because C, A and B are all affine. Its quasi-compact source has quasi-compact continuous image, with the open-cover argument written in the step. Openness uses the base change of the finite-presentation flat covering map. The diagonal specialization of the cocycle forces identity, so the saturation contains C.

For step 4 I opened surjective-base-change and descent-datum. I checked the pullback of r_C over a map Z to W_C is surjective without requiring r_C affine or quasi-compact. On that pullback the witness in C is an actual morphism, so cocycle composition applies on test schemes, not merely on underlying pairs of topological points. The transported map factors through the open because this holds after a surjective morphism; reverse transport gives equality of opens and an inverse. The restricted datum and compatibility with the inclusion are precisely what the later gluing statement asks for. This is a routine calculation with the given transport and its cocycle, not an omitted separate comparison lemma.

For step 5 I read the statements of lqf-restriction-to-opens, affine-scheme-qcqs, qcqs-morphism-permanence, lqf-locally-finite-type and lemma-nagata-quasi-affine-morphism-of-quasi-finite. Each is used for its stated conclusion: source-open restriction, affine target quasi-separatedness, compact-source criterion for a quasi-compact morphism, locally finite type in the Stacks convention, and finally quasi-affineness under the four hypotheses. I corrected the informal restriction argument here as described above. No claim that Mathlib's LocallyQuasiFinite alone includes finite type is made.

For step 6 I checked the new 0247 statement takes an fpqc singleton and a quasi-affine object morphism with exactly the datum constructed in step 4. I opened the complete statement of lem-pd-effective-invariant-open-cover: it takes an open cover, effective restricted data and transport-compatible inclusions, all proved in steps 3-5. It concludes effectiveness of V, finishing precisely the affine case left in step 2. The broader existing singleton-fpqc formulation is used as a generic tool, not silently inferred from a weaker definition node.

I tested the empty base and empty family (the family covers only the empty base), V empty (empty invariant open cover), the identity cover (saturation of C is C), infinite disjoint unions of quasi-finite pieces (no global quasi-compactness), and an object not locally of finite presentation. For the new reduction, the vacuous property and the empty finite coproduct agree with 02W3. For the quasi-affine descent statement, the identity cover, empty object and punctured affine plane are consistent and show why affine descent alone is insufficient. Every statement is self-contained, the new nodes have no proof or proof dependencies, and all recorded new searches are actual msearch.py log entries whose hits I read. IsStack results assume the missing stack hypothesis and property-descends-along results concern already existing morphisms, so neither is an exact or one-line match. No proof step exceeds 2000 characters. The citations file contains a literal statement quote for every use.

## Unfinished work

The two supporting statements are intentionally unsplit for later stage-1 items. No required part of this item's argument is left implicit. Validation and delivery use the prescribed server-side tools.
