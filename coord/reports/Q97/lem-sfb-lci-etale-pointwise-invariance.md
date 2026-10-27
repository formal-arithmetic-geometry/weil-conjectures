## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-lci-etale-pointwise-invariance.json: split, unchanged statement, four proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-syntomic-etale-source-locality.json: one new statement-only unsplit lemma; no Mathlib match.
- citations.json: all 12 step/node citations, quoted verbatim from the statements read.

Attachments: none. The blueprint tag and complete-intersection / syntomic / etale concept searches of lean/WeilConjectures found no declaration proving the item or the new lemma. Existing ring-theory syntomic declarations concern local polynomial presentations, not etale-source descent.

WANTED: none. No Lean, compiler, Lake or repository mutation was used.

The item was unsplit and the sandbox had no prior node or report. There is no released repair note. The statement needs no correction. The seeded Tag 036S citation alone did not provide a pointwise argument: the source neighbourhood must first be made syntomic, then its image must be an open target neighbourhood, and only that image is covered surjectively. The split now writes this argument. It uses the already existing open syntomic locus rather than adding another local-ring neighbourhood lemma.

The blueprint ancestor command returns None: the inherited created.item chain through lem-sfb-admissible-direct-image terminates without an imported blueprint node. I retained the inherited blueprint.from.node and via on the item and copied precisely the computed ancestor and prefixed via to the new node. Read the current latest blueprint sk-thm-sf-ctf-stability unit and det-thm-sf-ctf-stability-direct-images proof (3). The new lemma supplies the etale-chart comparison in the existing isolated-lci supporting branch; it does not replace a unit step. The latest blueprint has no syntomic-source locality statement. Whole-DAG searches by syntomic, complete intersection, etale/source and Tags 036S/02KM, together with blueprint_refs search, found no duplicate.

Mathlib searches were run with msearch.py and are recorded exactly in searches.jsonl and the node records, including two semantic phrasings of the new lemma and item, Loogle and source greps. I read the returned hits. The promising name Scheme.isJointlySurjectivePreserving is about lifting compatible pairs of points to fibre products (Sites/MorphismProperty.lean lines 31–45 and PullbackCarrier.lean lines 384–385), not descent of a morphism property. The complete-intersection grep hit in RingTheory/Extension/Presentation/Basic.lean line 103 is only a warning in the dimension-of-presentation docstring. Smoothness, etaleness and universally open results do not state either assertion. Thus there are no Mathlib leaves.

## Not duplicates

lem-sfb-syntomic-etale-source-locality vs lem-sfb-lci-etale-pointwise-invariance: the new lemma is general locality of syntomic morphisms to an arbitrary base under etale source covers; it neither mentions corresponding local rings over a field nor constructs or compares pointwise loci. The item still supplies the neighbourhood/open-image argument and checks the structural hypotheses.

lem-sfb-syntomic-etale-source-locality vs lem-sfb-space-fibrewise-lci-source-locus: the latter constructs and compares opens of algebraic spaces and their base changes, whereas the new statement concerns ascent/descent of syntomicity of scheme morphisms. It does not assume or invoke either of these parent nodes.

lem-sfb-syntomic-etale-source-locality vs lem-trf-syntomic-locus-base-change: the existing node proves openness and arbitrary base-change compatibility of a fibrewise locus, not locality under a cover of the source. The new lemma does not construct that locus or assert its base-change formula.

lem-sfb-syntomic-etale-source-locality vs lem-trf-syntomic-geometric-fibres-affine-criterion: the existing node compares geometric fibres and affine ring tests for one map; it gives no etale-source descent theorem.

lem-sfb-syntomic-etale-source-locality vs lem-trf-syntomic-pointwise-local-model: constructs a standard syntomic affine neighbourhood from pointwise flatness, finite presentation and a CI fibre; it does not give etale-source ascent or descent.

lem-sfb-syntomic-etale-source-locality vs def-trf-local-complete-intersection-scheme-over-field: defines an affine-cover predicate over a field and describes field scalar extension; it does not state descent of syntomic morphisms over arbitrary bases.

lem-sfb-syntomic-etale-source-locality vs lem-trf-lci-affine-open-locality: passes a CI affine-cover condition to affine opens of one field-scheme, without etale source covers or syntomic descent.

lem-sfb-syntomic-etale-source-locality vs lem-trf-lci-geometric-chart-descent: compares affine fibre charts under field extension and descends CI across that field extension, not across an etale source cover.

lem-sfb-syntomic-etale-source-locality vs lem-trf-lci-pointwise-criterion: compares local rings and affine CI neighbourhoods over a field, not etale-source descent for syntomic morphisms.

lem-sfb-syntomic-etale-source-locality vs lem-trf-lci-residue-chart-cover-extension: extends an affine CI cover along a residue-field extension and gives tensor identifications, not etale-source ascent or descent.

## Review by Q97

I read descent.tex Tag 036S, label lemma-syntomic-syntomic-local-source, and its proof through composition and the permanence theorem (Tag 02KM, lemma-syntomic-smooth-etale-permanence). I also read morphisms.tex Tags 01UC (definition-syntomic), 01UE (lemma-syntomic-locally-standard-syntomic), 01UG (lemma-local-complete-intersection), and the etale-syntomic and etale-open lemmas. The new node's explicit flat / locally finite presentation / CI-fibre-local-rings meaning is equivalent to that source's syntomicity by 01UE and 01UG, so applying 036S to etale maps (which are syntomic) gives exactly the new two assertions. It introduces all schemes, morphisms, cover indices and fibre objects, cites their actual definitions, and carries no proof sketch in its statement or proof field. It is a reusable theorem for arbitrary bases, not a renamed pointwise clause of the item.

Step 1 uses lem-weil-pbc-module-over-field-flat for the stalk module, def-weil-flat-morphism for the stalkwise criterion, pqf-def-locnoeth for the one affine chart, and pqf-lem-lft-fp-locnoeth for local finite presentation. I opened their statements: the latter requires a locally Noetherian target, which holds because every ideal of the field is zero or the whole field. No Noetherian hypothesis on Y or Z is introduced, and no global finite-type or quasi-compactness conclusion is taken.

Step 2 uses the statement of lem-trf-syntomic-locus-base-change, including its largest-open assertion, not any construction hidden in its proof. Its local-finite-type, flat and locally-finite-presentation hypotheses were verified in step 1. The fibre over the unique point of Spec k is T itself by def-pc-scheme-fibre and the fibre-product identity; the displayed inverse fixes the k-structure. Hence its CI pointwise condition and the item's are the same. The new node is cited here only for its explicitly written meaning of syntomicity. Its fibre-local-ring formulation agrees word for word with the existing locus theorem's last sentence.

Step 3 uses lem-weil-pbc-etale-composition-cancellation: its first clause covers the open inclusions, its second their compositions with e, and its third the target restriction. Thus no unquoted restriction-of-etale theorem is assumed. The new lemma's ascent clause applies to the already syntomic L_Y. Then the largest-open statement established in step 2 gives the required membership.

Step 4 uses lem-weil-pbc-etale-morphism-open-map for V=e(L_Z) being open, and the same three composition/cancellation clauses for L_Z to V. Surjectivity is only onto this image, not onto Y. The singleton cover therefore satisfies every hypothesis of the new descent clause; the composite is the structural map already known syntomic in step 2. Maximality then proves membership of y. These are genuine neighbourhood arguments, not inline assertions of the desired invariance.

I checked B–E against the node files and sources: no elementary side-claim became a new node; each non-elementary input has a statement citation; none borrows only a cited node's proof; all 12 quotes were copied from those statements; all new searches were actually run; the new node has no dependency on the item or its ancestors, so introduces no cycle. Every proof step is below 2000 characters. No SGA route is used. lem-trf-syntomic-locus-base-change is declared as an off-unit generic tool in split_report.tool_uses, since no node of the present unit supplies its scheme-level open-locus theorem.

Small cases checked: empty Z is vacuous; a non-surjective open immersion only tests image points; a finite separable field extension is etale and both local rings are fields; over an imperfect field no smoothness/regularity equivalence is used. A singular CI such as k[t]/(t^2) stays within the CI assertion and is never claimed smooth. The new source-locality statement allows the empty covering family only for empty X; without that condition descent would be false. Quasi-compactness and separation are not present in the source locality theorem and were not silently added. No mathematical correction was needed.

## Unfinished work

None in the requested one-level split. The new lemma is deliberately statement-only for its later worker. Server dry run and direct push follow this report.

Dry-run repair: opened all six same-tag candidates named by the duplicate checker and added explicit comparisons above. Corrected the etale-openness source tag to 03WT, verified in the local tags table.
