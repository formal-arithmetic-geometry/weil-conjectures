# Q111: lem-sfb-profinite-action-trivial-parameter-fixed

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-trivial-parameter-fixed.json: existing statement, now split into seven proof steps; not a Mathlib leaf.
- citations.json: a verbatim statement quotation for each of the twelve step/node citations.
- searches.jsonl: actual msearch results; the item retains its earlier imported search records and adds the seven searches run for this delivery.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written or compiled.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, trivial-parameter terminology, fully fixed sections and profinite action found no declaration stating the item. The two unrelated fixed-sections hits concern Picard cochains and formal kernels.

## Sources and WANTED

WANTED: an external non-SGA reference for the internal representable profinite-group action presentation, specifically restriction on trivial parameters and its direct-image interpretation. This was already WANTED in the item's source; the proof here is explicitly agent-written, not attributed to Stacks or to a theorem in the blueprint. I read paragraph (3) of literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md and the chapter/unit records. That paragraph is the direct-image route motivating the auxiliary infrastructure, and does not state this lemma. Stacks 00W0 is only the ordinary discrete-group analogue and is not used as evidence for internal profinite actions. No SGA source is used.

## Errors and changes

The item had a statement and search history, but no proof. Its statement is retained verbatim, with no weakened clauses or added hypotheses. The repair below also cites the existing site definition for the sheaf criterion in step 1. The general profinite-action presentation is not cited: it already depends on this item. In particular the proof does not use an equivalence which this lemma is supposed to help establish. The module-lift sibling is also unnecessary: the scalar assertions follow directly from the explicit inverse free-evaluation formula.

The inherited blueprint.from.node is null. The prescribed ancestor command likewise prints None. I preserve that inherited value and its already precise place, rather than fabricate an ancestor. Whole-blueprint searches for invariants, Yoneda, trivial and profinite found no blueprint statement equal to this item; same_as is [].

## Not duplicates

No new nodes were created. The finite-cover-site statement is reused for preservation of covers and finite limits; the Yoneda/free-evaluation statement is reused for the section subset and both map formulas. No elementary assertion was promoted to a node.

## Review by Q111

I read all of delivery-errors B through E against the saved node and the statements in citations.json. There are no new standalone statements needing a separate source or small-case test. The item's source and the current blueprint paragraph were read as described above; each cited auxiliary statement was opened in the live DAG. All proof steps are shorter than 2000 characters.

Step 1 uses the sheaf equalizer criterion of def-weil-pbc-sites-and-cohomology and uses lem-sfb-profinite-action-finite-cover-site exactly for the claim that t preserves finite limits and covering families. Its hypotheses are the same compatible universes and compact Hausdorff totally disconnected J as the item. Applying the sheaf matching-family condition along t, with the identified fiber products, proves restriction is a sheaf, including the empty cover. No general continuity theorem is silently imported.

Step 2 uses the Q_X(T) formula of lem-sfb-profinite-action-yoneda-free-evaluation, which is a subset equality on the entire profinite J times T. For tS, its two maps to S are the same projection. Pulling back along the actual continuous map (g,f), and conversely testing at (gamma,pi), proves exactly the every-base-change condition. This does not replace continuous sections of J by constant elements or points.

Step 3 takes the restriction and postcomposition formulas from that same cited statement. The definition of actions and trivial inflation is in lem-sfb-action-topos-geometric-restriction. Factoring an equivariant map from a trivially acted-on sheaf through the fully fixed subset is checked by the displayed equality for an arbitrary f and g. The inverse is composition with the inclusion. This is an explicit factorization argument, not an invocation of the ordinary group representation adjunction.

Step 4 uses only the specified p_J adjunction in lem-sfb-action-topos-geometric-restriction and step 3. It writes both comparison maps and checks both inverse identities, one by injectivity of the fixed-subset inclusion and the other by injectivity of the adjunction hom bijection. This also verifies canonicity and naturality, without citing a theorem of uniqueness whose statement might omit the required comparison.

Step 5 uses the definition in def-sfb-condensed-action-module for sectionwise linear action and for the injective, precisely fully fixed image of a normalized invariants inclusion. The Yoneda statement supplies identity evaluation. The scalar-and-sum calculation proves closure and the linearity of trivial evaluation. It assumes no existence of a chosen invariants datum beyond the conditional datum in the item.

Step 6 uses exactly the inverse free-evaluation formula from lem-sfb-profinite-action-yoneda-free-evaluation. Applying the sectionwise R-linear action from def-sfb-condensed-action-module proves multiplication compatibility with scalars; the same formula proves sums and units. No module equivalence or sheafification comparison is used.

Step 7 uses the explicit morphism and parameter naturality clauses of the Yoneda/free-evaluation statement; it gives the actual free comparison equation and the substitution (a,f composed with b). Naturality of the normalized-invariants comparison follows through its specified natural inclusion, whose injectivity is stated in def-sfb-condensed-action-module. Thus every continuous parameter map is covered, rather than merely point inclusions.

I tested J=1 (every section is fixed and both evaluations reduce to the underlying section functor), empty S (the sheaf has its unique empty section and all formulas agree), the zero ring/module (all module comparisons are the unique ones), and a nontrivial finite group acting on a constant sheaf (the trivial evaluation retains precisely invariant values, while free evaluation retains every value). The proof uses compactness only through the pre-existing profinite-site input; it does not require finite J, discrete action, or a uniform open stabilizer. The all-base-change quantifiers are retained throughout.

The Mathlib hits were read as reported by msearch. I additionally opened Mathlib/RepresentationTheory/Invariants.lean at lines 250--298: invariantsAdjunction at line 276 is for an ordinary group acting over one fixed commutative ring, not a group sheaf and parameter-dependent section rings. The condensed hits are forgetful/site and locally constant functor comparisons, not this internal action statement. Both natural-language phrasings were searched, as well as Loogle and grep. No search was invented or recorded as absent when unavailable.

## Unfinished work

None for this one-level split. Existing cited nodes retain their own stage-1 obligations; they were not edited.

## Returned delivery repair (2026-10-23)

The returned head was b51cdf5f02b; the retained sandbox contains its seven-step split, report, citations and seven logged searches. The return was a side-completion promotion failure, not a mathematical rejection. I compared this retained split with the current shared live item: the live node is unsplit with empty proof and proof dependencies and no proof origin; its statement, statement dependencies, source, chapter, unit, created record and blueprint metadata agree with the retained version. There is no released repair note for this item. The initial required dry run rebased the retained work through deliver.py onto current origin/sheaf-dag and passed at b6fdb3e8d85.

I reread every current statement cited by the retained proof: lem-sfb-profinite-action-finite-cover-site, lem-sfb-profinite-action-yoneda-free-evaluation, lem-sfb-action-topos-geometric-restriction and def-sfb-condensed-action-module. Each retained quotation is the entire current statement, byte for byte; hence no cited statement has changed relative to the delivery's saved citation evidence. The site lemma still preserves trivial-action covers and finite limits, the Yoneda lemma still gives the whole-parameter equation and inverse free-evaluation formula, the action-topos lemma still gives the trivial-inflation adjunction, and the module definition still specifies fully fixed images and natural inclusions. Their split statuses do not change what their statements supply.

This is not an unchanged re-push. I reconstructed the sandbox item from the current live record while retaining the owned split fields, added the existing site definition as a step-1 citation to state exactly which sheaf criterion is used, wrote the restriction-stability and hom-set naturality arguments in step 3, and wrote the explicit counit-comparison naturality equation in step 4. The new site-definition citation was read in full and its equalizer sentence copied verbatim into citations.json. These refinements introduce no new lemma or mathematical hypothesis. They preserve the proof route, all seven previous arguments, the source attribution and search history.

I repeated the B--E review on the repaired proof: all twelve citations have matching statement text; the three new explicit calculations are elementary consequences of the cited statements, rather than hidden general comparison results; all steps remain below 2000 characters. The empty parameter, trivial group and zero module tests remain valid, as does the finite nontrivial action test. The item is still an agent-written auxiliary lemma with its inherited WANTED reference, not a theorem claimed from the blueprint or SGA.
