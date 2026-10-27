## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-representable-lqf-calculus-descent.json: the item, split into ten proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-lqf-cancellation.json: statement-only scheme cancellation input; Mathlib candidate, not an exact leaf with the Stacks definition.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-lqf-fpqc-descent.json: statement-only scheme fpqc descent input; no Mathlib match.
- citations.json: every step/node pair, with the verbatim cited statement.

Attachments: none. Searches for the exact blueprint tag and representable algebraic-space/stack quasi-finiteness in lean/WeilConjectures found no declaration giving the item. Scheme quasi-finiteness declarations do not prove this stack statement.

WANTED: none.

The supplied node had no proof. Its source references correctly give the asserted mathematics. The statement contained literal doubled TeX backslashes, now reduced to single TeX commands; no mathematical hypothesis or conclusion changed. The proof of Stacks 04XD has a typographical covering-map error: it calls the map T times_Y V to T an fppf covering, although the covering map is T times_Y W to T. The latter is the base change of the covering W to Y. Our final step uses H=V times_B T to T, never the pullback of the source of f. This matters for the empty map f: empty to Spec k: the source pullback cannot cover a nonempty target.

No work remains on this split beyond independent maintainer review. The two new inputs deliberately have no proof, proof dependencies or proof origin. Their eventual splitting is separate stage-1 work.

## Sources and searches

Read stacks-properties.tex, lemma-property-spaces-too (04XC) and lemma-check-property-covering (04XD); spaces-morphisms.tex, definition-locally-quasi-finite (03XJ), lemma-local-source-target (03MJ), lemma-quasi-finite-local (040Z), lemma-composition-quasi-finite (03XK), lemma-base-change-quasi-finite (03XL) and lemma-permanence-quasi-finite (03XN); spaces-descent.tex, lemma-descending-property-quasi-finite (0427). For the new nodes read morphisms.tex lemma-permanence-quasi-finite (03WR), and descent.tex lemma-descending-property-quasi-finite (02VI), respectively, including their proofs. Source labels and tags were checked in tags/tags.

The current latest blueprint unit and direct-image proof were read. The inherited ancestor is null, also reported by blueprint_refs.py ancestor; its long from.place and via chain identify the quasi-DM atlas auxiliary input below direct-images (3). That original provenance is retained. New nodes refine the scheme arguments explicitly used in the Stacks space-chart proofs. No unit or chapter route is changed.

Whole-DAG title/statement/source searches covered all five original tags, 03WR, 02VI, local quasi-finiteness, cancellation, descent, permanence, composition and presentations. Whole-blueprint searches used quasi-finite, locally quasi-finite, 03XN, 0427, permanence-quasi-finite, 03WR and 02VI. No blueprint node states the new scheme inputs. Existing lem-a1-scheme-lqf-composition, lem-a1-scheme-lqf-etale-source-locality, lem-weil-pbc-separated-lqf-base-change and the generic presentation/fppf-conversion inputs were reused. The existing quasi-finite fppf-descent bundle imposes quasi-compactness/finite type, so it does not supply descent of local quasi-finiteness here.

Every recorded Mathlib query was actually run with msearch.py, and its hits read. The search log remains searches.jsonl. Cancellation semantic queries found Mathlib LocallyQuasiFinite.of_comp and locallyOfFiniteType_of_comp. Their sources were read at Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean:103 and Morphisms/FiniteType.lean:72. Mathlib explicitly says its LocallyQuasiFinite omits local finite type (QuasiFinite.lean:20--23,57--59). The project comparison Scheme.Hom.isLocallyQuasiFinite_iff in WeilConjectures/AlgebraicGeometry/QuasiFiniteMorphismComparison.lean:62 is a separate comparison theorem, not a Mathlib declaration. Thus the new Stacks-meaning scheme cancellation node is left unsplit with the candidate documented, instead of falsely claiming an exact Mathlib leaf. For scheme descent two semantic phrasings, Loogle and source greps returned only unrelated composition/base-change/class results or no hits, not fpqc descent. Item searches likewise returned scheme-only results and no algebraic-space/stack source declaration.

## Not duplicates

lem-sfb-scheme-lqf-cancellation vs lem-sfb-representable-lqf-calculus-descent: the new input is cancellation only for schemes, below the compatible-chart proof of the item's algebraic-space cancellation and representable stack calculus; it neither assumes nor states an algebraic-space or algebraic-stack result.

lem-sfb-scheme-lqf-cancellation vs lem-sfb-space-lft-cancellation: the existing node only cancels local finite type, without the zero-dimensional-fibre/quasi-finiteness assertion. It cannot supply the new input's conclusion.

lem-sfb-scheme-lqf-fpqc-descent vs lem-sfb-space-four-property-fppf-descent: the existing quasi-finite assertion includes finite type/quasi-compactness and does not give local quasi-finiteness for a non-quasi-compact map. The new input is scheme-only and works for fpqc covering families.

lem-sfb-scheme-lqf-fpqc-descent vs lem-sfb-representable-stack-fppf-locality: that node states a stack target-cover test for quasi-finiteness with finite type, not scheme fpqc descent for local quasi-finiteness. Neither provides the other statement as a specialization without further mathematics.

## Review by Q53

I opened the source labels above, both new statement files, and the statement of every node used by the item. I checked each use against the statement, not the dependency's proof; citations.json contains those statements verbatim. In particular the general presentation criterion is a conditional theorem: our proof first verifies all its scheme-locality hypotheses, rather than citing it as if it listed local quasi-finiteness unconditionally.

Step 1 uses the precise locally-quasi-finite definition, scheme etale source locality (both implications), clause (2) of separated-lqf-base-change (no separatedness assumed), scheme composition, and the new scheme cancellation input. Identities and isomorphism invariance follow on the affine witnesses. The two substantial new inputs are scheme results strictly below the chart/stack assertions; neither is a relabelling of an item clause.

Step 2 checks the exact pointwise condition (iii) of the generic presentation criterion: the etale map onto its open image is surjective, and etale-source descent applies to the restriction of f to that open scheme. The open-image lemma is used after regarding schemes as their representable algebraic spaces. This repairs the otherwise unjustified jump from one etale chart to a Zariski neighbourhood. Conditions (i) and (ii) are established in Step 1. The resulting criterion gives every compatible diagram, and a single surjective-source diagram suffices; target-chart surjectivity is not silently demanded by that theorem.

Step 3 explicitly constructs three compatible scheme presentations through W, V, U. The two generic space-pullback/etale-calculus nodes provide the required etale and surjective composites. Scheme composition proves one implication; the new scheme cancellation theorem proves the other with no assumption on the second map. This is the actual argument of 03XN rather than an algebraic-space cancellation node identical to the item's last clause.

Step 4 uses two successive target-atlas pullbacks, ensuring U' is a scheme and the maps U' to the new source and V' to the new target really are surjective etale. The scheme map U' to V' is an ordinary base change. No separatedness, quasi-compactness or finite-presentation hypothesis enters this argument.

Step 5 pulls the open cover back to U, where the pointwise affine definition proves locality. The generic chartwise stack calculus is cited for the definition of an open source cover, and the scheme open-immersion/etale lemma justifies the reverse-direction presentation. The argument works when the cover is empty and the source is empty.

Step 6 uses the actual definition of an fppf family and the fppf-to-fpqc family theorem. It never treats a flat lfp surjection as quasi-compact. Taking a scheme atlas E of Z reduces the assertion to scheme descent of E to T. The new descent node assumes exactly that all the pullbacks of E to the fpqc covering are locally quasi-finite; the chart criterion proves that premise. It then returns local quasi-finiteness including local finite type, not just Mathlib's weaker class.

Step 7 uses representable pullback over an arbitrary algebraic space, which its cited statement explicitly allows, with no atlas hypothesis on the base map. The two-stage etale chart gives both directions of the scheme-test/space-chart comparison. The fibre-product identification here just removes a redundant identified object using the stated triple definition; no unquoted stack theorem is needed.

Step 8 uses the general fibred-groupoid representability theorem, whose statement explicitly allows arbitrary base-changing categories, and the algebraic-stack-fibre-product theorem for the ambient objects. The map on triples is spelled out, so arbitrary stack base change is not confused with scheme base change.

Step 9 uses Step 7 on the algebraic space B_T, not the scheme-only defining test without justification. Space composition was proved in Step 3. For open locality the cited definition of open covers is stable on every scheme test, and Step 5 applies.

Step 10 checks q's given representability, surjectivity, flatness and local finite presentation after a scheme test. The atlas D of H makes D to T a surjective flat lfp scheme map by the cited calculus. The displayed beta-inverse formula gives the isomorphism over D with both projections respected; its inverse is composition with beta. This verifies the hypotheses of Step 6 and uses the correct covering H to T, even if f has empty image. Forward descent is Step 7. All non-elementary facts in these steps are cited nodes or conclusions of earlier numbered steps. No step exceeds 2000 characters.

For the new cancellation statement, I tested identity second maps, empty source, arbitrary intermediate maps, and open immersions. No separatedness of the intermediate map is needed (03WR explicitly imposes none). For the new descent statement, identity covers, empty target/empty covering, field extensions, disjoint unions with infinitely many components, and a non-quasi-compact fppf surjection all fit. An infinite disjoint union of points is locally quasi-finite over a field and need not be quasi-finite: this is why the existing quasi-finite bundle could not be substituted. For the item, A1 to Spec k fails local quasi-finiteness on both sides of a target cover, and empty/identity maps pass. Stack automorphisms are not silently discarded: representability supplies algebraic spaces and the triple formulas retain the specified isomorphisms.

B--E checks: both new nodes introduce all objects, use TeX, cite the scheme/cover/quasi-finiteness definitions, have no embedded proof and carry their own logged searches and inherited blueprint location. All tag-sharing pairs found by the delivery gate will be distinguished explicitly if any further pair appears. Off-unit statements are generic scheme/chart/cover tools, declared in split_report.tool_uses for maintainer judgement. I made no unit/chapter/target changes, wrote no Lean, ran no compiler, used no SGA, and wrote only inside the assigned sandbox.

## Source error

In the proof (not the statement) of stacks-properties.tex Tag 04XD, the displayed left covering is T times_Y W to T. Its following sentence instead writes T times_Y V to T. The latter need not be surjective when f is not; f: empty to Spec k and W=Spec k is an explicit counterexample to that claim. Step 10 uses the correct base change of the given cover. This changes no assertion of our item.

## Dry-run repair

The first dry run rejected step 10 for the phrase "as in the item" (B2). I replaced it by the explicit representability assumption on f and all assumptions on q, including that V is an algebraic space. No mathematical argument changed.
