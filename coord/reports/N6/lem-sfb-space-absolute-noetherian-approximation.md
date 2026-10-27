# N6 stage-1 delivery: lem-sfb-space-absolute-noetherian-approximation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-absolute-noetherian-approximation.json: statement, split into ten proof steps; no Mathlib match; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-space-splitting-filtration.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-etaleness-eventual-stage.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-approximation-prescribed-open.json: statement-only, unsplit; no Mathlib match.
- citations.json: a verbatim statement quote for every citation in every item step.

Three new nodes; zero new Mathlib leaves. The scripts and search log in this sandbox are local working records, not library changes.

## Attachments

None for the item. Searching WeilConjectures by the blueprint tag and by algebraic-space/absolute-Noetherian-approximation concepts finds scheme approximation, not the space assertion. The existing prop-nagata-noetherian-inverse-system already records AlgebraicGeometry.Scheme.nonempty_noetherianApproximation; it is reused only for the schematic base case. Its declaration and docstring in WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean were read. The ExtensionData.approximation implementation there extends across one extra affine open; it does not directly state the new arbitrary-prescribed-open lemma. Sheaf geometry was searched for the new ids and concepts as well; no additional attachment is claimed.

## WANTED

None. All proof sources used here are in literature/stacks-project. No SGA source is used.

## What needed repair

The input statement is correct and is retained verbatim. Its proof was empty. The default source reference gives 04ZK for the Noetherian consequence; the proof instead verifies this on its actual finite-type scheme atlas using the existing scheme Noetherian lemma, so it does not create another space-Noetherian lemma or cite an unrelated cotangent-coherence theorem.

The chapter and recorded unit were read, together with the current latest blueprint sk-thm-sf-ctf-stability-direct-images.proof.md. The current high-level direct-images proof is the proper/open preservation route. This assigned node is a generated geometric prerequisite on its existing alteration/finite-surjective-affine-target branch, not the key statement of that unit. No unit or chapter was edited. blueprint_refs.py ancestor reports None for this generated branch, consistently with the supplied node. I preserved its null ancestor and full via/place chain and supplied precise new source places; the server review accepts this representation. Searches of the entire imported blueprint for approximation, Noetherian approximation, filtration, finite filtration, equivalence relation, the relevant tags, and neighborhood/gluing concepts found no blueprint node giving these space results. The scheme approximation node is reused.

During self-review I corrected the descent-situation source tag to 084W, added the existing cofiltered-to-directed reindexing theorem for the scheme base case, added explicit finite-type composition for W_i, and cited the scheme source-locality theorem for the glued etale projections. I also made affineness of the relation transitions explicit before using its limit. All ten steps are below 2000 characters; the item keeps the groupoid construction and comparison arguments instead of moving its conclusion into a new lemma.

## Unfinished

No unfinished part of the item's one-level split. The three new prerequisites intentionally have no proof; they are subsequent stage-1 items. No Lean was written or compiler/build tool run. Nothing was written in the shared repository or launcher.

## Not duplicates

lem-sfb-scheme-approximation-prescribed-open vs lem-nagata-affine-raw-refinement-cofinal: the existing node proves directedness/exhaustiveness of raw coefficient tuples and explicitly asserts no finite-stage gluing conditions; the new node extends an arbitrary supplied open inverse system to schemes and states the limit, cartesian-open and cofinality conclusions.

lem-sfb-scheme-approximation-prescribed-open vs def-nagata-affine-raw-refinement-system: the existing node defines a raw coefficient preorder, with no existence or scheme limit theorem; the new node is an existence theorem for an arbitrary prescribed open approximation.

lem-sfb-scheme-approximation-prescribed-open vs lem-nagata-one-affine-subring-extension: the existing node extends finite marked image-subring models over one additional affine chart and assumes an exhaustive subring system on the old charts; the new node assumes only a scheme inverse system on any qc open, produces a cofinal refinement and compatible ambient schemes, and does not follow by specialization of the marked-subring assertion.

lem-sfb-scheme-approximation-prescribed-open vs def-nagata-finite-affine-subring-model: the existing node defines finite marked subring modelhood and expressly asserts no existence; the new node gives actual ambient finite-type scheme approximations compatible with a prescribed open system.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-eventually-fibre-dimension: the existing node descends a dimension bound for fibres over affine scheme bases, not etaleness of a map over space bases.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-qcqs-base-descend-closed-immersion: the existing node descends closed immersions between finitely presented spaces over qcqs scheme bases; it neither gives etaleness nor allows algebraic-space bases.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-eventually-finite-map: the existing node descends finiteness, not etaleness; a finite map need not be etale.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-eventually-surjective-map: the existing node descends point surjectivity, not etaleness; neither condition implies the other.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-descend-closed-immersion: the existing node descends closed immersions over affine scheme bases, not etaleness over general space bases.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-eventually-flat: the existing node gives eventual flatness over affine scheme bases, not etaleness of a map of spaces over a space base; flatness alone does not give unramifiedness.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-qcqs-base-eventually-proper: the existing node descends properness of finitely presented spaces over qcqs scheme bases, not etaleness of arbitrary qcqs space maps.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-descend-separated: the existing node descends separatedness over affine scheme bases; separatedness alone does not give etaleness.

lem-sfb-space-etaleness-eventual-stage vs lem-sfb-space-eventually-proper: the existing node descends properness over affine scheme bases, not etaleness over arbitrary algebraic-space bases.

The common tag 084W in these last nine pairs describes the setup, not the property being descended. No existing source-tag match for 07ST was found. The existing space-fp-over-space-limit-descent, space-affine-limits-schematic-stages, quotient and atlas criteria are reused rather than restated. None of the three new nodes gives the item's conclusion for a general qcqs algebraic space.

## Review by N6

I read spaces-limits.tex, proposition-approximate (07SU), from its first filtration paragraph through the final presentation identity. For the new filtration node I read decent-spaces.tex, lemma-filter-quasi-compact-quasi-separated (07ST), and its use in 07SU: the opens are qc since they are continuous surjective images of V_p, and the last etale neighborhood is an isomorphism because it is an isomorphism on the reduced whole target. The node includes that terminal schematicity as the source explicitly uses it. This is a finite chart filtration, not absolute approximation itself. For the new eventual-etaleness node I read spaces-limits.tex, Situation 084W and lemma-descend-etale (07SL); the essential local-finite-presentation hypothesis is present on f_0 and all three initial spaces are qcqs. For the prescribed-open node I read limits.tex, lemma-approximate (07RN), including its final J = coproduct P_i construction; each P_i is nonempty after a tail, so the index map is cofinal, not just order preserving. I retained the inverse-image equality of stage opens and compatibility of their projections.

For step 1, the new filtration statement provides all U_p,V_p,f_p and terminal schematicity. I opened space-integral-qcqs-permanence and checked that its statement really includes qc-open quasi-separatedness. The scheme approximation statement provides the system, and the separately cited cofiltered-limit-directed-reindex theorem gives a directed index set without altering objects or transition properties. The finite-type-over-Noetherian statement explicitly includes Spec Z, and locally-noetherian-quasi-separated gives the separation of these scheme stages. Thus this is not an application of a scheme theorem to a space.

For step 2, qcqs-space-fibre-product supplies W's qcqs property. Chartwise-etale-permanence supplies base change of etaleness, and the etale definition supplies local finite presentation. space-qcqs-permanence gives qc and qs of W -> U; these are the finiteness clauses needed to apply the full space-base fp descent node. I opened its statement and checked that it allows B_i to be spaces, unlike the similarly named scheme-base theorem. space-fp-qcqs-source supplies qcqs of W_0, so the hypotheses of the new 07SL node are actually available.

For step 3, flat-proper-fp-locality is used only for its base-change-of-finite-presentation clause. fp-qcqs-source, chartwise-etale-permanence and affine-locality provide the source finiteness and transition properties. affine-limits-schematic-stages explicitly supplies limit/base-change compatibility and eventual schematicity for qcqs stages; W is already an open scheme in V. The finite-type-composition node applies because W_i -> U_i is qc and etale, hence finite type, and U_i -> Spec Z is finite type. The local-properties-chart-test includes agreement with schemes. Therefore the prescribed-open theorem applies to a qc separated scheme V and qc open W. Its cofinality preserves both U and W as limits. I did not assume the new V_i are separated: their finite type over Z gives local Noetherianity and hence quasi-separatedness, which is all the subsequent atlas criterion needs.

For step 4, fibre-products-etale-covers gives the scheme E_i, and chartwise-etale-permanence includes the cancellation used for its diagonal. The etale-monomorphism-open node states precisely the needed open-immersion assertion. glue-schemes supplies a scheme covered by V_i and E_i with their stated overlap. I wrote the relation laws on the charts and their intersections, rather than citing a definition for those laws. The existing etale-local-on-source theorem is a scheme theorem and applies here since R_i,V_i are schemes. Thus no algebraicity of the quotient was assumed before the etale relation was constructed.

For step 5, etale-relation-quotient explicitly gives the algebraic space, surjective etale quotient chart, kernel pair and quotient mapping property. qcqs-space-fibre-product applies to E_i because W_i and U_i are qcqs. space-qcqs-permanence needs R_i qc and V_i qs, both already verified. space-qs-atlas-criterion asks for V_i quasi-separated and one relation projection qc, exactly the properties proved. The chart-test theorem supplies local finite type of the quotient, with its global qc property already established.

For step 6, I wrote the source-cartesian comparison on the actual two open pieces; it is not inferred just from compatibility of relations. The fibre product E_j times_{V_j} V_i equals E_i using both W_i = W_j times_{U_j} U_i and cartesian preservation of W_i inside V_i. Both pieces and their overlap give the asserted comparison. Only the quotient node's stated universal property is used for inducing transitions and testing their equations.

For step 7, I checked the source-cartesian-to-quotient-cartesian claim by local lifts, including uniqueness over the identity relation. The quotient node really states etale local lifting and the kernel-pair identity. Affine locality applies along the surjective etale chart V_j; it would not follow from the topological quotient alone. The space limit node gives the required base-change formula. This identifies V with the pullback of V_0 over X prime and R with its kernel pair; base-change stability of the covering follows from chartwise-etale-permanence.

For step 8, I checked that R_i transitions are affine by the source-cartesian squares, and then applied the space-limit node to the open charts at a fixed stage. This avoids an unsupported assertion that arbitrary inverse limits commute with open pushouts. Only limits of the cartesian stage opens and the elementary universal property of fibre products are used.

For step 9, atlas-presentation is used for its full sheaf quotient and relation identity, not merely fully faithfulness. The original relation has the diagonal and W times_U W as open pieces. Coverage follows because over the reduced complement Z the supplied etale neighborhood is an isomorphism, so every geometric pair is diagonal; equality of underlying open unions gives the actual scheme open cover. Their overlap is precisely W. The gluing maps preserve both projections, so quotient universality identifies X with X prime. This is the end of the induction, not a new lemma assuming its conclusion.

For step 10, the existing scheme finite-type-over-Noetherian statement gives local Noetherianity of each displayed V_i. The item's definition only asks that an etale atlas be locally Noetherian, so no assertion about all atlases is smuggled in. Quasi-compactness and quasi-separatedness of each quotient were already proved. The same check applies to the schematic base case.

I tested the empty X and W, the single-stage system, U = empty and U = X, nilpotent/nonreduced X in the last filtration stratum, and etale charts with multiple sheets. Empty schemes are legitimate stages; the directed sets remain nonempty. The relation on the complement of W is the identity even for nonreduced complements: the relation comparison is made using its open diagonal, and coverage is checked on geometric points, not by asserting that an arbitrary map factors through a reduced closed subscheme. All hypotheses needed by every citation were checked against its statement. The citations file quotes those statements verbatim. Searches were run using msearch.py and their results read; the returned scheme/ring lemmas do not give any new node by one-line specialization. No unavailable service was recorded as absence. New nodes contain statements only, every named notion has an existing definition citation or an inline definition, all proof uses are in proof_deps, and no statement weakening or source dispute was needed.
