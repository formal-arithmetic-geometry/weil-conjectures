# Q85 stage-1 delivery: lem-sfb-space-flat-deformation-properties

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-deformation-properties.json: item split into eight steps; all three equivalences and every hypothesis retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-fibre-flat-module.json: statement-only unsplit input, Stacks 06A5; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-algebra-fp-lift.json: statement-only unsplit affine algebra input, Stacks 06AG clause (13); no Mathlib match.
- citations.json: one verbatim statement quotation per step/dependency pair.

## Attachments

None. Searched WeilConjectures by the exact blueprint tag and by flat deformation, thickening, nilpotent, finite presentation and related words. No project declaration states all three algebraic-space equivalences. The existing flat-fibre etale criterion is used through its existing DAG node, not proposed as an attachment for this item. The private injective_of_flat_surjective_nilpotent_ker in BijectiveQuotientMapPowOfFlat.lean states a different flat quotient-map result and does not prove either new input.

## WANTED

None. All mathematical sources used are present in literature/stacks-project.

## Errors and changes

The imported statement is faithful to 0CG6 with a first-order specialization of its finite-order base hypothesis. No STATEMENT-DISPUTED and no change of statement or statement dependencies is needed. The item had no proof. Its bibliography gives the right clauses: isomorphism (3), quasi-compactness (5), quasi-separatedness (7), local finite presentation (14), properness (21).

The existing flat-deformation-lfp is insufficient for the charts: it concerns the structural morphism of a flat scheme to an affine base, whereas W prime -> V prime need not be flat over V prime until the isomorphism argument. The target V prime is not assumed flat over U prime. The new presentation input explicitly requires only C prime to be flat over R prime. The existing proper-nilpotent-base-change-reflection is likewise scheme/affine-base only; it is not cited as an algebraic-space theorem.

The initial finite-presentation grep used RingTheory/FinitePresentation as a directory even though Mathlib has FinitePresentation.lean. The search command reported zero hits. I retained that actual output, explicitly identified its limitation, and superseded it with a successful grep over RingTheory. No unavailable service is recorded as absence, and every new query in the nodes was actually executed by msearch.py. The item retains all inherited search evidence and adds the current queries. Search-0.txt through search-15.txt preserve the actual output; searches.jsonl is the command's own log.

The inherited blueprint.from.node is null: blueprint_refs.py ancestor prints None. I retained that result and the full via chain, prepending this item on the two new nodes. The latest blueprint unit and direct-images proof were read in literature/blueprint/latest; the present item is a supporting geometric obligation below the inherited proof-(3) alteration/curve-moduli chain, not a replacement of a unit step. Other-unit generic tools are declared in split_report.tool_uses, never in the maintainer-owned field.

## Not duplicates

lem-sfb-relative-flat-algebra-fp-lift vs lem-sfb-flat-deformation-lfp: the existing node fixes the target to Spec A, flatness over that target, and its own reduction; the new node has an arbitrary intermediate algebra A over a different ring R and assumes only C flat over R. It lifts the relative A-algebra presentation without assuming A flat over R. The existing node cannot be applied to C over A since the required A-flatness is absent.

lem-sfb-relative-flat-algebra-fp-lift vs lem-sfb-space-flat-deformation-properties: the new input is strictly the affine commutative-algebra relation-lifting argument. It gives neither the space chart descent, topology/diagonal assertions, properness nor isomorphism. The item's steps do that work.

lem-sfb-relative-flat-algebra-fp-lift vs lem-sfb-curve-smooth-locus-deformation-test: the latter mentions 06AG within supporting proof material but states a smooth-locus criterion for the curve moduli stack, not a relative algebra presentation lifting lemma.

lem-sfb-nilpotent-fibre-flat-module vs lem-coef-infinity-parameter-cone-extension: the shared identifier 06A5 is a namespace collision; the latter cites Kerodon 06A5 for extension of quasicategorical cocones, not Stacks algebra 06A5. Its statement is unrelated to ring-module flatness.

lem-sfb-nilpotent-fibre-flat-module vs lem-coef-infinity-fiber-cocone-simplex-extension: this node also uses Kerodon 06A5 for quasicategories, not Stacks 06A5 for flat modules.

lem-sfb-nilpotent-fibre-flat-module vs lem-coef-infinity-kan-mapping-restriction: again the identifier is from Kerodon, and the statement is about mapping/restriction of infinity categories, not rings or nilpotent ideals.

Neither new node is a clause merely renamed: flatness of h prime is not a conclusion of the item and is used only on charts for the isomorphism argument; the relative algebra input is used within the local-finite-presentation chart argument and leaves the whole passage to spaces and global finite presentation to the item. Neither is a two-line consequence of the cited existing nodes. Whole-DAG keyword/tag searches, whole imported-blueprint searches (deformation, thickening, nilpotent, finite presentation, flat module, 06A5, 06AG, 0CG6, flat deformation), and Lean-source searches found no existing statement covering these inputs. Existing space topology, scheme local finite type, affine criterion, chart locality and etale detection nodes are all reused instead of being duplicated.

## Review by Q85

I read spaces-more-morphisms.tex, lemma-deform-property (Stacks 0CG6), including its chart reduction, topology paragraph, isomorphism argument and properness reference. I also read lemma-thicken-property-morphisms (09ZY), lemma-thicken-property-morphisms-cartesian (09ZZ), the scheme lemma-deform-property (06AG), especially general remark (I) and the proof of clause (13), and algebra.tex lemma-criterion-flatness-fibre-nilpotent (06A5). For the etale alternative at the end I read morphisms.tex lemma-etale-flat-etale-fibres (02GM); the existing etale detection node supplies the final use of 05ZH. No SGA source is used.

For the new flat-module node, 06A5 applies with S=S prime=A and an arbitrary A-module M. Its first conclusion is precisely the statement I extracted; the additional localization-flatness conclusion of the source is not needed. In particular there is no finite-presentation or Noetherian assumption to add. For the new presentation node, I checked 06AG's affine diagram: R prime -> C prime is flat, while R prime -> A prime need not be. The displayed kernel reduction is exact because the quotient C prime is R prime-flat; the source then lifts finitely many generators of the kernel and uses nilpotent Nakayama. Lifting algebra generators precedes this argument. That is a substantial algebraic lemma, so it is left as a statement-only node, not hidden in an elementary step. The reverse direction is reduction of a finite polynomial presentation.

Step 1: I opened and read the statements of def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers, lem-trf-space-representable-etale-scheme-tests, lem-sfb-space-flat-proper-fp-locality, lem-sfb-space-local-properties-chart-test, lem-weil-pbc-quotient-base-change-closed-immersion-ideal and lem-weil-pbc-flat-morphism-affine-criterion. They respectively give the atlas, the pulled-back covers, composition of representable etale charts, base-change flatness, the precise two-atlas chart criterion, affine quotient coordinates, and flatness of the coordinate algebra. I checked that W prime -> U prime is flat via the chart test on the already flat pullback of P prime, not from an unsupported assertion about etale composition. The charts need not be quasi-compact. Refining by affine opens is allowed pointwise.

Step 2: I checked the statements of lem-sfb-space-thickening-base-change and lem-sfb-space-thickening-topological-properties, and the fibre-product node. Base changes of a thickening are thickenings; the topological-properties node states each of the four equivalences taken from it, even without a cartesian square or finite order. The cartesian identification is written explicitly and does not confuse the two fibre products. Products of images of the base ideal show the square-zero condition after every scheme test; no flatness is used for it.

Step 3: I checked lem-weil-pbc-thickening-lft-cartesian: it assumes a finite-order target thickening and exactly a cartesian source. Both are present on W subset W prime and V subset V prime. The space-local-properties-chart-test statement says precisely how the two scheme chart maps detect the property. It does not require h prime itself flat, nor an affine or Noetherian base.

Step 4: I checked the statement of the new relative algebra lemma, the statement of lem-weil-pbc-lfp-affine-opens-finite-presentation, the affine definition def-sbc-locally-finite-presentation, and the chart-test node. The affine-opens result is essential: local finite presentation on the reduced charts gives a finite presentation on the selected compatible affine opens. Applying the new algebra lemma then gives local finite presentation on the unreduced charts, and conversely. This avoids applying the old flat-deformation-lfp with the unjustified assumption that C prime is A prime-flat.

Step 5 is just conjunction of the already established components with the definitions written in the item's statement. It uses no new theorem and creates no node for a definitional assembly.

Step 6: I checked the scheme-test lemma says the atlas W -> P times_Q V is etale as a scheme map when h is an isomorphism. The definition of etale supplies flatness and local finite presentation, not a hidden fibre criterion. The affine flatness criterion produces C flat over A. The new 06A5 node takes C prime flat over R prime and C prime/IC prime flat over A prime/IA prime; both are now established. It concludes precisely C prime flat over A prime. Neither Q prime nor V prime is silently assumed base-flat.

Step 7: I read the statements of the etale-base-change-finite-limits node, lem-sbc-flat-fibre-etale-neighbourhoods, and lem-sfb-scheme-etale-source-target-properties. The first gives the etale fibre, the second gives etale source neighbourhoods for a flat locally finitely presented map, and the last assembles them on the source. Every residue-field map factors through the reduction because a square-zero element maps to zero in a field; the cartesian fibre comparison is a direct fibre-product identity. The empty-fibre case is covered explicitly by the neighbourhood criterion's statement. There is no residue-field identification based merely on a homeomorphism.

Step 8: I checked representable-etale composition and lem-trf-space-etale-source-atlas-detection. The latter's atlas has to be a representable surjective etale map; step 1 gives exactly that for W prime -> P prime. The conclusion is chartwise etale, exactly the hypothesis of lem-sfb-space-etale-thickening-detects-iso. Its thickening is Q -> Q prime and its tested base change is h, not just P -> P prime. Pullback of an inverse proves the easy direction elementarily. This retains the source's etale reduction and replaces its surjective-open-immersion ending by the existing equivalent topological-invariance detector, below the unit level.

I checked the new statements on I=0, M=0 and the zero algebra: the flat-module criterion reduces to its existing flatness hypothesis when I=0, and is valid for zero modules; presentation lifting becomes tautological when I=0, and zero algebras have a finite presentation. The assumption of base flatness cannot be dropped: for R=k[epsilon]/epsilon^2 and M=k, with A=R and I=(epsilon), the reduction is flat over k but M is not R-flat. For presentation lifting, take R=k direct-sum V with V square zero and infinite-dimensional, A=R, C=R/V=k: its reduction modulo I=V is finitely presented over k, while R -> k has infinitely generated kernel and is not finitely presented. C is not R-flat, as required to exclude this example. Allowing a nonflat intermediate algebra is necessary and consistent: R=k[epsilon]/epsilon^2, A=R[x]/(epsilon x), C=R by x=0 has C R-flat and finitely presented over A, though A is not R-flat.

For the item I checked B=B prime (identity thickening), empty P, empty B, and arbitrary non-quasi-separated charts. An isomorphism onto an empty Q forces P empty; the thickening homeomorphisms preserve emptiness. No finiteness of the atlases is introduced. Every proof step is shorter than 2000 characters; the two substantive hidden algebra arguments were extracted, and the elementary steps only compare fibre-product points, multiply square-zero ideals, or assemble established equivalences. Every citations.json quote is verbatim from the cited statement, so the quoted part is independently inspectable. The first dry run found that a concurrent live update had added definition citations to the thickening base-change statement; I reread the updated statement and narrowed that quote to the unchanged base-change assertion actually used by step 2. Its mathematical content and this split were unaffected.

## Unfinished work

No part of this one-level split remains unfinished. The two new statement-only algebra inputs intentionally remain unsplit, as required. No Lean was written and no compiler, Lake, build, or local preflight/check_dag/review_split was run. The delivery dry run runs the required checks on the server.
