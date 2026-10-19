# lem-sfb-alpha-ring-hom — Q05 stage-1 split

## Files written
- dag/nodes/sec-proetale-coefficients/lem-sfb-alpha-ring-hom.json: statement, split; Mathlib has generic transport but not the geometric monoidality assertion needed here.
- citations.json: verbatim statement quotes for all seven distinct cited nodes (eight step citations total).
- report.md: this report. searches.jsonl is produced only by msearch.py.

## Attachments
None. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the blueprint id, isMonHom_condensedPullbackHom, condensedPullbackHom, upperStarFromPointComp and compAlgHom found no corresponding declaration. Upstream master Basic.lean:401 has the direct instance, but its comparison monoidality at :352 has proof sorry. Master is reference material and is not a completed proof.

## WANTED
None. The relevant blueprint statements and proofs and Mathlib source are available locally. No SGA source used.

## Problems corrected or reported
The imported proof named only comparison monoidality and left the general transport fact implicit. Existing det-def-sfb-ring-object-transport clause 3 supplies exactly that fact, so no new node is needed. The proof now explicitly checks that successive and composite transport have the same unit and multiplication, rather than silently identifying ring structures.

The mathematical claim is unchanged: no hypotheses or conclusions are changed. The statement reference sk-def-sfb-finite-pushforward-pullback names a blueprint unit rather than an extant DAG node. After the first dry run rejected that missing-node reference (B3), I replaced it in the statement by the concrete defining child def-sfb-finite-upper-star-monoidal, which is also in stmt_deps and the proof. No chapter/unit JSON record exists for this newly imported section/unit in the shared snapshot; I read the current chapter and unit _section.md files instead and left maintainer metadata untouched. The item is not the unit key node, so no realization record is written.

Blueprint search for monoidal natural, ring objects and alpha found no distinct equivalent theorem; def-sfb-alpha-bundled packages a stronger ring isomorphism and is not used as a proof. det-def-sfb-ring-object-transport is the already-existing general theorem, not a new child. The ring-object tool use is declared in split_report.

## Unfinished
No mathematical gap remains in this one-level split. Its cited existing nodes retain their own stage-1 work. No Lean was written or compiled. No delivery is pushed; the second reader will deliver after the dry run.

## Not duplicates
No new nodes. The generic monoidal-transformation fact is already clause 3 of det-def-sfb-ring-object-transport; it was reused. No clause of the item has been repackaged as a child.

## Review by Q05
I read the current main-20261015 chapter sec-proetale-coefficients/_section.md, the coefficient-morphisms unit statement and its proof, and lem-sfb-alpha-ring-hom.md with its .proof.md. They specify exactly the route used here: transport the coefficient ring along the two strong monoidal functors, then use the monoidal comparison. I also read det-def-sfb-ring-object-transport.md and its .proof.md and the statements of every cited node. There are no new nodes or additional literature sources to audit.

In step 1, sk-def-sfb-pulled-back-coefficients states that both coefficient rings are transported along the point pullbacks, def-sfb-finite-upper-star-monoidal supplies the specified strong structure on f^*, and the transport node gives the explicit unit and multiplication formulas. Expanding the definition of the composite lax structure and functoriality proves the two displayed equalities, so this part is elementary, not a new theorem. All expressions have source the tensor square (respectively the tensor unit) in the category on X and target f^*p_Y^*Lambda. No claim about ring structures is taken from an underlying-object equality alone.

In step 2, def-sfb-pullback-from-point-comp-iso supplies the natural comparison between these exact functors, def-sfb-alpha identifies its component with alpha_f, and lem-sfb-pullback-from-point-comp-monoidal explicitly asserts compatibility with their unit and tensor comparison maps. This is stronger than just having an underlying natural isomorphism and is exactly the necessary hypothesis. The domain is condensed abelian groups and the codomain is abelian pro-etale sheaves; no identification with discrete etale coefficients or completed coefficient categories occurs.

In step 3, clause 3 of the transport node explicitly states that components of monoidal natural transformations are morphisms of the transported ring objects. I checked its hypotheses against step 2, including that both functors have the given monoidal structures. The written naturality and monoidality equalities separately verify multiplication and the unit; clause 2 of det-def-sfb-ring-object-monoid says precisely that these are the defining conditions. I did not cite a definition as if it proved monoidality. citations.json contains the verbatim statements, not excerpts borrowed from proofs.

For delivery-errors B--E: no new unsplit statements, new sources, or new leaves are submitted; existing definitions cover all statement notions. Searches were run using msearch.py and recorded with the exact tool/query and actual hits. The initially unqualified Loogle identifier had zero hits and was retried successfully with CategoryTheory.Functor.mapMonNatTrans. The generic Mathlib declarations were read at Mon.lean:898 and :909; they require the monoidal-transformation hypothesis and hence do not by themselves prove this geometric item. I used the already-existing DAG transport node instead of duplicating a Mathlib/generalization node. All uses are backed by statements, proof_deps is their union, and the argument follows the current unit without any route replacement or SGA reference.

I checked small cases f=id, the zero coefficient ring, and noncommutative coefficient rings: the two preservation identities still make sense and require no commutativity, nonzero condition, properness, or finite-type assumption. Empty schemes also cause no extra hypothesis, since the argument is entirely categorical. The generic fact is stronger (lax suffices); using strong functors here meets all its hypotheses.

## Statement corrected
Only the bracketed reference for the specified strong monoidal structure was corrected, from the absent unit node sk-def-sfb-finite-pushforward-pullback to its existing defining child def-sfb-finite-upper-star-monoidal. This is a reference repair, not a mathematical statement dispute; the structure, quantification, hypotheses, and conclusion are identical to the blueprint. The first dry run reported only this B3 error; the corrected delivery is rerun below.

## Dry-run tool interference
The second dry run, after repairing the only first-run B3 error, failed with out-of-scope changes in the tool-owned temporary delivery: coord/blueprint-index.tsv, coord/queue.md, coord/queue.tsv, def-sfb-finite-lower-star-comp, and det-pe-wlocal-strict-contractible. None is in this sandbox and none was written by this worker. Retrying the required tool rather than editing unrelated shared state.

## Second reading by Q05
I opened the source node and proof (`lem-sfb-alpha-ring-hom.md` and `.proof.md`) and checked the item statement hypothesis by hypothesis: it quantifies the transported ring structure on $f^*\Lambda_Y$ and concludes exactly that [def-sfb-alpha] is a ring-object morphism; verdict: agrees with the source after the recorded reference repair to [def-sfb-finite-upper-star-monoidal].

Step 1 was checked against [sk-def-sfb-pulled-back-coefficients], [def-sfb-finite-upper-star-monoidal], and clause 1 of [det-def-sfb-ring-object-transport]; the displayed composite lax maps and the resulting unit and multiplication are the defining two-line composition formulas, so the elementary marking is appropriate and the transported structures are identified correctly. Verdict: pass.

Step 2 was checked against [def-sfb-pullback-from-point-comp-iso], [def-sfb-alpha], and [lem-sfb-pullback-from-point-comp-monoidal]; these statements identify the exact natural transformation, its component, and its unit/tensor compatibility for the two strong monoidal functors. Verdict: pass.

Step 3 was checked against clause 3 of [det-def-sfb-ring-object-transport] and clause 2 of [det-def-sfb-ring-object-monoid]; the written naturality and monoidality equations establish multiplication and unit preservation with the correct source and target. Verdict: pass.

There are no new nodes in this split, so no new-node B1--B7 review or duplicate search is required; all cited existing statements were opened in the shared DAG and their verbatim quotes were checked in `citations.json`. I also checked the zero ring, identity morphism, empty scheme, and noncommutative coefficient cases; no hypothesis or edge case is lost. No SGA source or Lean/compiler tool was used.

Changes made: retained the worker's concrete replacement of the absent [sk-def-sfb-finite-pushforward-pullback] reference with [def-sfb-finite-upper-star-monoidal], retained the explicit composite-transport and ring-hom equations, and added this second-reading record. No mathematical statement or dependency was otherwise changed.
