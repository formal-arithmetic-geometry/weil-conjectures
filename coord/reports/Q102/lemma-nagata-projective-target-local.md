## Worker report

Files written:

- `dag/nodes/sec-nagata-compactification/lemma-nagata-projective-target-local.json`: statement; Mathlib leaf, no new nodes. The statement is unchanged.
- `citations.json`: empty list, since a Mathlib leaf has no DAG proof steps or cited nodes.
- `report.md`: this report. `searches.jsonl` is the search command's original log.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag, the named locality instance, and properness/locality terminology did not find a project declaration stating this item. The recorded `lean` points into Mathlib and is not a project attachment.

WANTED: none.

The imported proof had two unjudged paragraphs. Its first paragraph correctly names the properness locality instance, but the generic theorem applying such an instance to a family of opens was not recorded. Its second paragraph is a warning about projectivity, not a proof step. This delivery records the complete one-line specialization as a Mathlib match and leaves the proof empty, as required for a leaf. The imported search said that the instance was not found; the current logged Loogle and source searches find it. The immutable source record cites Stacks 08J0 for the warning; the actual properness assertion is Stacks **01W2**, `morphisms.tex`, `lemma-proper-local-on-the-base`. No source metadata or import flags were changed.

Nothing remains unfinished for this item. The item is a Mathlib leaf, so no worker-written proof, new definition, or new subsidiary lemma is needed.

## Mathlib match

I read `Mathlib/AlgebraicGeometry/Morphisms/Basic.lean`, lines 111–154, including the namespace and hypotheses. `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top` at lines 146–154 says that, for any target-local morphism property P, an arbitrary family of target opens whose supremum is top and whose restrictions satisfy P implies P(f). With P = `@AlgebraicGeometry.IsProper`, this is exactly the item:

`AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top (P := @AlgebraicGeometry.IsProper) V hV hproper`.

The only inferred property instance is `AlgebraicGeometry.IsProper.instIsZariskiLocalAtTarget` in `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, lines 77–79. I read its proof and the definition of `IsProper` at line 42: separated, universally closed, and locally of finite type. The file explicitly notes that quasi-compactness follows from universal closedness. There is therefore no change of mathematical properness convention requiring an additional comparison theorem. The variables called X and Y in Mathlib are merely reversed relative to the item's names; the restricted morphism is precisely the morphism from the inverse-image open to its target open.

All six searches in `mathlib_searches` were run with the provided `msearch.py`; their tools and query strings agree with `searches.jsonl`. LeanFinder returned both the instance and generic cover theorem. Loogle returned the instance. LeanSearch returned the properness definition and related properties but not the direct cover theorem. The first source grep found the instance. A single-file Basic grep returned introductory documentation hits, so a directory grep was run and located the actual generic theorem at line 146. The recorded results distinguish these cases rather than claiming the documentation hits were declarations. No search service was unavailable.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs requiring a distinction. Whole-blueprint searches for “Properness is local”, “proper morphisms”, and “properness”, and DAG searches for the proper-locality label and terminology were read. The exact properness-locality statement is already this imported node; it is retained rather than copied. Other nodes citing the Stacks lemma for projective-bundle properness do not change this leaf's identity. `blueprint.same_as` is empty; `blueprint.from` remains null because this is an imported blueprint node.

## Review by Q102

I read the chapter and `sk-lem-nagata-sketch-blowups` unit records, the item's original master blueprint statement and proof, and the current `main-20261015` statement and proof. Both snapshots say properness, not projectivity, and have the same statement. The leaf realizes the locality paragraph used to assemble properness from local blow-up charts without changing the unit route or its key statement. This item is not the unit's key node, so the unit realization record is untouched.

For the literature check I read Stacks Tag 01W2, label `lemma-proper-local-on-the-base` in `literature/stacks-project/morphisms.tex`. Its second condition is the existence of an open cover on which all restrictions are proper, and its first condition is properness of the original morphism. The requested direction is exactly (2) ⇒ (1). Its proof is marked omitted, which would require an explicit argument for a non-Mathlib split; here the fully stated generic theorem and the properness instance already give the entire result in one line. The project's source pointer to 08J0 pertains only to its separate projectivity warning and is not used as evidence for properness.

There are no delivered proof steps, so C1/C3/C4 have no node citations to audit and `citations.json` correctly has no entries. Instead I checked the actual theorem statement: its hypotheses are solely target locality, an open-cover equation, and P of each restricted morphism. The properness instance supplies the first, the given cover supplies the second, and the item's hypothesis supplies the third. No conclusion was inferred from the proof of another DAG node, and no theorem was inferred from a definition node. No step longer than 2000 characters remains.

I checked the limiting cases explicitly. A singleton full-target cover gives the original properness hypothesis back. Empty members of a cover are allowed. An empty indexing family can cover only an empty target; any scheme mapping to that target is empty as well, and the theorem still applies. Infinite covers are permitted by the unrestricted indexing parameter; no finite subcover, affine intersection, Noetherian base, or separated-base hypothesis is introduced. The morphism is always the inverse-image restriction, not a map formed just from containment of its image. There are no new statements to test separately and no statement dispute.

Against B–E: the only delivered node already existed and introduces its morphism and cover; its TeX and statement are preserved. Its Mathlib declaration, file, line, specialization, and inferred instance are explicit. No statement-only subsidiary nodes, restatements, or elementary helper nodes were created. Removing the imported paragraphs in favor of a Mathlib leaf avoids an unjudged elementary flag and a non-proof warning. All metadata outside the split-owned fields is retained. This review required no Lean writing, compiler, Lake, repository mutation, or other agents.

The first dry run rejected a null `proof_origin` even for this existing Mathlib leaf. I retained the imported blueprint provenance with `by: agent` and an explicit place for the locality specialization; this records its source without adding proof steps or changing the match.
