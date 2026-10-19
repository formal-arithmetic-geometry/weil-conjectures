# Stage-1 split: lem-sfb-modobj-extension-right-exact

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-modobj-extension-right-exact.json`: statement, split; no direct Mathlib match for this particular module-object functor. Reuses the reviewed Mathlib leaf `lem-weil-pbc-left-adjoint-preserves-colimits` and the Mathlib definition node `def-galois-finite-limits-colimits`.
- `citations.json`: verbatim statement excerpts for the three step citations.
- `report.md`: this report.

Zero new nodes; zero new Mathlib leaves. The existing statement is unchanged.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint id, expected declaration name, `extendScalars`, and extension-of-scalars terminology found only ordinary module/sheaf scalar extension and related constructions, not the item's functor on module objects in a general braided monoidal category. This item has no `lean_audit` field and no `blueprint_update` field in the supplied node. The upstream-master declaration `CategoryTheory.Mod.preservesFiniteColimits_extendScalars` exists at `WeilConjectures/CategoryTheory/ModuleObjects/ChangeOfScalarsSquare.lean:160` and has the expected hypotheses, but upstream master is reference material under the brief and is not attachment evidence.

## WANTED

None.

## Corrections and source audit

The imported proof omitted the node for the non-elementary implication that a left adjoint preserves colimits. I supplied the existing node `lem-weil-pbc-left-adjoint-preserves-colimits`, rather than creating a duplicate. It is already a reviewed Mathlib leaf, matching `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`, `Mathlib/CategoryTheory/Adjunction/Limits.lean:92`; I read its declaration and surrounding variables at lines 44–98. Its source is Stacks Tag 0038, `categories.tex`, label `lemma-adjoint-exact`, part (1). I read both that assertion and its proof, lines 3472–3506, and confirmed the tag in `stacks-project/tags/tags`.

The current blueprint's lemma statement and separate `.proof.md` agree with the node. I read the chapter `_section.md`, the unit `sk-def-sfb-change-of-scalars/_section.md`, and its separate proof. The split follows unit part 2 exactly: use the extension/restriction adjunction, then preserve colimits. The item is not the unit's key node, so no realization record is changed. The imported item has neither `chapter` nor `unit`, and no corresponding new-chapter/unit JSON records exist in `dag/chapters/` or `dag/units/`; this is pre-existing maintainer metadata, not repaired by this delivery. The blueprint paths still identify its chapter and unit unambiguously.

I added `def-galois-finite-limits-colimits` to statement dependencies to name finite colimits explicitly. Its statement defines a finite colimit as a colimit over a category having finitely many objects and morphisms. This does not add an existence hypothesis. Preservation means that every colimit cocone of such a diagram that exists is carried to a colimit cocone. The hypotheses of `def-sfb-modobj-extension` assume coequalizers and tensor-colimit preservation, not cocompleteness; the proof accordingly does not assert all finite colimits exist.

Searches of the whole DAG by adjunction/colimit terminology and `Adjunction.leftAdjoint_preservesColimits` located the existing general node. Whole-blueprint searches using `tools/blueprint_refs.py search` for `left adjoint`, `leftAdjoint_preservesColimits`, `extension right exact`, `Ext_`, and `finite colimits` found no other equivalent blueprint node. The module-object forgetful-functor and lifted-pullback preservation nodes concern different functors and hypotheses. `blueprint.same_as` is therefore `[]`; as an imported node its `from` correctly stays null. All Mathlib searches recorded in the item were actually run with `msearch.py`, and the exact queries are present in `searches.jsonl`. The first semantic query gave restriction/forgetful-functor results; the second, more general phrasing returned the left-adjoint preservation theorem. LeanSearch also returned the theorem and the finite-colimit restriction instance. The Loogle query ran with zero hits. The source grep found the theorem at line 92; the focused monoidal extension-scalar grep gave zero hits. No new Mathlib leaf was needed.

## Not duplicates

No new nodes. Reused `lem-weil-pbc-left-adjoint-preserves-colimits` instead of introducing another Tag 0038 lemma.

## Review by Q49

I checked this split against delivery-errors B–E with the current blueprint proof, Stacks Tag 0038, and every cited node's statement open. There are no new statement-only nodes, definitions, or relabelled clauses of the item to audit under B/D. The only file changed in the DAG is the sandbox copy of the assigned item; statement text and import metadata are retained. The proof text uses TeX with normal single backslashes after JSON decoding.

For step 1, I read `def-sfb-modobj-extension` and `def-sfb-modobj-extend-restrict-adjunction` in full. The latter explicitly supplies an adjunction Ext_phi ⊣ Res_phi, not merely a construction of the two functors. Its opening says “In the situation of” the former, so it has precisely the item's braided category, coequalizer, tensor-preservation, commutative source monoid, and monoid-morphism hypotheses. In particular I did not require the target monoid to be commutative, the category to be abelian, or the category to be closed. The verbatim adjunction assertion is in citations.json for step 1.

For step 2, I read the complete statement of `lem-weil-pbc-left-adjoint-preserves-colimits`: it accepts functors with any natural adjunction and a small indexing category with an existing colimit, and concludes that the cocone with the original mapped legs is colimiting. Substitute Ext_phi and Res_phi, using step 1. A finite category is small, and the chosen finite diagram has an existing colimit by the premise when testing preservation. Thus every hypothesis of the cited theorem holds, without a hidden assumption that the module categories have all small or all finite colimits. I also read `def-galois-finite-limits-colimits`; its precise finite-index definition is what identifies the conclusion as preservation of finite colimits. Both exact excerpts are in citations.json for step 2. The generic result is a Mathlib leaf and is a tool independently of its filing under the proper-base-change unit; it does not replace the blueprint's extension/restriction route.

I tested the empty-index case: any initial object that exists is carried to an initial object by the same cited theorem, since the empty category is small. For a one-object discrete diagram the result reduces to the identity cocone. For an identity scalar morphism the result agrees with the identity extension functor; no invertibility hypothesis is used in the argument. Categories without coproducts cause no false existence claim: only existing finite colimits are tested. None of these cases exposes a statement dispute. Dependencies are acyclic: the general preservation node depends only on the category-colimit definition, and the finite-colimit definition has no statement dependencies. The missing non-elementary citation was the correction; no non-elementary argument is hidden under an elementary flag.

## Unfinished work

None at this one-level split. The adjunction remains an existing downstream node to be handled by its own worker. No Lean code was written, no compiler/Lake/build tool was run, and no SGA route was used. The required dry run is the final validation; the second reader will deliver.

## Second reading by Q49

- Item statement: checked against the blueprint node and its proof file; the hypotheses are exactly those of `def-sfb-modobj-extension`, and the conclusion is preservation of existing finite colimits.
- Step 1: checked against `def-sfb-modobj-extension` and `def-sfb-modobj-extend-restrict-adjunction`; the latter explicitly states the Ext–Res adjunction in the former's setting, so the left-adjoint inference is valid.
- Step 2: checked against `lem-weil-pbc-left-adjoint-preserves-colimits` and `def-galois-finite-limits-colimits`; the former applies to every small diagram with an existing colimit, and the latter defines finite colimits by finite indexing categories. The finite-category-is-small observation is elementary.
- Existing dependency `def-sfb-modobj-extension`: read its full statement; it introduces the exact braided category, coequalizer, tensor-colimit, monoid, and module-object data used by the item.
- Existing dependency `def-sfb-modobj-extend-restrict-adjunction`: read its full statement; it supplies the required natural adjunction and no stronger hypotheses are used.
- Existing dependency `def-galois-finite-limits-colimits`: read its full statement and Stacks Tag 04AS source; it defines the finite-index interpretation used in step 2.
- Existing Mathlib leaf `lem-weil-pbc-left-adjoint-preserves-colimits`: read its statement and the declaration `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`; it gives exactly preservation of the mapped existing colimit.
- Small cases checked: empty finite indexing category, one-object discrete diagram, identity scalar morphism, zero module, and scalar extension between fields; the argument still applies without extra hypotheses. Categories where only the tested colimits exist cause no existence claim.
- Changes: retained the worker's repaired proof and dependency on the existing finite-colimit definition; no further mathematical or structural change was necessary. No new nodes were introduced, so B1–B7 and duplicate-node checks are vacuous.

Independent second-reader Mathlib search: `msearch.py ... leanfinder "A functor with a right adjoint preserves colimit cocones"` ran successfully and returned eight hits, including `CategoryTheory.Adjunction.leftAdjoint_preservesColimits` and the `IsLeftAdjoint` preservation instance. I checked the former at `Mathlib/CategoryTheory/Adjunction/Limits.lean:92` with the universe and adjunction variables at lines 44–49. This confirms the existing leaf rather than introducing a new one. I also independently searched slopmaster2 by the item id and both expected declaration names: no declaration matched. Upstream-master lines 151–164 have the expected hypotheses and finite-colimit conclusion, but are not finished-proof evidence.
