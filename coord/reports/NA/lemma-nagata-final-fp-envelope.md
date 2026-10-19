## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-final-fp-envelope.json`: split into two steps, with the original statement unchanged; no Mathlib match.
- `citations.json`: full verbatim statements for each of the three citations.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. The draft `lem-nagata-fp-envelope-witness` node was withdrawn; it is not part of this delivery.

## Attachments

None. `AlgebraicGeometry.Scheme.Hom.fpEnvelope_spec` in `WeilConjectures/Compactification/NagataCompactification.lean:97` is not an attachment: its scheme and maps are chosen through `exists_fpEnvelope`, whereas this item concerns the explicit `Env_fp(X/S)` selected from the finite-presentation model system. I read the definitions at lines 80–91 and the theorem at lines 97–101 and preserved the second reader's rejection.

## WANTED

None.

## Findings and corrections

The imported mathematical statement is correct with the context inherited through its definition dependency: the base is qcqs and the original morphism is separated and of finite type. The original proof's reference to the existing proposition is the right route; its missing detail was the identification of the named final envelope with the explicit pair to which that proposition applies. I made that equality explicit and added its definition citations to the proof dependencies. I did not change the statement or the definitions.

An early draft incorrectly tried to use the chosen-witness route from Lean. On checking C4 and E4, I removed that node and argument entirely: the definition node does not identify the explicit model with Lean's arbitrary witness. The final proof uses only the natural-language statements of the existing nodes. The mismatching inherited Lean attachment metadata on the final-envelope definition and envelope proposition is not evidence for those identifications and is not changed here. In particular, the proposition's natural statement concerns the explicit constructed envelope; its recorded Lean existence theorem is not used as a theorem about that specific object.

`blueprint.same_as` records `prop-nagata-finite-type-closed-in-fp`, which has the same assertions after the defining renaming. The imported item's `blueprint.from` remains null because the item is itself a blueprint node; there was no unspecified ancestor place to fill. The item is not the key theorem of its unit, so no unit realization record is changed.

## Review by NA

I read the complete item blueprint at `sk-thm-nagata-compactification/lemma-nagata-final-fp-envelope.md`, the final-envelope definition at order 399, the explicit-pair definition at order 396, and the property proposition at order 397. I also read the chapter record, the Nagata compactification unit record and its stated route through `sk-prop-nagata-sketch-envelope`. Stacks Tag 01ZJ is `limits-proposition-separated-closed-in-finite-presentation` in `literature/stacks-project/limits.tex:2300`; its hypotheses are a separated finite-type morphism and a qcqs base, and its conclusion gives a separated finite-presentation envelope and a closed immersion over that same base. Its short proof passes through finite-presentation approximations and eventual separatedness, exactly the construction exposed by the existing explicit-envelope nodes. No new source lemma is introduced here.

Step 1 cites `def-nagata-final-fp-envelope`, whose displayed equality defines the final pair to be `Env_fp(X/S)`, and `def-nagata-finite-type-closed-in-fp`, which both introduces the qcqs/separated/finite-type hypotheses and identifies `Env_fp` with the specified model-stage pair. The step takes components of those displayed equalities; the structure map is the unchanged structure map of that same selected stage. This is elementary substitution, not any invariance theorem or an isomorphism between arbitrary envelopes. It asserts no closed-immersion or finite-presentation property merely from a definition.

Step 2 cites `prop-nagata-finite-type-closed-in-fp`. I checked its full statement: it explicitly supplies separatedness and finite presentation of the constructed structure morphism, and the closed immersion over S of the constructed map. These are exactly all the non-elementary facts the step needs. The hypotheses are those retained in step 1, with no Noetherian, properness or finite-presentation assumption on the original f added. Replacing each component by its defining equal component proves all three clauses and retains the over-S factorization. This uses the proposition's statement, not its imported proof or Lean attachment. The proof has no dependencies on a future identification, and creates no cycle.

For B1–B10 and C5, the whole-DAG search for `Env_fp` and `finite-presentation envelope`, and `tools/blueprint_refs.py search 'finite-presentation envelope'`, found the two definition nodes and the existing property proposition. The latter already carries the necessary theorem, so no new node restates a clause or duplicates the theorem. I ran and read LeanFinder (two phrasings), LeanSearch, Loogle with fully qualified morphism names, and msearch grep over the actual `AlgebraicGeometry` subdirectory of Mathlib. They found generic separation, finite-type and local finite-presentation results, not a theorem about this explicit chosen stage. The final `mathlib_searches` records these actual queries; there is no Mathlib leaf claim.

For D1–D5 and E1–E7, the proof consists of component equalities and the already-existing property theorem, with every non-elementary assertion cited. Empty source, empty base (hence empty source), identity morphism, and a finite-type morphism that is not finitely presented cause no problem: the construction's inherited hypotheses still apply, and the proof never supposes f itself is finitely presented or identifies an arbitrary witness with the explicit model. There is no disputed statement or source correction. The important repair was discarding the attempted witness identification. All citations in `citations.json` were copied directly from the three node statements. The two envelope-unit citations are recorded in `split_report.tool_uses`; they implement the unit's own stated route, rather than replacing it.

## Unfinished work

None for this one-level split. The second reader should assess the exact explicit-object identification and treat the inherited mismatching Lean annotations as metadata, not as additional mathematics. No Lean source was written or compiled, and no push is authorized in this worker's handoff.

## Second reading by NA

- Item statement: checked against blueprint node `lemma-nagata-final-fp-envelope` (order 400) and Stacks Proposition 01ZJ (`limits.tex:2300`); the closed immersion over (S), separatedness, and finite-presentation clauses and the inherited qcqs/separated finite-type hypotheses agree.
- Step 1: checked both cited statements verbatim; `def-nagata-final-fp-envelope` supplies the equality with `Env_fp(X/S)`, while `def-nagata-finite-type-closed-in-fp` supplies the explicit selected pair and hypotheses. The component substitution is elementary and does not identify an arbitrary existence witness.
- Step 2: checked `prop-nagata-finite-type-closed-in-fp` verbatim; it states all three required properties for exactly the selected pair, so replacing the components from step 1 is valid and preserves the over-(S) condition.
- New nodes: none; no B1–B7 review or duplicate node was needed. Whole-DAG and blueprint searches confirmed that the existing property proposition is the appropriate dependency.
- Edge cases: tested empty source/base, identity morphisms, and finite-type morphisms that are not finitely presented; no step adds a hypothesis or assumes the original morphism is finitely presented.
- Changes: none; the split, citations, and recorded searches passed the second reading. No Lean files or compiler/build tools were used.
