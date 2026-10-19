## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proetale-supported-reconstruction.json`: statement node, now split into six steps; no Mathlib match for the complete statement.
- `citations.json`: verbatim statement evidence for every proof-step citation.
- `searches.jsonl`: six new searches run through the required command; the item's inherited search records are retained.
- `report.md`: this report.

No new nodes or new Mathlib leaves. The existing Mathlib leaf `lem-weil-pbc-adjunction-of-natural-bijection` supplies the formal adjunction identities. No unit file is changed: this item is a tool below the unit, not its key statement.

## Attachments

None. Searched the source under WeilConjectures for the exact blueprint id and for reconstruction/support, open/closed and adjunction terminology. No declaration proves the complete statement. The source's Zariski structure-sheaf module results and finite-coefficient open/closed machinery do not establish this arbitrary ring-sheaf statement, its two support conditions, and the prescribed normalization. The exact master checkout was searched read-only and was not treated as proof evidence.

## Wanted sources

None. Read `literature/stacks-project/proetale.tex`, particularly Tags 09AH (`lemma-ses-associated-to-open`) and 09BN (`lemma-open-immersion`), together with `categories.tex`, Tag 0037 (`definition-adjoint`) and its following transpose formulas, and `lemma-unit-counit-relations`.

## Faults repaired

The item was an unsplit statement extracted by Q28 from the locally closed extension comparison; it had no proof. Its statement is true and is preserved verbatim. The proof now exposes both support arguments and all three formal clauses: the transpose is invertible, has the prescribed restriction, and is the unique morphism with that restriction. It also computes both naturality squares rather than claiming compatibility without an equation.

No change to the blueprint route is needed. Read the chapter and unit records and the current main-20261015 `det-prop-scalar-six-pullback.proof.md`, proof (2), especially its composition compatibility sentence. This proof supplies the support reconstruction needed in Step 7 of `lem-sfb-locally-closed-extension-coherence`, exactly the item's existing from/place/via ancestry.

## Unfinished work

None at stage 1. No Lean files were written, no compiler or Lake commands were run, and no shared project or launcher files were modified.

## Mathlib and duplicate searches

Read all six search outputs: LeanFinder in two phrasings, Loogle for `"SheafOfModules", "counit"`, LeanSearch, whole-Mathlib grep, and a more targeted grep in CategoryTheory. All services returned results successfully. The natural-language hits suggest sheafification, the Zariski module restriction adjunction, generic module pushforward adjunctions, abstract Serre localization and derived-category boundedness. Inspected Mathlib/AlgebraicGeometry/Modules/Sheaf.lean (restriction adjunction and counit, lines 412–448), Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean (counit formula at line 303), Presheaf/Sheafification.lean (Hom formulas, lines 98–150), and CategoryTheory/Abelian/SerreClass/Bousfield.lean (line 50). None supplies the two pro-etale support reconstructions; the generic adjunction formulas are already represented by the existing Mathlib leaf, which is reused. These are no-match verdicts for the complete item, not claims that those generic ingredients are missing.

Searched the whole DAG for Tag 09AH, localization exact sequences, support and reconstruction. Searched the imported blueprint with blueprint_refs.py for 09AH, support reconstruction, two successive and prescribed restriction, and checked its ancestor command. The broader existing ringed open–closed theorem is the precise tool for this proof, not a duplicate to create. The etale-only `lem-weil-pbc-open-closed-short-exact` is unsuitable here. `det-sf-open-closed-sequence-ring-sheaf` assumes qcqs schemes; this item does not, so it is not used. The supported-sections adjunction node addresses a different right adjoint and does not supply this statement.

## Tool use

`lem-weil-pbc-proetale-ringed-open-closed` is declared in split_report.tool_uses. This generic localization-sequence theorem is used as a black box twice on arbitrary ring sheaves, and no node of the coefficient-comparison unit provides its result. This retains the unit's open/closed comparison route. The other statement citation is already a Mathlib leaf and therefore a permitted generic tool.

## Review by Q56

I read the source places above against the item and the four cited node statements. Tag 09AH explicitly requires a quasi-compact complementary open immersion. Both applications have exactly this hypothesis: (i,k) on X and (e,u) on Z. The second ring is i^{-1}R; its module N=i^{-1}A restricts to zero on B by the item's second hypothesis. Nothing uses finite type, Noetherianity, qcqs, constant coefficients, a finite coefficient ring, or a derived coefficient category. Tag 09AH itself states the abelian-sheaf result; the already existing `lem-weil-pbc-proetale-ringed-open-closed` explicitly states the needed arbitrary-ring-sheaf module version. I use that node's statement, not an argument hidden in its proof.

Step 1 cites that ringed theorem for the exact sequence with its unit, the exact-sequence definition for the short exact meaning, and the module-category definition for its abelian structure. Exactness of extension by zero makes its value on the zero sheaf zero. The resulting unit is a cokernel of 0 -> A, and comparison with the identity gives its inverse. Step 2 cites the same ringed theorem with the other pair and the exact-sequence definition. Its exact closed direct image sends the zero sheaf to zero. The counit is a kernel of N -> 0, hence invertible; applying a functor to sigma and its inverse and composing establishes lambda's invertibility. These two kernel/cokernel deductions are routine consequences of the displayed sequences, not separate missing geometric facts.

Steps 3–6 each cite `lem-weil-pbc-adjunction-of-natural-bijection`. I opened its statement: it gives both transpose formulas, naturality, and triangle identities, exactly the data used. In Step 3 the counit calculation returns lambda^{-1}, so the isomorphism is the transpose for the specified adjunction. In Step 4 the right triangle identity is applied at N and unit naturality at sigma^{-1}; multiplication by the inverse of H(lambda) gives the required restriction. No unproved identification of a closed or open adjunction map is used. In Step 5 the candidate h is arbitrary. Its inverse transpose q satisfies Hq=eta_M sigma, and counit naturality followed by the left triangle identity gives q lambda=id. Cancelling lambda and using the Hom bijection proves uniqueness. In Step 6 the hypothesis b sigma=sigma' HFa is first rearranged, then the open counit and closed unit naturality equations give the two squares displayed in the node. These four steps are marked elementary because each consists solely of the written substitutions, the cited adjunction identities, and cancellation of the already constructed inverses.

I checked all domains and codomains: lambda:LM -> FA, theta:A -> GLM, its inverse transpose FA -> LM, and the restriction HFA -> HLM. All compositions read right to left. The normalization does not need an extra theorem asserting invertibility of the open unit. This avoids both a hidden fully-faithfulness argument and dependence on an unspecified natural isomorphism.

For small cases: if S is empty, the second localization forces N=0 and the first forces A=0, so all assertions hold, including uniqueness. For i=u=id, lambda=sigma^{-1} and theta=sigma under the canonical identity adjunctions. For u=id with a proper closed support, the result reduces to the supported closed unit followed by the transported sigma. For i=id it reduces to the open counit reconstruction. For the zero ring every module is zero and the equations still hold. None requires sigma to exist when its source and target differ: it remains the stated hypothesis.

Checked delivery-errors B–E: no statement-only node is burdened with a hidden proof, no new node is created, the statement introduces its objects and keeps its definition dependencies, exact-sequence citations concern the actual pro-etale ring-sheaf category, and no clause is displaced into a renamed child. Every non-elementary input is cited, every cited statement says what is taken from it, and all quotations were checked verbatim. Proof dependencies are exactly the union of uses. No step exceeds 2,000 characters (all are under 750), and none hides a standard comparison lemma. The statement, blueprint ancestry and creation metadata are retained. No SGA source is used.
