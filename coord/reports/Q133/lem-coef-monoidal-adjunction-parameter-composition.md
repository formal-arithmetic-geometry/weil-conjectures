# Q133: lem-coef-monoidal-adjunction-parameter-composition

## Files written

- `dag/nodes/sec-six-functors/lem-coef-monoidal-adjunction-parameter-composition.json`: statement, now split into three explicit elementary calculations. Mathlib verdict: no exact match under the stated weak tensor-bifunctor hypotheses.
- `citations.json`: verbatim statement excerpts for both proof-step citations.
- `report.md`: this report.
- `searches.jsonl`: actual search-command records, retained with their original results.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The two existing leaves are reused. Each intermediate equality is a substitution into an existing statement or an explicitly written application of a defining law; introducing a node for any of these would manufacture an elementary lemma or restate a clause of the item.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree by the item id, the blueprint tag, tensor-parameter composition, homEquiv/tensor, monoidal adjunction and projection-map names. There is no declaration giving every clause under the item's hypotheses. Read `CategoryTheory/Adjunction/ProjectionMap.lean` and `ProjectionMapAssoc.lean`: these give projection maps and an associator identity, respectively, not this parameter-composition identity. The upstream master is reference material only and was not counted as a finished proof.

## WANTED

None. All sources needed for this formal calculation are present locally.

## Corrections and source audit

The mathematical statement is unchanged. Replaced literal backslash-n sequences by real paragraph breaks. The initial source description associated canonical unit/counit formulas with derived-adjunction Tag 0FND. Read that lemma in `literature/stacks-project/derived.tex`, label `lemma-pre-derived-adjoint-functors-general`, lines 9517–9562: it states a natural derived Hom isomorphism, not the tensor equation here. The precise source for the ordinary adjunction formulas is `literature/stacks-project/categories.tex`, Tag 0037, label `definition-adjoint`, lines 3344–3383. Updated the item's source accordingly while retaining the derived-adjunction context in its description. Since neither Stacks lemma literally states this tensor equation, `proof_origin.by` is `agent`.

Read the chapter and unit records and the current ancestor blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. Its second paragraph assembles mapping-complex comparisons and says the specified units and counits are compatible. This item supplies precisely the tensor-parameter calculation used by step 16 (formerly step 15) of `lem-coef-derived-system-evaluation-calculus`, without replacing the unit's route. It is not the unit's key node; no chapter or unit record was changed. The ancestor proof, rather than a same-named declaration in a sorry-containing upstream source, supplies the context.

## Mathlib and duplicate searches

Before deciding how to split, searched the whole DAG for the item, tensor-parameter composition and Tag 0FND; ran `tools/blueprint_refs.py ancestor lem-coef-monoidal-adjunction-parameter-composition`, and blueprint searches for `tensor parameter`, `monoidal adjunction` and `tensor-parameter`. No blueprint node states this identity in another form, so `blueprint.same_as` remains empty. The monoidal-adjunction blueprint matches are definitions or finite-sheaf monoidality assertions; the sibling `lem-coef-closed-adjunction-naturality` concerns internal-Hom naturality rather than composition and requires additional closed structure.

Ran all four prescribed search kinds with `msearch.py`, including two different LeanFinder phrasings. Read their actual returned hits, and retained the imported search evidence as well. Read Mathlib `CategoryTheory/Adjunction/Basic.lean`, lines 226–246, which gives the two Hom-bijection naturality identities. This ingredient is already covered by `lem-weil-pbc-adjunction-of-natural-bijection`; it does not give the tensor-comparison equation by itself. Read Mathlib `CategoryTheory/Monoidal/Functor.lean`, especially lines 1036–1039 and 1065–1115: the counit tensorator identity assumes monoidal structures and a right-adjoint lax tensorator, while this item has only bifunctors and a natural tensor isomorphism. Other hits require rigid duals or Cartesian closed categories. None is an exact match or one-line specialization with the hypotheses given here. Every new search entry copies the command's tool and query exactly; every service call succeeded. No new node was needed.

## Not duplicates

No new nodes, hence no new/existing pairs requiring justification.

## Review by Q133

I read the item with both its objects and all of its morphisms expanded, and checked delivery-errors B through E against the node and the source. There are no new-node statements or source tags to audit beyond this item. The proof is an agent calculation based on Stacks Tag 0037, not an attribution of the displayed tensor identity to Tag 0FND. No SGA source was used.

For step 1 I opened the full statement of `lem-weil-pbc-adjunction-of-natural-bijection`. It expressly supplies the natural counit and the inverse formula Psi^{-1}(h) = epsilon composed with F(h). Here Phi is Psi^{-1}, as the item itself specifies. With A = T tensor P and B = FS tensor N, q maps S tensor A to S tensor GN, lambda maps S tensor GN to GB, and G(g) maps GB to GN'. Expanding Phi of their composite gives e_{N'} F G(g) F(lambda) F(q). Counit naturality for the actual D-morphism g:B to N' replaces its first two factors by g e_B, giving exactly step 1. Existence and uniqueness of lambda are just applying the specified bijection's inverse, not an additional representability or projection-formula theorem. The verbatim quote in citations.json includes the precise formula and naturality assertion used.

For step 2 the naturality assumption on mu is part of this item's statement; it is not imported from a monoidal coherence theorem. I substituted the morphism pair (1_S,f), checked f:A to GN, and wrote F(q) mu_{S,A} = mu_{S,GN}(1_{FS} tensor F(f)). All terms go from FS tensor FA to F(S tensor GN). Multiplication by the inverse of mu_{S,GN} and insertion of lambda's defining image yields the displayed intermediate equality. I opened `def-nagata-category` and checked that it states the associativity and identity laws used to reassociate and cancel. The inverse-isomorphism equations and F(1)=1 are the defining equations of the structures already specified in the item. The category-law excerpt in citations.json is copied verbatim; no theorem about tensor invertibility or a projection map is inferred from this definition node.

For step 3 the tensor-preservation law is explicitly assumed in the item. Composing the three maps 1 tensor e_N, 1 tensor F(f), and 1 tensor mu_{T,P} gives 1 tensor (e_N F(f) mu_{T,P}), which is 1 tensor f-sharp by definition. I checked the intermediate objects FP/FT are parenthesized as FS tensor (FT tensor FP), followed by FS tensor F(T tensor P), then FS tensor FGN, then FS tensor N; the final map g lands in N'. There is no rebracketing, use of symmetry, tensor-Hom transposition, closedness, dualizability, or inversion of lambda hidden in this step. All three steps are shorter than 2000 characters; none contains an unproved comparison or a hidden standard lemma.

For edge cases I checked F=G=identity with the identity adjunction and mu=identity, where the formula is exactly tensor functoriality; the one-object terminal category, where every map is the identity; and arbitrary choices of parentheses, which remain fixed throughout. I also checked the ordinary Set example F=G=identity, Cartesian tensor and identity mu with arbitrary functions f and g: both sides send (s,(t,p)) to g(s,f(t,p)). Invertibility of lambda is never used. The proof works verbatim for noninvertible counits: only their naturality is used. In fact no additional associativity or unit data can enter any displayed calculation because all objects have the original parentheses.

The split does not offload the conclusion into another node, and every non-definitional fact it uses is either part of its hypotheses or supplied by the cited adjunction leaf. `proof_deps` is exactly the union of step `uses`. Both cited nodes are existing Mathlib leaves, so no off-unit theorem route is introduced. I corrected the source attribution and formatting; there is no statement dispute or mathematical weakening.

## Unfinished work

None in this one-level stage-1 split. No Lean files were written and no compiler, Lake or build command was run.
