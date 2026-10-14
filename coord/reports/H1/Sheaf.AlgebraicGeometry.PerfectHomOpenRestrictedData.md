## What changed

The disputed pinned conjunction is decomposed in the held module into named stage and apex
proof obligations. The original theorem now combines these two strictly simpler declarations;
all concrete definitions and public signatures remain unchanged.

## Proved and sorry left

`perfect_hom_open_restricted_data_pinned` is proved by pairing
`perfect_hom_open_restricted_stage_pinned` and `perfect_hom_open_restricted_limit_pinned`.
Those two intermediate declarations retain `sorry`; each is one conjunct of the original
statement. `perfect_hom_open_restricted_data` retains its existing reduction through
existence and the pinned theorem.

## No longer needed

No imports, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The pinned statement quantifies over arbitrary independently supplied `hB`, although the
mate construction selects a particular compatible datum. Sign-twisting all equivalences of
an `hB` preserves its structural fields but changes the asserted equations. The two named
intermediate obligations preserve this obstruction while making the planned Lean reduction
explicit and compilable.

## New nodes

- `new-perfect-hom-open-restricted-stage-pinned`
- `new-perfect-hom-open-restricted-limit-pinned`

## Earlier second reading (a previous round; superseded)

Pending independent review.

## Second reading by H1

1. **Visible changes and signatures.** I compared the delivered module with the repository version. The existing declarations, definitions, and target signatures are unchanged byte for byte. The only interface additions are the two explicitly split conjunct theorems, and the report and node files record them.

2. **Compilation and axioms.** I compiled the delivered module with `lcompile.py`; it compiles cleanly. The only remaining `sorry`s are the two named split obligations, each with a public declaration, source docstring, and matching DAG node. No prohibited `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition was introduced. The parent pinned theorem is proved by pairing the two obligations.

3. **Statements and novelty.** The two added statements are exactly the stage and apex conjuncts of the disputed pinned conjunction, hence strictly simpler and needed for the decomposition. They preserve all hypotheses and conclusions of their respective conjuncts. The sign-twist counterexample in the existing disputed comment explains why arbitrary `hB` cannot justify either equation. Searches and repository inspection found no existing declaration duplicating either statement.

4. **Pruning and route.** The proof takes the direct conjunction route and retains the module's existing public imports. No import or proof dependency is unused by the delivered proof, so nothing can be pruned. The unit route remains represented: the parent pinned node is still the source of the two split obligations, and the unit's realized entry is unchanged.

5. **DAG agreement.** Both new node files reproduce the Lean declarations verbatim, identify the disputed parent as their blueprint source, and record their proof dependencies, source, unit, chapter, and delivery metadata. The parent node remains marked disputed and its proof metadata agrees with the decomposition.

I changed only the report by adding this second-reading record; no Lean proof or statement required repair after review.
