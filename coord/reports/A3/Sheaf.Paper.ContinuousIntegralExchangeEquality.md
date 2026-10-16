## What changed

Reduced the exchange equality to two explicit one-sided adjunct normal-form calculations. The item uses injectivity of the actual bounded f′ adjunction and transitivity. Each new theorem identifies just one adjunct with an explicit pull-square-comparison/counit composite; neither restates the original equality. Existing signatures and all definitions are unchanged. The attempted generic construction refactor and its experimental modules are omitted.

## Proved and sorry left

Closed AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_equality from the two named statements. Added two holes: AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_source_adjunct (lem-weil-pbc-continuous-integral-exchange-source-adjunct) and AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_target_adjunct (lem-weil-pbc-continuous-integral-exchange-target-adjunct). This is a decomposition, one hole closed and two added, not a net proof. Source adjunct still needs the concrete exchange-counit and mate-counit substitutions. Target adjunct additionally needs derived pull-composition coherence. Complete proofs in words accompany both. The session developed and compiled the abstract mate/counit algebra and normalization probes, but concrete combined kernel checking exceeded the limit; no limit was raised.

## No longer needed

No existing modules or nodes are pruned. Removed the unused original private abstract helpers from the item: the final combination needs only the two new normal-form statements. The original public comparisons import stays. Experimental cube, composition, diagnostics and the source construction refactor are not delivered.

## Where the brief, the DAG or earlier work was wrong

The DAG grouped pull coherence and concrete adjunct normalization into one step. The final two statements give distinct side calculations with a common explicit normal form. Identity and zero-object cases reduce to the expected adjunction/comparison identities. No properness or Cartesianity is needed. The unit route and target statements are unchanged.

## New nodes

lem-weil-pbc-continuous-integral-exchange-source-adjunct calculates the source adjunct using naturality and the mate/counit relation. lem-weil-pbc-continuous-integral-exchange-target-adjunct calculates the target adjunct using these relations and derived pull-composition coherence. Both are strictly one-sided pieces, in separate modules with complete proof descriptions, sources and search records. Change record for the static private-helper/command-layout check: coord/changes/continuous-integral-exchange-proof-layout.md. No definition or public statement changes.

## Second reading by A3

1. **Statements and signatures.** Compared the delivered item with the repository version. The target theorem signature is byte-for-byte unchanged. The two added adjunct statements are one-sided equalities with the same explicit normal form; neither restates the target equality or changes an existing declaration.

2. **Compilation and proof status.** Compiled all three delivered modules with `lcompile.py --all`; each compiles cleanly. The target theorem is proved by bounded-adjunction injectivity and transitivity. The two named adjunct declarations are the only remaining `sorry`s, and each has a docstring proof plan and a matching DAG node. No definitions contain `sorry`, and no forbidden declarations were added.

3. **New statements and dependencies.** Checked both split statements against the source-side and target-side calculations in the item and searched the library and recorded search results for existing declarations. They are true one-sided reductions, strictly simpler than the target, and use only the stated comparison and category-theory dependencies.

4. **Pruning and imports.** The item imports the two adjunct modules as proof-only imports. The original private abstract helpers were removed because the final proof does not use them; this is recorded in `coord/changes/continuous-integral-exchange-proof-layout.md`. No public dependency or required node is pruned, and the unit route remains the two adjunct calculations followed by injectivity.

5. **DAG agreement and unit route.** Checked the item and both new node records: declarations, statements, proof steps, proof dependencies, origins, chapter, and unit agree with the delivered Lean. The `sk-thm-properbasechange` route is preserved. 

The second reading found no mathematical or interface defect. The changes made were the required report section only; the delivered Lean and node contents were left unchanged.
