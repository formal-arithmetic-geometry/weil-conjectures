## What changed

Reduced `AlgebraicGeometry.Scheme.exists_finite_model_of_completed_model` to two
comparison-isomorphism obligations for an explicit candidate. Its signature and public
imports are unchanged. Added proof imports for the two comparison modules, Noetherian
completion flatness and locality, and the existing source-library finiteness descent theorem.

`PuncturedCompletionMatchingSections` constructs the ring
Γ(Y) ×_{Γ(P)} Γ(E), where P is the supplied overlap, its structural A-algebra map, its
spectrum, and the two canonical comparison maps. All of its definitions have real bodies.
The overlap base equation, the two structural equations and the two comparison base equations
are proved. No witness is chosen from an unproved existence theorem: the overlap isomorphism
is supplied by the original hypothesis, and the ring is an actual categorical pullback.

The main proof takes the two canonical comparison isomorphisms and proves the inverse
completed base equation. It proves finiteness by fpqc descent from the prescribed finite s:
Mathlib gives flatness and locality of the Noetherian completion, hence faithful flatness.
The existing source-library finiteness descent theorem then applies. No separate finiteness
hole is needed. The original unit route stays: the item is below the trait-case purity input,
and its unit has no realized statement or proof-step node being bypassed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_finite_model_of_completed_model`
(node `lem-sbc-punctured-completion-finite-gluing`). This is a decomposition, not a proof
free of sorry dependencies: one upper hole is closed and two strictly partial obligations
are added (net holes closed minus added: -1).

The only sorries delivered are:

- `AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMap_isIso`
  (`lem-sbc-punctured-completion-matching-punctured-iso`): the punctured comparison for the
  fixed matching ring is an isomorphism; it does not assert finiteness or a completed comparison.
- `AlgebraicGeometry.Scheme.CompletionGluingData.completedMap_isIso`
  (`lem-sbc-punctured-completion-matching-completed-iso`): the completed comparison for the
  fixed matching ring is an isomorphism; it does not assert finiteness or a punctured comparison.

Both are single public theorems with proof exactly `by sorry`, complete proof docstrings and
matching DAG nodes. The explicit construction and all five compatibility equations are proved.
The attached source-library fpqc finiteness descent declaration is already proved; no new
module or sorry is introduced for it.

## No longer needed

No existing import or module is removed. The original proof-only dependency on
`def-weil-finite-integral-morphism`, `def-pc-fibre-product` and
`def-weil-pbc-scheme-conventions` is replaced in the parent node
by the explicit construction and comparison nodes; all three definition nodes remain required for
statements and are not globally pruned. No global pruning is claimed.

No new finiteness-of-matching-ring obligation is needed: the completed comparison and
faithfully flat descent prove finiteness. No algebra-structure-transfer obligation is needed:
matching sections already form a commutative ring, with componentwise operations through the
ring pullback. These were steps of the informal plan rather than existing removable modules.

## Where the brief, the DAG or earlier work was wrong

The item's original proof steps cite definitions only; none states the formal-gluing
comparison needed to implement the argument. Thus directly importing those declarations
cannot close the original hole. The two new comparison statements isolate the missing
consequences of Stacks Tags 05ER and 05EU, as used in Tag 0BLH.

The original docstring says that the zero algebra handles empty covers. That does not
preserve an arbitrary prescribed completed model: for a field A, U is empty and E may be
nonempty. The constructed matching ring is Γ(E) in this case, and Artinian local A is already
complete. The new docstring corrects this proof description without changing the statement.

Read the actual source pages for Tags 0BLH, 05ER and 05EU. The last tag explicitly preserves
finiteness and tensor structures. The two new assertions were checked on empty U (Artinian
local bases), an empty finite completed model, and already complete A. They require no
flatness or etaleness of q or s. Flatness of the completion map, however, is used by the
source's module-gluing theorem and by the proved finiteness-descent step.

LeanFinder and Loogle returned no formal-gluing comparison. The grep search and direct
library search found the already proved finiteness fpqc descent theorem. LeanSearch returned
HTTP 500 and is recorded as unavailable, not as evidence that no lemma exists.
The blueprint searches found no matching-sections statement and no exact finiteness descent
statement (the existing finite-flat closed-subscheme descent node is a different assertion).
`blueprint_refs.py ancestor` returned None for this new parent node; its existing
`blueprint.from.node` explicitly identifies `sbc-thm-spreading-finite-etale-galois`, so the
new nodes retain that ancestor and the parent's documented trait/purity sentence.

## New nodes

`def-sbc-punctured-completion-matching-sections` in
`PuncturedCompletionMatchingSections` records the supplied overlap data and the explicit
ring, scheme, morphisms and proved comparison equations.

`lem-sbc-punctured-completion-matching-punctured-iso` in
`PuncturedCompletionMatchingPuncturedIso` is the principal-open localization comparison of
Tag 05ER, assembled over the punctured spectrum.

`lem-sbc-punctured-completion-matching-completed-iso` in
`PuncturedCompletionMatchingCompletedIso` is the completed tensor-product comparison of
Tag 05ER, interpreted through affine schemes.

`lem-sbc-finite-morphism-fpqc-descent` attaches the existing, proved declaration
`AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` (Tag 02LA). It adds neither
a Lean module nor a hole and is used only as a tool in the assembly.

No statement, definition or interface of an existing module is changed; no change record or
forced adaptation is needed. The parent node's proof, proof_deps and proof_origin now follow
the Lean proof.

## Second reading by T3

1. Compared the delivered finite-gluing module with the repository version. The theorem signature and existing interfaces are unchanged; only the proof and proof-only imports changed. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`; they compile without errors. The only remaining `sorry`s are the two named comparison theorems, each with a matching node and source docstring; no definitions contain `sorry` and no forbidden declarations occur. Verdict: pass.
3. Read the explicit matching-sections construction and the two split statements. The ring is constructed as a categorical pullback, and the comparison statements are strictly partial obligations rather than restatements of the parent theorem. Verdict: pass.
4. Checked the proof route and imports. The parent uses both comparison obligations, the completed-map inverse identity, and the existing fpqc finiteness descent theorem; the unit route remains through the stated matching-sections and comparison nodes. Verdict: pass.
5. Checked all five DAG nodes against declarations and proof dependencies. The parent proof dependencies match the imports and the split nodes carry source, proof text, Lean declarations, and blueprint ancestry. Verdict: pass.

Changed only this report section during second reading; no Lean or DAG repairs were needed.
