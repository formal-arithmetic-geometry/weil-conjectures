## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.NoetherianConstantSubsheafGeneric` with a compiling proof of
`AlgebraicGeometry.Scheme.exists_open_generic_generating_subsheaf_of_mono_constant`.
Its signature and existing docstring are unchanged. The only added imports are proof imports:
`WeilConjectures.ConstructibleSheaf.Pullback`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`,
`Sheaf.AlgebraicGeometry.ConstantSubsheafGenericStalkModel`, and
`Sheaf.AlgebraicGeometry.FiniteConstantMapOpenFactorization`.

The proof first obtains a constant model of the generic image, proves its value finitely
generated using `Module.Finite.of_injective` over the Noetherian coefficient ring, and
constructs its finite locally constant sheaf directly from constant-stalk isomorphisms.
It then extends the generic factorization over an open and derives monicity by monicity
of the composite. Finally it transports each generic-stalk model through
`Etale.upperStarCompSheafFiberIso` and cancels the stalk monomorphism to prove that the
constructed stalk map is an isomorphism, hence epi. The small-universe limits, AB5,
and filtered-colimit preservation instances are supplied explicitly by shrinking.

Updated the item's proof, proof_deps, and proof_origin to this Lean argument, and added
one module and node for each of the two remaining geometric steps. No existing statement,
definition, or public import was changed; no change record is needed.

Validation: all three modules compile locally in import order with lcompile.py. The target
module has no sorry. The two intermediate modules have only their named whole-proof sorries.
The dry run also performs the local axiom probes, server compilation of independent modules,
and the stage-3 preflight. Nothing is pushed by this worker.

## Proved and sorry left

Proved (from the two named intermediate statements):
`AlgebraicGeometry.Scheme.exists_open_generic_generating_subsheaf_of_mono_constant`
(node `lem-weil-pbc-noetherian-constant-subsheaf-generic`).

The delivery leaves exactly these two sorries, each the entire proof of its public theorem:

- `AlgebraicGeometry.Scheme.exists_constant_generic_stalk_model_of_mono_constant`, in
  `Sheaf.AlgebraicGeometry.ConstantSubsheafGenericStalkModel`, node
  `lem-weil-pbc-constant-subsheaf-generic-stalk-model`.
- `AlgebraicGeometry.Scheme.exists_open_factorization_of_finite_constant_map`, in
  `Sheaf.AlgebraicGeometry.FiniteConstantMapOpenFactorization`, node
  `lem-weil-pbc-finite-constant-map-open-factorization`.

This is a reduction, not an axiom-free closure of the transitive dependency tree. The first
intermediate gives only a generic model, with no open extension or finiteness; the second
extends a specified finite constant map using a single stalk factorization, with no generic
surjectivity conclusion. The main proof establishes finite generation, finite local
constancy, monicity, and epimorphy itself.

## No longer needed

No original import was removed: `WeilConjectures.ConstructibleSheaf.Defs` is required by
the unchanged signature. No node or module is pruned from the transitive argument.
The old direct dependencies `def-weil-pbc-etale-site` and `lem-weil-pbc-flat-lfp-open`
are now used inside the finite-map descent node rather than in the main combining proof.
The remaining old dependencies continue to occur directly or in the generic-model node.
The finite-underlying-set theorem `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric` was
inspected and is not imported: its assumptions `[Finite Λ]` and `[Finite M]` do not match
finite generation over an arbitrary Noetherian coefficient ring. No unit-realizing node
is bypassed; this split stays below the sk-thm-p1 unit statements and steps.

## Where the brief, the DAG or earlier work was wrong

The statement appears correct. Its originally listed dependencies do not supply the actual
constant-module generator descent or comparison of generic stalk images: these are substantial
parts of the written proof. They have now been isolated as two self-contained statements.
The proof does not need Noetherianity of X, finite cardinality of the coefficient ring, or
finite presentation of the model module. Monicity makes all generator relations vanish on
the same open, even if their set is infinite.

Sources were read directly at https://stacks.math.columbia.edu/tag/09BH, especially proof (3),
and https://stacks.math.columbia.edu/tag/03RZ. The local literature checkout has only indexes.
The natural-language details of compatible geometric stalks and of extension from any point
are agent-written elaborations of the cited source steps, recorded as such in proof_origin.

Edge cases checked mathematically: zero model module (zero map, no generators), F=0,
phi an isomorphism, arbitrarily large coefficient rings and modules, empty X (excluded by
the chosen eta in the item; the open-factorization lemma needs a chosen x), and non-Noetherian
X. The constant model makes no assertion away from eta. The factorization lemma does not
assume G constant, and needs only finite generation of N; the proof descends the images
under the global map alpha and uses monicity to kill every relation.

Searches: LeanFinder returned finite-type SheafOfModules generators and structure-sheaf
spreading-out results, which do not state either intermediate. Loogle returned constant
sheaf APIs only. The source-library finite-value theorem was inspected; its stronger
cardinality assumptions exclude its use. Grep of Mathlib's site APIs found only the
constant-adjunction counit formula. LeanSearch was attempted for each intermediate and
returned Internal Server Error; its unavailability is recorded without a match verdict.
All queries were run through msearch.py and are in searches.jsonl. Blueprint searches for
constant subsheaf, generator lifting, and stalk factorization found no duplicate nodes.

## New nodes

`lem-weil-pbc-constant-subsheaf-generic-stalk-model`:
`lean/Sheaf/AlgebraicGeometry/ConstantSubsheafGenericStalkModel.lean` describes the image
submodule inside a constant sheaf at generic geometric points, without finiteness or an
open extension. Its source is Tag 09BH (3), the generic-submodule paragraph; the docstring
and node give the range construction, monicity, and compatible-separable-closure comparison.

`lem-weil-pbc-finite-constant-map-open-factorization`:
`lean/Sheaf/AlgebraicGeometry/FiniteConstantMapOpenFactorization.lean` states the generator
lifting/descent step independently of irreducibility and constancy of the ambient sheaf.
Its source is Tag 09BH (3), the generator lifting/descent paragraph. Its docstring and node
explain common refinement, open image, descent, all relations, and the adjunction.
There are no change records.

## Second reading by J1

1. **Visible declarations.** Compared the delivered main module with the repository version.
The theorem signature and docstring are byte-for-byte unchanged; only proof-only imports and
the proof body differ. The two added modules introduce the split statements recorded by their
nodes.

2. **Proof and trust basis.** Compiled all three modules with `lcompile.py --all`; compilation
succeeds. The main theorem has no `sorry`. The only remaining sorries are the two named whole
proofs in the split modules. No `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
hollow definition occurs. Scratch-copy `#print axioms` checks for all three declarations show exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`; the latter remains from the open statements.
The proof uses ordinary category-theoretic cancellation and the declared intermediate statements.

3. **Split statements.** Read both new statements and their docstrings against Stacks Tag
09BH, Proposition 59.74.1(3). The generic-stalk-model statement identifies only the generic
image and makes no finiteness or open-extension claim. The finite-constant-map statement
assumes exactly finite generation and one stalk factorization and concludes an open extension.
They are strictly smaller parts of the main argument, handle the zero case, and are not
duplicates of declarations found by the recorded searches. Repeated LeanFinder searches with
image-independence and section-membership wording, and a Mathlib site-API grep with
range/image/lift wording; these returned only structure-sheaf spreading-out, local generator,
and constant-adjunction APIs. Read the upstream and Sheaf constant-subobject statements: their
finite-cardinality hypotheses do not apply here. Neither split step can be closed in a few
minutes with the available APIs.

4. **Pruning and route.** The main proof uses the generic model, finite-generation argument,
open factorization, pullback local constancy, and stalk cancellation. The old direct dependency
`lem-weil-pbc-flat-lfp-open` is used inside the split factorization node; no imported module is
unused in the delivered route, and the unit `sk-thm-p1` remains realized by its existing nodes.

5. **DAG agreement.** The main node's `proof`, `proof_deps`, and `proof_origin` describe the
Lean proof, and each new node has its statement, source, proof steps, searches, Lean record,
and `status: split`. The node statements match the theorem declarations exactly.

I changed only this report: added the second-reading record above. No Lean proof or statement
needed repair.
