## What changed

Replaced the first worker's existence/uniqueness clause restatements with an actual
componentwise reduction. The original module now constructs the local natural
transformation from unique compatible ring maps on individual triples. Its proof
establishes naturality by composing pointed global maps with local morphisms, then
uses component uniqueness. Global uniqueness follows by natural-transformation
extensionality. The original declaration signature and all public imports are unchanged.

Added `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtension`,
which states the remaining single-object extension lemma. Its docstring gives the
model, unit-refinement, localization, arrow-descent and uniqueness argument in words.
The construction chooses only ring maps determined uniquely by that statement.
No arbitrary existence witness supplies data to a definition.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_extension`.

Added one named hole:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension`,
node `new-lem-sbc-etale-triples-prime-localization-component-extension`.

This is a decomposition: one original hole closed, one component hole added,
net zero holes closed in the import closure. The target still depends on `sorryAx`.
The two holes proposed in the first worker's sandbox,
`etaleResidueTriples_primeLocalization_cocone_extension_exists` and
`etaleResidueTriples_primeLocalization_cocone_extension_unique`, and their new
modules and nodes, were removed before delivery; neither was in the repository.
There are no other sorries in the delivered modules and none in definitions.

## No longer needed

Removed the direct proof-only imports
`Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations` and
`Sheaf.Paper.EtaleFiniteDataDescent` from the item's module. Their old direct
proof-dependency nodes are
`lem-weil-pbc-localization-colimit-principal-localizations` and
`lem-weil-pbc-etale-finite-data-descent`; neither is invoked by the assembly proof.
They are dependencies of the component-extension node and remain imported by its
module, so no existing module is pruned from the targets' import closure.
The component module also imports the proved unit-refinement theorem for its plan.
The item's new proof-only import is the component-extension module.

Removed the first worker's proposed existence and uniqueness imports, modules and
nodes. Removed the unchanged relation module from the delivery set.
No existing public import was removed and no existing definition changed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox merely split the target's existence and uniqueness clauses,
leaving both as sorries. Its docstrings referred back to the parent proof and its
new nodes had no real descent steps. The parent node was not updated to match the
combining proof. These faults are repaired by the single-object reduction and the
updated parent route. The earlier claim that the target was proved did not describe
axiomatic closure and understated the two added holes.

Scheme finite-data descent alone produces a scheme model, not immediately a ring
model. The new component docstring explicitly uses the existing affine-limit leaf
`lem-weil-pbc-limit-affine-stage` (Mathlib `Scheme.exists_isAffine_of_isLimit`,
Stacks 01Z6) on the model's upper tail to make it affine. The new node also names
the existing unit-refinement and etale composition facts rather than hiding them.
No assertion that the original statement is false is made.

## New nodes

`new-lem-sbc-etale-triples-prime-localization-component-extension` concerns a
single local triple and a ring map on its ring. It asserts no local natural
transformation and no naturality between local objects. Its proof plan uses the
existing localization colimit, scheme finite-data descent, affine-limit leaf,
etale composition and proved unit-refinement statements. It has the parent's
chapter and unit, its full Lean statement, provenance, searches and docstring proof.

No change record is required: no existing signature or definition changed.
The parent node's `proof`, `proof_deps` and `proof_origin` now describe the formal
componentwise assembly. The former dependencies remain below the component node.

## Second reading by S4

1. Compared every existing delivered module with the repository by `diff`.
   The item's original signature, including R, p, arbitrary field K, χ, q, ψ,
   the algebra instance, hψ, hK, V, η and the full unique-existence conclusion,
   is byte for byte unchanged. Only its proof and private imports change.
   The sandbox copy of the relation definition was identical and was excluded.
   No public definition, interface, or target statement changes. Verdict: pass.

2. Compiled the original proposal and the repaired two-module set using only
   lcompile.py. The repaired proof builds its natural transformation explicitly.
   Under.w supplies commutation with the local base and Over.w supplies
   commutation with the pointing. Associativity turns β followed by f into
   another admissible map, allowing component uniqueness to prove naturality.
   Extensionality and that same uniqueness prove the full conclusion.
   The sole remaining sorry is the named component theorem. No axiom, unsafe,
   opaque, implemented_by, extern or hollow definition occurs. Axiom checks
   are recorded below. Verdict: a valid decomposition, not axiom-free completion.

3. Read Stacks 00CR, 01ZM, 07RP and 04GW online, the actual finite-data-descent
   signature, Mathlib's 01Z6 declaration, and the proved unit-refinement module.
   The new statement retains arbitrary K: neither algebraic closedness nor
   separability is used. Its model exists by finite presentation; its pointing
   restricts from t and does not need to be descended independently. Injectivity
   of residue-field maps supplies the required kernel p. Any β descends after a
   common principal refinement; naturality handles the two refinement arrows.
   Localization extensionality gives uniqueness, including independence of model.
   Checked R a field with p=0: localization changes no ring, and the identity
   pointed map forces each leg. Checked V the zero ring: its ring maps are unique,
   so the conclusion remains valid. Empty t.B cannot admit a pointing to a field;
   this is excluded by the actual triple structure, not by an added hypothesis.
   No local ring, Noetherianity or separable closure assumption was introduced.
   Searches used distinct queries through leanfinder, loogle and grep on Mathlib,
   upstream and Sheaf; leansearch returned service unavailable, recorded without
   a mathematical verdict. Localization lifts/extensionality and finite-data
   descent exist, but no equivalent single-object pointed leg theorem was found.
   Verdict: the new hole is true, needed, and strictly a component of the argument.

4. Read the parent node and dag/units/sk-prop-input-spreading.json. The unit's
   realized arrays do not contain this node and remain unchanged. The same
   localization and descent route is retained beneath the component lemma;
   no unit or chapter step is bypassed. The already proved unit-refinement
   declaration and the affine-limit Mathlib leaf are generic tools. Both old
   proof-dependency imports removed from the assembly module are named above;
   their modules remain needed transitively. Verdict: route kept; no closure pruning.

5. The parent node now cites exactly the component lemma used in Lean, with
   separate assembly, naturality and uniqueness steps. The component node
   states its exact Lean interface and gives the full remaining model argument,
   with the union of its proof-step dependencies in proof_deps. Its new module
   is the node's recorded module. No existing statement fields changed.
   Verdict: DAG and Lean agree at the formal assembly and remaining-plan levels.

Second reading changed: removed the two clause restatements and their nodes,
wrote the explicit componentwise naturality/uniqueness proof, introduced one
single-object extension lemma with a full proof docstring and node, repaired
parent proof metadata, removed unused direct private imports and the identical
relation file, and corrected progress accounting. The remaining component theorem
requires a substantial scheme-to-ring localization/descent formalization and was
not claimed closed by a short proof.

Axiom check: scratch copies ending with #print axioms for both delivered theorems
compiled through lcompile.py. Both the original theorem and the component theorem use exactly propext,
Classical.choice, Quot.sound and sorryAx.
The scratch copies were removed before the delivery checks.

Sources read: [00CR](https://stacks.math.columbia.edu/tag/00CR),
[01ZM](https://stacks.math.columbia.edu/tag/01ZM),
[07RP](https://stacks.math.columbia.edu/tag/07RP), and
[04GW](https://stacks.math.columbia.edu/tag/04GW).
The affine-model step was checked directly against the Mathlib declaration
Scheme.exists_isAffine_of_isLimit and its existing DAG leaf for Tag 01Z6.
