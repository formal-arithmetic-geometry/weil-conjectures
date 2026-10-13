## What changed

Reduced the sole remaining hole, `RingHom.exists_flat_stage_of_colimit_flat`,
without changing any existing signature or public import. Added two proof imports:
`Sheaf.RingTheory.FlatFinitePresentationModel` and
`Sheaf.RingTheory.FinitePresentationModelStage`, each with one public intermediate
statement in a new module. Added the proof import `Mathlib.RingTheory.FiniteStability`
and a proved private helper `RingHom.finitePresentation_lTensor`.

The helper proves finite presentation of the limit map by tensor cancellation,
finite-presentation base change, and transport across an algebra equivalence.
The main proof obtains a flat integer model, descends its comparison isomorphism,
base-changes the model's flatness to the stage, and composes with that isomorphism.
The persistence and final eventual-flatness proofs are unchanged.

The two obligations are separate parts of the existing Stacks argument: the first
has no diagram or stage conclusion; the second has no flatness hypothesis or
flatness conclusion. Their combination is a complete checked Lean proof.

## Proved and sorry left

Closed one existing hole by decomposition:
`RingHom.exists_flat_stage_of_colimit_flat`
(`lem-weil-pbc-colimit-flat-ring-map-stage`). No direct `sorry` remains in the item.
`RingHom.eventually_flat_of_flat_stage` and
`RingHom.exists_eventually_flat_of_colimit_flat` retain their existing proofs.
The new private helper `RingHom.finitePresentation_lTensor` is proved.

Added exactly two holes, each the entire proof of one public theorem in its own
module, with its source, full proof in words, and DAG node:

- `RingHom.exists_flat_finitePresentation_model`
  (`lem-weil-pbc-flat-finite-presentation-model`).
- `RingHom.exists_finitePresentation_model_stage`
  (`lem-weil-pbc-finite-presentation-model-stage`).

This is a decomposition, not a proof without dependencies on sorry. The net hole
change is one closed minus two added, or -1. No definition contains a hole or
chooses an arbitrary witness from an unproved existence theorem. The existential
model witnesses are unpacked only inside the proof of the original proposition.

## No longer needed

No import was removed, and no module is claimed pruned. The following old direct
`proof_deps` are no longer used directly by the stage-existence proof; the two new
nodes retain the mathematical dependencies for their arguments, while flatness
and finite-presentation definitions also remain statement dependencies:

- `def-weil-affine-spectrum`.
- `def-weil-pbc-category-colimit`.
- `def-weil-pbc-finite-type-algebra`.
- `def-weil-pbc-finitely-presented-algebra`.
- `def-weil-pbc-flat-ring-map`.
- `def-weil-pbc-localization-at-prime`.
- `def-weil-pbc-noetherian-ring`.
- `lem-weil-pbc-colimit-category-fp-algebras`.
- `lem-weil-pbc-colimit-eventually-flat`.
- `lem-weil-pbc-directed-colimit-base-change-elementwise`.
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`.
- `lem-weil-pbc-filtered-colimit-algebras-underlying-module`.
- `lem-weil-pbc-filtered-colimit-localization-at-prime`.
- `lem-weil-pbc-filtered-colimit-modules-criterion`.
- `lem-weil-pbc-filtered-colimit-rings-zero`.
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`.
- `lem-weil-pbc-finite-type-algebra-noetherian`.
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`.
- `lem-weil-pbc-flat-local-ring-maps`.
- `lem-weil-pbc-flat-map-local-criterion`.
- `lem-weil-pbc-flat-over-localization`.
- `lem-weil-pbc-limit-finite-presentation`.
- `lem-weil-pbc-localization-flat`.
- `lem-weil-pbc-localization-noetherian`.
- `lem-weil-pbc-localization-tensor-over-base`.
- `lem-weil-pbc-localization-tensor-product`.
- `lem-weil-pbc-openness-of-flatness`.
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`.

The unit's `realized` nodes and route are unchanged. This is dependency regrouping,
not a claim that these modules leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt only reformatted an already proved declaration and left the
module's sole hole untouched. This delivery reduces that hole instead.

No error was found in the original stage-existence statement or its nine-step
argument. Neither existing dependency alone states the missing conclusion:
`Algebra.exists_limit_finite_presentation` supplies a non-flat approximation;
`RingTheory.exists_flat_stage` requires Noetherian local stages;
`RingHom.exists_map_of_finitePresentation_colimit` supplies factorization and
eventual equality, rather than the comparison construction for two base-changed
ring systems. Their signatures were read before stating the grouped obligations.

LeanSearch returned an Internal Server Error for both new-node searches. This is
recorded as unavailable, not as evidence of absence. LeanFinder and source grep
found component lemmas but no exact theorem. The local literature checkout is
absent on this machine; the primary Stacks pages for Tags 02JO and 05N9 were read
online to check the reduction against their statement and proof.

Edge cases checked mathematically: the original index type is nonempty because
of i₀; zero rings and empty spectra are allowed, with the unit relation descended
also when 1=0; presentations may have zero variables or relations. The second
intermediate does not assume P embeds into the limit ring: finite-presentation
factorization works for arbitrary structure maps. Its P and Q universe is
independent of the original rings. The first model is stated at the maximum of
the two ring universes, permitting lifted finite presentations.

## New nodes

`lem-weil-pbc-flat-finite-presentation-model` groups steps 2–7 of the original
stage-existence argument, with Stacks Tag 02JO (1), specialized to the top ring
as its module. Its statement produces a flat finitely presented integer model
and a compatible ring isomorphism after base change.

`lem-weil-pbc-finite-presentation-model-stage` groups step 1's system setup and
step 8's comparison descent, with Stacks Tag 02JO (3), Tags 00QO and 05N9 (2),(3).
Its statement descends an arbitrary finitely presented comparison model to a
stage, without requiring flatness. Both nodes inherit chapter
`sec-proper-base-change` and unit `sk-thm-p1`. No change record is needed because
no existing interface changed.

## Second reading by N3

1. **Existing interfaces: PASS.** Diffed the item against the read-only repository.
   All three existing declaration signatures are byte-for-byte unchanged; their
   parsed statements also agree. The persistence and eventual-flatness proofs are
   unchanged. Only proof imports, a private proved helper, and the stage-existence
   proof were added. The two sibling modules are new, with no existing declarations
   replaced. No statement or definition change record is required.
2. **Proof and axioms: PASS as a decomposition.** Compiled all three files locally
   in import order with `lcompile.py`, without warnings or errors. Scratch copies
   with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` for the stage and final theorem and the two reported intermediate
   holes; persistence has only the three permitted axioms. The delivery tool's
   probe also checks the private helper. There are exactly two direct holes, both
   entire public named theorems with docstrings and nodes. No data definition,
   forbidden declaration, or arbitrary witness extracted into data was added.
3. **Intermediate statements: PASS.** Read both complete statements, docstrings,
   and nodes against [Stacks 02JO](https://stacks.math.columbia.edu/tag/02JO) and
   [05N9](https://stacks.math.columbia.edu/tag/05N9). The flat model argument chooses
   the ring approximation with top module Q itself; it does not infer Q is flat
   from flatness of an arbitrary module model returned by 02JO(1). Comparison
   descent uses finite presentation of P over Z and Q over P, plus that of the
   stage map, and requires no flatness. Checked singleton diagrams, zero target
   rings, zero source rings when the structure map exists, empty presentations,
   noninjective P structure maps, nonantisymmetric directed preorders, and differing
   universes. In the empty-spectrum case the unit relation still descends. These
   are strictly separate parts of the argument, not renamed copies of the item.
   Independent LeanFinder queries, Loogle `RingHom.Flat, RingHom.FinitePresentation`,
   and source searches found component operations but no replacement theorem.
   Read the existing LimitFinitePresentation and ColimitCategoryFpAlgebras signatures;
   neither closes either new obligation in a few minutes.
4. **Route and pruning: PASS after report repair.** Read `dag/units/sk-thm-p1.json`;
   the item is below its realized nodes and no unit step is bypassed. All imports
   added to the original item are proof-only. The sibling imports supply their
   statement vocabulary. The finite-presentation helper is the same tensor
   cancellation/base-change argument as Mathlib's flat `lTensor` theorem and
   introduces no hole. No shorter applicable complete proof was found. Corrected
   `No longer needed` to enumerate every removed old direct dependency and to
   distinguish regrouping from pruning.
5. **DAG agreement: PASS after metadata repair.** Existing stage-node proof steps
   follow the helper, the two obligations, and flat base change plus composition.
   Each delivered node's `proof_deps` equals the union of its step `uses`; the
   reachable dependency graph is acyclic. New nodes have their source, complete
   proof plan, search records, creation/blueprint/unit data, and matching Lean
   records. Added the finite-type definition dependency explicitly to the first
   model step and recorded the independent semantic searches.

Second reading changed only the dependency/search metadata and report. No Lean
proof or statement needed repair. One old hole is closed by decomposition into
two new holes (net -1); neither new hole is claimed proved.
