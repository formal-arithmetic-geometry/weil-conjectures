## What changed

Replaced the sole sorry in
`Sheaf.Algebra.Homology.HomTensorDifferentialComponent` with a complete Lean assembly.
The original theorem signature and docstring are unchanged. Added two private proof imports:
`Sheaf.Algebra.Homology.HomTensorDifferentialSummand` and
`Sheaf.Algebra.Homology.HomTensorSummandRestriction`.

The assembly restricts both internal Hom maps to each tensor summand, distributes subtraction
and unit scalar multiplication, composes internal Hom maps, and uses Mathlib
`HomologicalComplex.mapBifunctor.d_eq`, `ι_D₁`, and `ι_D₂` to identify the restricted total
differential with its two summand maps. A proved private helper
`CategoryTheory.homObjMap_add_first` lifts the existing general-universe presheaf lemma
`PresheafOfModules.homObjMap_add_left` through `SheafOfModules.hom_ext`. Its proof-only
import is `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit`. Distributing scalar multiplication and applying
`sub_sub` gives the separate three-term summand formula. The restriction criterion then
assembles equality. The raised heartbeat setting is local to this theorem and is needed
for elaborating the dependent total-complex indices; the single-file compile is within 60 s.

The original node's proof and proof dependencies now describe this assembly. All three Lean
modules compile cleanly via lcompile.py. The copied adjunction experiment in the sandbox
scratchpad is not part of the delivery.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_component`
(node `lem-sc-hom-tensor-iterated-differential-component`) by decomposition, not by a
sorry-free proof. Proved the private additivity helper `CategoryTheory.homObjMap_add_first`.
There is no sorry left in the item's module.

Added exactly two named public holes, each in its own module with a source, complete proof
in words and node:

- `CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_summand`
  (`lem-sc-hom-tensor-iterated-differential-summand`): the expansion on a single summand,
  with separate first and signed second tensor differential terms. It does not assemble
  the coproduct or combine the two differential contributions.
- `CategoryTheory.homTensorSummandRestriction_ext`
  (`lem-sc-hom-tensor-summand-restriction-ext`): a generic internal Hom restriction
  criterion for arbitrary source and target modules, with no differential or Hom-complex
  comparison map. Uncurry, preserve the coproduct under tensor, and use coproduct
  extensionality. It is independent of the summand differential calculation.

Net holes: one closed, two added. Existing imported
`CategoryTheory.homTensorDegreewise_exists` remains an upstream hole; this delivery does
not change its module. No data are chosen from a new unproved existence theorem.

Edge cases checked against the mathematical statements: zero source A or target N makes
both maps zero in the restriction criterion; zero K or L gives a zero total tensor;
zero differentials make all differential summand terms vanish. Negative degrees obey
Int.negOnePow_add, with the second summand differential already carrying (-1)^p.
No boundedness, freeness, tensor-section generation, or extra site hypotheses were added.

## No longer needed

No import was removed from the existing module: its only public import is required by its
unchanged signature. No original dependency is globally pruned. The old direct proof dependencies
`def-pur-hom-complex`, `lem-sc-hom-tensor-degreewise`, and
`lem-pc-sheaf-modules-tensor-closed` are no longer direct dependencies of the component
assembly; they remain dependencies of the new summand and restriction nodes. The original component
node now directly uses the two new supporting nodes and
`def-pc-tensor-complex-sheaves`; `def-pur-hom-complex`,
`lem-sc-hom-tensor-degreewise`, and `lem-pc-sheaf-modules-tensor-closed` remain needed below
the new nodes. `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` is not imported by
the assembly: the structural criterion owns the adjunction step instead. Its current
Lean interface fixes both site universes to be equal and cannot be applied directly at
the general universes of this item.

## Where the brief, the DAG or earlier work was wrong

The original node's single proof step combines a sectionwise expansion with a structural
coproduct/internal-Hom extensionality argument. Neither is exposed by its existing Lean
dependencies. The delivery separates these two strictly different tasks and implements
the remaining assembly in Lean. No original statement is disputed or changed.

The local clone has no Stacks source checkout in literature/stacks-project; the exact
sources were read through the official pages https://stacks.math.columbia.edu/tag/0A90,
https://stacks.math.columbia.edu/tag/0A5Y, and https://stacks.math.columbia.edu/tag/03EO.
The searches used leanfinder, loogle and Mathlib/library rg. LeanSearch returned Internal
Server Error; this unavailability is recorded rather than reported as absence of a lemma.
No blueprint duplicate was found for the summand expansion or restriction criterion.
The unit record sk-thm-picard-duality has no realized node carrying a step that this
below-unit decomposition bypasses.

A further attempt generalized the source's private presheaf tensor-Hom construction from
KFlat and its sheafification adjunction to separate site universes. The intermediate
adjunction helpers compiled once, but the full proof attempt exceeded the 60-second
single-file limit due to tensor-localization comparison unfolding. It is not delivered;
the structural lemma is left as its own named, sourced hole. No existing dependency
interface or other group's module was adapted.

## New nodes

`lem-sc-hom-tensor-iterated-differential-summand`, in
`dag/nodes/sec-picard-framework/lem-sc-hom-tensor-iterated-differential-summand.json`,
is stated by `Sheaf.Algebra.Homology.HomTensorDifferentialSummand`.
Its source is Stacks 0A90 with the explicit calculation of 0A5Y. It only expands one
summand and keeps the two tensor differential contributions separate.

`lem-sc-hom-tensor-summand-restriction-ext`, in
`dag/nodes/sec-picard-framework/lem-sc-hom-tensor-summand-restriction-ext.json`,
is stated by `Sheaf.Algebra.Homology.HomTensorSummandRestriction`.
Its source is Stacks 03EK/03EO with the coproduct universal property. Its arbitrary source
and target module formulation is a structural tool, independent of the differential
calculation. No change record is required because no existing signature or visibility
changed.


## Second reading by N3

1. Compared the complete original module with the delivery by diff and checked its
   declaration header byte for byte. PASS: the original theorem signature, notation,
   universes, visibility, and docstring are unchanged. Only proof code, a private helper,
   local elaboration settings, and proof-only imports were added. No definitions changed.
2. Compiled all three modules locally in import order. PASS: no errors or warnings.
   A scratch copy of the component with `#print axioms` reports only `propext`,
   `Classical.choice`, and `Quot.sound` for the private helper; the component and the
   two new theorems additionally report `sorryAx`, exactly as expected from the reported
   open statements. Source inspection found exactly the two named theorem holes and no
   forbidden declarations, hollow definitions, or new choices of arbitrary data.
3. Read both new signatures, proof docstrings, and nodes against Stacks
   [0A90](https://stacks.math.columbia.edu/tag/0A90),
   [0A5Y](https://stacks.math.columbia.edu/tag/0A5Y), and
   [03EO](https://stacks.math.columbia.edu/tag/03EO). PASS: the summand expansion is a
   strictly smaller calculation, and restriction extensionality is an independent
   structural statement. For p=0 the second term has sign (-1)^n, for p=1 its sign is
   reversed, and for p=-1 the same parity identity applies. Zero differentials and zero
   complexes give the asserted zero terms; zero A or N makes the extensionality
   conclusion automatic. No assumption about generation by global pure tensors is used.
   Independent leanfinder and loogle searches for internal Hom of coproducts, and rg
   searches for restriction/extensionality and additivity, found ordinary coproduct
   tools but no existing version of either new statement at these universes. The
   existing general-universe presheaf additivity lemma does replace the helper proof.
4. Read the assembly from its extensionality step down through the differential
   restrictions. PASS: the Mathlib differential identities, functoriality, additivity,
   and subtraction rewrites give a real reduction, rather than a renamed hole.
   Both support imports and the private presheaf additivity import are used. The old
   public import is required by the signature; the new statement imports supply their
   signature's total tensor and internal Hom constructions. The three old dependencies
   no longer used directly are now explicitly listed above. No module is globally
   pruned. The unit record has empty realized statement and step lists, so this
   decomposition bypasses no realized unit step. Neither remaining hole has a short
   proof using the available general-universe interfaces.
5. Compared each node with its Lean signature and the proof's dependencies. PASS:
   existing node changes are limited to proof, proof_deps, and proof_origin; the new
   nodes have complete statements, sources, natural-language proof steps, searches,
   creation/blueprint records, and verbatim Lean signatures. The original proof's
   dependency union agrees with the new assembly, and the support nodes' dependency
   unions agree with their proposed proofs.

Changed the private additivity helper to use
`PresheafOfModules.homObjMap_add_left`, added its proof-only import, updated the
component node's proof text and this report, and made the old direct dependency list
explicit. No holes were closed or added by the second reading. The delivery remains
one original hole closed by decomposition with two holes split off (net -1).
