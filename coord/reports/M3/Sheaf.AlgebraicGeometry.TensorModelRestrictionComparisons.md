## What changed

In `Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons`, replaced the proof of
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons` without changing
its signature. The proof evaluates the K-flat natural comparison on the singleton
family P and the identity functor on all complexes, then inverts it, applies eA,
and uses derived tensor symmetry. It proves naturality of this model comparison.
It constructs d by composing R(c) with the derived tensor restriction comparison,
and proves both requested equations by functoriality and the coherence equations.

Added and proved `Sheaf.AlgebraicGeometry.KFlatTensorModelNaturalComparison`,
a fixed-first-model specialization of the existing bifunctor comparison, and the
private, fully proved `transport_model_comparisons` theorem in the original module.
The latter proves the model naturality and restriction equations in arbitrary
monoidal categories, avoiding repeated unfolding of the sheaf constructions.

Added `Sheaf.AlgebraicGeometry.DerivedRestrictionTensorHomCoherence` for the
remaining simultaneous tensor/Hom restriction and evaluation compatibility.
Updated the original node's proof, proof dependencies and proof origin.
No definition, existing statement, visibility or target signature changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons`
(node `lem-sc-tensor-model-restriction-comparisons`). Its written proof constructs
and proves naturality of c, then composes comparisons to prove the required
naturality and evaluation equations. The item's module has no remaining sorry.

Also proved `AlgebraicGeometry.Scheme.kFlat_tensorModel_naturalComparison`
(node `lem-sc-kflat-tensor-model-natural-comparison`) from the already proved
`AlgebraicGeometry.kFlat_derivedTensor_comparison_natIso`. It has no sorry.
The private `transport_model_comparisons` is fully proved as well.

Validation: `lcompile.py --all` compiled the three modules. The heartbeat-comment
warning in the fixed-model module was corrected before the delivery dry run.
The public signature of the original theorem was compared verbatim with the
repository version and is unchanged.

Added one hole:
`AlgebraicGeometry.Scheme.exists_derivedRestriction_tensorHom_coherence`
(node `lem-sc-derived-restriction-tensor-hom-coherence`). This isolates the
comparison theory for derived objects; it contains no complex P, eA, tensor model B,
or tensor-model naturality conclusion. It cannot alone furnish the original
statement's c or d: the model computation and the composition equations are proved
in the original module. This is a decomposition, not a complete sorry-free proof;
one hole closed and one added, net zero before any closure-based pruning.

Edge cases checked mathematically: J is arbitrary, including acyclic non-K-flat
complexes; no K-flatness of J is used. Zero complexes and the empty open are
included because every operation is functorial and the coherence assertion has
no nonzero, stalk-existence, or boundedness hypothesis. The open U = top case is
the same comparison through the canonical over equivalence.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`
- `Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`
- `Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`
- `Sheaf.Algebra.Homology.HomComplexRestrictOpen`
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`

These modules and their nodes remain needed in the new coherence helper's proof
plan, and are imported there. `KFlatDerivedTensorComparison` is also used by the
proved fixed-model specialization. No module or node is claimed pruned from the
target closure. Kept the original statement imports; the original module's proof
imports are now `KFlatTensorModelNaturalComparison`, `DerivedTensorSymmetry`, and
`DerivedRestrictionTensorHomCoherence`.


The old direct proof dependencies no longer used directly by the original proof are
`lem-pc-kflat-derived-tensor-comparison`,
`lem-pc-open-restriction-kflat-model`, `lem-pc-open-restriction-total-tensor`,
`lem-sc-derived-internal-hom-restrict-open`,
`lem-sc-derived-k-injective-restrict-open`, `lem-sc-hom-complex-restrict-open`,
and `lem-pur-hom-kflat-into-kinjective`. They remain dependencies of the new
helpers. `def-pc-canonical-derived-tensor-hom-bijection` also leaves the original
node's direct proof-dependency list, but remains a statement dependency and the
canonical equivalence is used explicitly. No closure pruning is asserted.

## Where the brief, the DAG or earlier work was wrong

The existing restriction lemmas give separate object isomorphisms. Their
signatures do not specify naturality of the derived tensor restriction comparison
or the simultaneous evaluation equation; independent choices of isomorphisms
cannot justify that equation. The new helper records exactly this missing
coherence step. It preserves the mathematical argument of the node and does not
bypass a blueprint unit's statement or realized proof step.

The literature source files named by the node are absent in this checkout.
Read the primary source pages directly: [08DJ](https://stacks.math.columbia.edu/tag/08DJ)
uses an arbitrary first complex, a K-flat second complex and a K-injective target;
[08DL](https://stacks.math.columbia.edu/tag/08DL) says that the constructed internal
Hom commutes with restriction. [079U](https://stacks.math.columbia.edu/tag/079U)
gives the bifunctorial derived-pullback/tensor comparison; for an open immersion,
exact ordinary restriction computes derived pullback. Evaluation compatibility is the componentwise
construction combining these facts, as detailed in the new theorem's docstring.
LeanSearch returned an Internal Server Error; LeanFinder, Loogle and local searches
ran and found no declaration supplying this simultaneous compatibility.

## New nodes

`lem-sc-derived-restriction-tensor-hom-coherence`, in
`dag/nodes/sec-picard-framework/lem-sc-derived-restriction-tensor-hom-coherence.json`,
states natural tensor restriction comparisons and compatible internal-Hom
comparisons on all derived objects. Its source is Stacks Tags 079U, 08DL and
08DJ. The node and docstring give the K-flat/K-injective representative argument,
termwise evaluation calculation, and passage through homotopy and localization.
It records LeanFinder, Loogle, grep and the unavailable LeanSearch request.
Its module contains one public named theorem with whole proof `:= by sorry`.
No change record is needed: no existing interface changes.

`lem-sc-kflat-tensor-model-natural-comparison`, in
`dag/nodes/sec-picard-framework/lem-sc-kflat-tensor-model-natural-comparison.json`,
is the fixed-first-model specialization of the existing natural bifunctor
comparison. Its module `KFlatTensorModelNaturalComparison` proves it by singleton
evaluation; it leaves no sorry and adds no unproved mathematical dependency.
The source is [06YH](https://stacks.math.columbia.edu/tag/06YH), together with the
existing project comparison theorem. Searches found generic lax monoidal
naturality and the project's stronger bifunctor theorem; the node records these
results and the unavailable LeanSearch request.

## Second reading by M3

1. Compared the delivered original module with the repository version and checked
   the public theorem signature byte for byte with a script: identical. The only
   changes are proof imports and proofs, including a private proved transport
   lemma. There are no changed existing definitions, statements or visibility,
   forced adaptations, or target changes. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`: no errors or warnings.
   Inspected every proof and the forbidden-declaration scan: no axiom, unsafe,
   opaque, implementation override, or sorry in a definition. The only new sorry
   is the reported named coherence theorem, whose whole proof is `by sorry`.
   The model specialization is singleton evaluation of the existing natural
   bifunctor comparison. The transport lemma proves inverse-comparison
   naturality, tensor transport through eA, symmetry, and both restriction
   equations by functoriality. Verdict: pass, subject to the declared coherence
   hole; this remains a decomposition, not a sorry-free proof.
3. Read the new statements, their docstrings, nodes, and the existing comparison
   and canonical tensor-Hom definitions. Tested the empty open, zero complexes,
   U = top, and arbitrary non-K-flat second complexes mathematically: no extra
   assumption is required. The coherence statement concerns only derived
   objects; the model construction and its naturality are independently proved.
   It does not restate the item. Searched again using LeanFinder for strong
   monoidal functors preserving internal Hom/evaluation, Loogle for
   `CategoryTheory.MonoidalClosed`, grep for `expComparison_ev` and derived
   restriction comparisons, and local source searches. The generic exponential
   comparison is for cartesian monoidal categories, while the existing project
   restriction results give separate object isomorphisms. None closes this
   simultaneous derived evaluation assertion. Verified Stacks 08DJ, 08DL,
   06YH, 06YG and 079U directly. Verdict: true sourced missing step, not a
   duplicate; no quick closure found.
4. Checked the route from the original theorem downward. The proved fixed-model
   specialization uses the existing K-flat comparison, and the abstract
   transport proves the model part without redoing sheaf representative
   calculations. All new proof-only imports are plain imports; public imports
   expose symbols required in signatures. The coherence imports are the modules
   of its still-open proof plan. The unit record has empty realized statement
   and step lists; none of its realized nodes is bypassed or removed. Completed
   the report's exact old dependency accounting. No module is pruned from the
   targets' import closure. Verdict: pass.
5. Checked all three node Lean statements verbatim against their declarations,
   their proof-dependency unions, origins, source references, creation records,
   blueprint paths, unit, and chapter. The original node records the two proved
   categorical reductions and the one remaining coherence dependency. Both new
   nodes have the required fields. Verdict: pass.

Axiom verification: scratch copies with `#print axioms` compiled successfully.
`kFlat_tensorModel_naturalComparison` uses only `propext`, `Classical.choice`,
and `Quot.sound`. The original theorem and the coherence helper additionally
use `sorryAx`, as expected from the one declared open coherence theorem. No
other axiom was reported. Scratch probes were removed before delivery.

Second-reading changes: corrected the new coherence module and node's tensor
source from the indirect quasi-coherence Tag 08DX to the bifunctorial
pullback/tensor Tag 079U; clarified exact restriction and descent through common
K-flat resolutions in its proof description; completed the report's removed-node
accounting. No Lean proof or statement required repair.
