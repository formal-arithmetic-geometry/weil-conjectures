## What changed

Decomposed `AlgebraicGeometry.exists_radicial_generic_reduced_preparation` into the
radicial construction and a proved, general fibre comparison. The existing target
signature and docstring are unchanged. The construction now supplies an explicit
universal homeomorphism `h : Y → pullback f (q ≫ U.ι)` with `h ≫ projection = g`.
The target obtains that witness, applies comparison, rewrites this factorization,
and assembles the original conclusion. No data definition chooses an arbitrary
witness of an unproved existence theorem.

The two new modules are `Sheaf.AlgebraicGeometry.RadicialPreparationConstruction`
and `Sheaf.AlgebraicGeometry.RadicialPreparationFibreComparison`. The latter proves
comparison using private, proved helpers for universal-homeomorphism invariance and
field-extension invariance. Its only project proof import is the already proved
`Sheaf.FieldTheory.CommonExtensionFields`; the construction keeps the old generic
flat finite presentation dependency as a plain proof import. All public imports
are needed by signatures. No existing interface changes and no change records.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.exists_radicial_generic_reduced_preparation`
(node `lem-sbc-radicial-generic-reduced-preparation`). Its proof still depends on the
construction hole below, so this is a decomposition, not a completed mathematical proof.

New hole added: `AlgebraicGeometry.exists_radicial_preparation_construction`
(node `lem-sbc-radicial-preparation-construction`). This is the sole `sorry` in the
delivery, in a named public theorem with a full natural-language construction proof.

Fully proved new declaration:
`AlgebraicGeometry.exists_radicial_preparation_fibre_comparison`
(node `lem-sbc-radicial-preparation-fibre-comparison`). Both private helpers are proved.
Its `#print axioms` contains exactly `propext`, `Classical.choice`, and `Quot.sound`.
The original theorem and construction also contain `sorryAx`, exactly for the open
construction. A scratch copy printed all three axiom lists and was removed afterward.

Accounting: one original hole closed, one new hole added, net zero. The first
worker's two-hole decomposition is repaired and reduced to one true construction
hole; its false comparison hole is replaced by a complete proof, not retained.

## No longer needed

Removed the direct plain import `Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation`
from the target module. The old proof dependency
`lem-sbc-generic-flat-finite-presentation` is no longer directly used by the target,
but remains a construction proof dependency, and its module is imported there.
No module is pruned from the target import closure. No other old proof dependency
is removed. The target's new proof dependencies are exactly the construction and
comparison nodes.

## Where the brief, the DAG or earlier work was wrong

The first worker's fibre comparison was false: it assumed no relation at all
between `Y → S` and `X → T`. For example, over an algebraically closed field k,
let T=Spec k[t], X=Spec k[t,x,y]/(xy-t), and f be projection. Its generic fibre is
geometrically integral but its fibre at t=0 is reducible. Taking U=V=T, S=Y=T,
and q=g=id satisfies all the old comparison hypotheses; g has point fibres at
every s, contradicting the claimed equivalence at zero. This erroneous new
statement is removed, not marked as a remaining disputed library statement.

The first worker's node statements were merely pointers to Lean and the docstring
proofs were incomplete. They now give self-contained statements, detailed source
arguments, correct dependencies, and the exact final Lean signatures.

The upstream stronger model theorem imports this target, so cannot be used here.
Searches with different wording found relevant Mathlib invariance and reduction
facts but no complete radicial construction theorem. The proved connectedness
field-extension argument in `GeometricallyConnectedCheckAfterExtension` provided
a useful proof pattern, adapted locally to irreducibility rather than importing
an irrelevant public connectedness interface.

## New nodes

`lem-sbc-radicial-preparation-construction`: the source construction, with a
universal homeomorphism onto the original pullback family. It proves no fibre
comparison, so is strictly the construction part of the argument, not a renamed
copy of the target. Its proof plan retains generic flat finite presentation.

`lem-sbc-radicial-preparation-fibre-comparison`: a proved general invariance
statement for arbitrary base change followed by a source universal homeomorphism.
It assumes no generic point, affineness, reducedness, or finite type; the specific
construction supplies exactly its required map. Its project proof dependency is
`lem-weil-common-extension-fields`. No change records are required for these new,
previously absent declarations.

## Second reading by J2

1. Compared the existing delivered module with the repository using `diff` and
   checked the text through `:= by`: every existing declaration signature is byte
   for byte identical. No existing definition or statement changed. The two other
   modules and their nodes are new. Verdict: pass after repair.
2. Compiled all three modules in dependency order through `lcompile.py`, without
   errors or warnings. Scanned for forbidden declarations and hollow definitions;
   none occur. The only remaining `sorry` is the construction theorem. Explicit
   `#print axioms` confirms the axiom lists recorded above. Verdict: pass.
3. Found and removed the false comparison, including the counterexample above.
   The repaired construction comes from [Stacks 0559](https://stacks.math.columbia.edu/tag/0559).
   Its characteristic-zero case takes the identity field extension; relative
   dimension zero and empty special fibres are allowed. Comparison is fully
   proved and handles empty fibres through the homeomorphism equivalence.
   Repeated leanfinder, loogle (quoted identifier), and grep searches with new
   wording, and searched the local Sheaf and upstream sources. LeanSearch was also
   attempted and recorded as unavailable (Internal Server Error), without a search
   verdict. Found no duplicate
   public theorem or shorter complete construction. Verdict: pass after repair.
4. The target now performs an actual construction/invariance reduction, using
   Mathlib pullback pasting, homeomorphisms, and surjective irreducibility descent
   to prove the comparison. Imports are minimal for signatures or the proof plan.
   The entire old dependency list is covered in No longer needed. Read
   `dag/units/sk-prop-normal-form.json`: its realized fields are empty; this node
   is below that unit, and neither its normal-form nor slicing steps is bypassed
   or changed. Verdict: pass.
5. Read and repaired all three delivered nodes. Their statements, verbatim Lean
   signatures, proof steps, proof_deps, and proof_origin match the final files.
   The construction has a full docstring proof and matching node; both new nodes
   carry source, searches, creation, blueprint, chapter, unit, and Lean records.
   Verdict: pass after repair.

Second reading changed the false comparison to a proved general theorem; added
the missing pullback universal homeomorphism to the construction; adapted the
target proof; removed its unused direct generic-flat import; completed the
construction docstring, both new nodes, proof metadata, and progress accounting.
