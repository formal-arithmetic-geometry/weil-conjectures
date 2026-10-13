## What changed

The item theorem keeps its original signature. Its proof now obtains geometric Cech
homology coordinates from the new PicardExternalCupLeftCechGenerators module and
uses tensor_kunneth_nat on the scalar models to construct the tensor comparison
isomorphism. For each pure tensor in each summand, it lifts factor homology classes
to cycles and equates the Cech cup formula with the normalization of the supplied d.
DirectSum.linearMap_ext and TensorProduct.ext' extend this equality to all classes.
Evaluation at the inverse Cech coordinate equivalence proves the displayed square.
The item's proof imports the generator module and TensorKunnethNat privately.
Its DAG node now records this route. No existing definition or statement changes.

## Proved and sorry left

Closed in the item's source: AlgebraicGeometry.Scheme.Modules.
picardExternalCup_left_cech_comparison (originally the sole hole).
Added: AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_generators,
node lem-sc-picard-external-cup-left-cech-generators, in its own new module.
This is a decomposition: one upper hole is closed and one geometric hole is added;
it is not a claim of a net hole reduction or of an axiom-free geometric proof.
The generator lemma has no supplied scalar-total cochain map and no comparison
with its homology map. The proof in the item supplies that comparison, constructs
a using scalar tensor Kunneth, and performs the cycle lifting and spanning argument.

The scalar algebra argument compiled without warnings in scratchpad/AlgebraCheck.lean.
The entire combining proof, with the concrete Cech functors replaced by arbitrary
functors and the generator assertion supplied as a hypothesis, also compiled
without warnings in scratchpad/CoordinateCheck.lean (7.1 seconds).
Concrete verification (2026-10-13): lcompile.py compiled the original comparison
module successfully in 6.4 seconds. Its --all check then compiled the new generator
module in 3.9 seconds and the complete comparison module in 7.0 seconds, with no
compiler warnings or errors. The formerly missing shared exactness dependency is
now available. No dependency source, interface, or tool was changed to bypass it.

## No longer needed

No original import is removed: PicardExternalCupLeftCechExact supplies the two
concrete functors appearing in the existing public statement. No globally pruned
node or module is claimed. The original refinement, affine comparison, quasi-coherence
and cup-compatibility dependencies are needed below the new geometric generator
node, rather than directly by the combining proof. Existence of a normalized scalar
cochain realization is unnecessary: the original theorem quantifies over supplied d.
The cochain module stays necessary for the normalization predicate in the statement.

The following old `proof_deps` are no longer used directly by the comparison proof;
all remain in the new generator node's proof plan, so none is globally pruned:

- `def-sc-cech-cup-product`
- `def-sc-cech-refinement-cochain-map`
- `lem-pc-module-pullback-adjunction`
- `lem-sc-cech-comparison-map-iso-affine`
- `lem-sc-cech-comparison-map-naturality`
- `lem-sc-picard-affine-diagonal-intersections`
- `lem-sc-picard-cech-cup-pullback-compat`
- `lem-weil-pbc-module-pullback-quasi-coherent`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`

## Where the brief, the DAG or earlier work was wrong

The proof dependencies do not directly state the scalar, integer-extended natural
Cech generator calculation: the refinement and cup compatibility declarations use
module-valued or additive Cech complexes. The new node collects that specific
geometric calculation, while the scalar-total Kunneth and spanning argument is
implemented here. The geometric statement was checked on empty schemes, zero
coefficients and degree zero: all zero-space cases have the unique maps and
isomorphisms; degree zero has only the (0,0) summand and the section pairing.
The unit sk-prop-av-cube has no realized node at this level, and its fixed statement
and step are unchanged. The source Tag 0BED was read online because the local
literature/stacks-project/varieties.tex file is absent. Mathlib searches ran through
msearch.py (LeanSearch unavailable, LeanFinder and Loogle returned generic homological
complex constructions, grep found no Cech cup or tensor Kunneth match in Mathlib).
The earlier shared-build availability blocker has cleared; both modules now compile.

## New nodes

lem-sc-picard-external-cup-left-cech-generators states the natural geometric Cech cup,
its Cech tensor homology coordinates in terms of scalar-model factor homologies,
the product comparison, and the external-cup formula on each pure tensor generator.
Its module contains exactly one named public theorem with exactly `:= by sorry`.
Its docstring gives the complete refinement, Leibniz, affine comparison, tensor
Kunneth and cycle-compatibility argument with sources. No a or scalar-total map d
occurs in its statement. The new node carries the actual logged searches, the
parent's chapter/unit, and the precise equation-kunneth-on-cech blueprint ancestry.
Proof-only visibility changes are recorded in `coord/changes/picardExternalCupLeftCechComparison.md`; there are no forced adaptations.

## Earlier second reading (a previous round; superseded)
The retained proof was independently checked by compiling the item together with its new generator module and the exactness dependency. The target signature is unchanged, the generator statement is a strict intermediate reduction, and the unit route through the Cech exactness node is preserved.

## Second reading by J2

1. **Interface comparison — pass.** Compared the delivered comparison module with the
   repository version. The theorem signature and all existing declarations are byte-for-byte
   unchanged; only proof-only imports, namespace openings, and the proof body differ. The new
   generator declaration is recorded as a split-off node with its verbatim Lean statement.
2. **Proof and axioms — pass.** `lcompile.py --all` compiles both delivered modules without
   errors or warnings. The comparison theorem has no `sorry`; the sole remaining `sorry` is the
   named generator theorem and is documented with its source, proof sketch, and DAG node. No
   forbidden declaration or hollow definition was added.
   A scratch `#print axioms` check of both declarations reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter remains because the
   geometric generator theorem is open.
3. **New statement — pass.** The generator statement is a strict intermediate assertion about
   the natural Cech map and pure tensor generators. It supplies the geometric part of the
   argument; the parent implements scalar-total Kunneth and comparison with any normalized d.
   Edge cases (zero coefficients,
   empty schemes, and degree zero) are covered by the stated construction. Searches found no
   existing library or Mathlib declaration duplicating it.
   Independently read Stacks Tag 0BED, especially equation the project server and its functoriality
   and cup compatibility. Additional LeanFinder search for "Cech cohomology external product
   tensor Kunneth comparison natural transformation on coefficient sheaves" returned generic
   condensed/sheaf tensor constructions; Loogle `"homologyπ"` returned the standard homology
   projection and naturality API. Mathlib grep `Kunneth|[Cc]ech|Čech` returned Cech nerves and
   unrelated results, not this geometric comparison. Repository searches confirmed that the
   existing Picard Kunneth models concern scalar resolutions, not these concrete Cech functors.
4. **Pruning and route — pass.** The proof uses the generator node and scalar tensor Kunneth
   result, then cycle lifting and linear extensionality. No original public import can be removed;
   the exactness module remains the source of the concrete functors. The unit route and its
   realized nodes are unchanged, and no unused proof dependency was introduced.
5. **DAG agreement — pass.** The comparison node's proof steps and `proof_deps` match the Lean
   proof, and the generator node records its declaration, source, searches, chapter, and unit.

Changed during second reading: made the old dependency list explicit, recorded the independent
searches and axiom check, appended this review, completed the change record with the verbatim unchanged old/new signature, and restored
the original single space before the theorem's `:=`. No mathematical statement, definition, proof, node, or import required repair.
