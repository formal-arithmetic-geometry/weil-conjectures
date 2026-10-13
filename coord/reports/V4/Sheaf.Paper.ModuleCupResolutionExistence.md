## What changed

The second reading removed the proposed `CupResolutionAssemblyData` structure, which duplicated the existing component conclusion. The component theorem is now decomposed into two strictly simpler named obligations: section-map assembly and the chain equation conditional on those maps. The realization proof uses the resulting component theorem.

## Proved and sorry left

Hole closed: `moduleCup_component_data_exists`. The already proved `moduleCup_resolution_realization_exists` is kept via that theorem.

Sorry left: `moduleCup_component_section_map_exists` and `moduleCup_component_chain_equation`, nodes `lem-sc-module-cup-resolution-section-map` and `lem-sc-module-cup-resolution-chain-equation`. One hole closed and two added: this is a decomposition, net minus one, rather than a completed proof.

## No longer needed

The proposed node `lem-sc-module-cup-resolution-assembly-data` and its declaration were removed. No imports or existing declarations were pruned. The old direct dependencies `def-pc-tensor-complex-sheaves`, `def-pur-sheaf-tensor-product` and `def-sc-module-cup-resolution-data` now belong to the two lower nodes; the parent directly uses only those lower nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier split introduced `moduleCup_component_structure_exists : Nonempty (CupResolutionAssemblyData D)`, whose structure fields were exactly the witnesses already required by `D.ComponentData`; it merely renamed the same open theorem. The corrected decomposition separates the section formula from the Leibniz chain equation, and each lower statement is used by the parent theorem.

## Second reading by V4

1. Statements and signatures were compared with the repository. Existing declarations are unchanged; the duplicate intermediate declaration and node were removed.
2. All three files compile locally. The two new public named theorems have whole proofs `:= by sorry`, source citations, detailed proof docstrings and matching nodes. No definition contains a hole. Axiom probes are checked by deliver3.py.
3. Independently searched leanfinder, loogle and grep, and read TensorSection and the existing Cech coproduct assembly. The results provide infrastructure, not these statements. The section-map lemma drops the chain conclusion; the chain lemma assumes the section formula and constructs no maps. Zero inputs, degree-zero sign and negative extension terms fit both statements. The maps are uniquely determined on tensor generators and coproduct inclusions, so the conditional chain statement applies to any family with the formula.
4. The shortest valid packaging route is the existing `moduleCup_component_data_exists` followed by `HomologicalComplex.Hom.mk`; the realization proof follows that route and keeps the unit dependency.
5. The component node records both new obligations; realization retains its existing component dependency. Each new theorem lives in its own module, imported privately by the parent; the public realization-data import supplies signatures. No old proof dependencies were removed. The unit realized record is unchanged (these nodes are below its cube step).

Changed: removed the invalid duplicate structure/theorem, added the two genuine component sub-obligations, and made the parent and realization proofs use them.

## New nodes

`lem-sc-module-cup-resolution-section-map` and `lem-sc-module-cup-resolution-chain-equation` record the two decomposed component obligations.
