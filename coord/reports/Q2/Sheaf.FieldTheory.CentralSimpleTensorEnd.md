## What changed

Kept the existing signature and docstring of `Field.centralSimple_mulLeftRight_bijective`
byte for byte. Replaced its hole with a reduction to injectivity, followed by the proved
Mathlib dimension formulas for tensors, opposites and linear maps and
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`.
All new imports in the existing module are private proof imports. Its existing public
imports are unchanged. Added only `Sheaf.FieldTheory.CentralSimpleTensorInjective`,
which states the remaining kernel/simplicity step with its source and proof in words.

## Proved and sorry left

Closed the original hole in `Field.centralSimple_mulLeftRight_bijective`, node
`lem-sc-central-simple-tensor-end`, by an actual dimension-comparison argument using
the split-off injectivity statement. Added one hole:
`Field.centralSimple_mulLeftRight_injective`, node
`lem-sc-central-simple-tensor-end-injective`.
This is a decomposition: one original hole closed and one lower hole added, net zero.
The target still depends on `sorryAx`; this is not an axiom-free proof of the target.
During second reading the proposed additional hole
`Field.centralSimple_mulLeftRight_surjective` was eliminated: the target proves
surjectivity directly using Mathlib. No such declaration or node is delivered.
No definitions or arbitrary witness choices were added.

## No longer needed

The repository node originally had empty `proof_deps`, and no original library imports
or nodes were pruned. Removed the draft proof import
`Sheaf.FieldTheory.CentralSimpleTensorSurjective`, its proposed new module and node
`lem-sc-central-simple-tensor-end-surjective`; these were never landed.
Removed the redundant new proof import `Mathlib.LinearAlgebra.Dimension.Constructions`,
whose formulas are public dependencies of the retained dimension imports.
No established library module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The first draft needlessly left surjectivity open, recorded neither three kinds of
search nor detailed proof steps on the new nodes, omitted the source from the
injectivity docstring, and recorded its declaration without its `Field` namespace.
These faults are repaired. Mathlib's Azumaya bijectivity assumes `IsAzumaya`, which
CSA does not provide. The upstream tensor-simplicity result handles extension by a
commutative field, not a general opposite algebra; it does not close this hole.

## New nodes

`lem-sc-central-simple-tensor-end-injective`, in
`lean/Sheaf/FieldTheory/CentralSimpleTensorInjective.lean`, states just injectivity
of the canonical action. Its proof is the kernel argument of
[Stacks Tag 074I](https://stacks.math.columbia.edu/tag/074I), using tensor simplicity
from [Tag 074G](https://stacks.math.columbia.edu/tag/074G).
The node has its Lean signature, source, proof steps, origin, creation and blueprint
records, and actual LeanSearch, LeanFinder and grep searches. LeanSearch returned
Internal Server Error, recorded as unavailable. No change records are required.

## Second reading by Q2

1. Compared the delivered existing module with the repository using `diff` and
   checked its signature bytes. Verdict: the existing declaration's full signature,
   namespace, universe, visibility and docstring are unchanged; no definition or
   target statement changed. Only private imports and its proof changed.
2. Compiled every delivered file locally through `lcompile.py` in import order and
   printed axioms from scratch copies. Verdict: no errors; only the explicitly
   reported named injectivity theorem contains `sorry`; no forbidden declarations
   or hollow definitions. Both declarations use only the three permitted standard
   axioms and `sorryAx`, from that one remaining hole.
3. Checked the injectivity claim against the cited Stacks kernel argument, including
   nontriviality from `CSA.isSimple`, and the small cases A=K and matrix algebras:
   the action is faithful; evaluation of the identity at one rules out a whole kernel.
   The zero algebra is excluded by CSA. Repeated searches with different wording
   using LeanFinder, Loogle, LeanSearch and grep and inspected the upstream tensor
   theorem. Verdict: the remaining statement is true, needed, and strictly the kernel
   part of the original argument, with a complete proof in words and its own node.
   The surjective component was closed directly, so it is no longer split off.
4. Inspected the parent proof, all old dependencies, import visibility and the unit
   `dag/units/sk-thm-br.json`. Verdict: dimension comparison uses the shorter proved
   Mathlib route; the existing unit route and its realized fields are unchanged.
   This parent was not itself a realized unit statement or step. No original proof
   dependencies existed to prune. Checked the new imports for redundancy: the
   tensor-finiteness and opposite-basis instances are needed, and the endomorphism
   finrank formula needs the finite/free matrix module; removed the redundant
   constructions import. No established library module is pruned.
5. Checked node signatures and proof dependencies against Lean. Verdict: the parent
   now cites only the injectivity node and describes the formalized dimension step;
   the new node accurately names `Field.centralSimple_mulLeftRight_injective`, has
   three kinds of search, and records the source-backed kernel proof and provenance.

Second-reading changes: proved the dimension/surjectivity step in the parent;
removed the proposed surjectivity module and node; completed the injectivity
source/docstring, search records and node proof; corrected its qualified declaration
name; updated parent metadata and reported this honestly as a net-zero decomposition.
