## What changed

Replaced the `sorry` of `AlgebraicGeometry.Scheme.Modules.affine_conormal_sections`
with a conjunction proof without changing its signature. The quasi-coherence
conjunct is proved from existing closed-immersion pushforward, kernel and pullback
results. Uniqueness of left adjoints transports ordinary pullback quasi-coherence
to tensor pullback. Only the affine equivalence and unit formula remain split off
as `affine_conormal_sections_existence`, in its own new module
`Sheaf.AlgebraicGeometry.AffineConormalSectionsExistence`.

Added a private proof import of `WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`.
Added the new helper as a private proof import; all public imports of the existing
module remain unchanged. Updated the existing node's proof, proof_deps and
proof_origin to match the actual reduction. The new node records the affine
comparison followed by the quotient-tensor equivalence, with its full word proof.
No definitions, existing statements or downstream interfaces change.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.affine_conormal_sections`
(node `lem-weil-pbc-affine-conormal-sections`) now has an actual conjunction proof.
Its quasi-coherence conjunct is proved without sorry: an independent scratch
copy of that proof has only the standard axioms.

Hole added: `AlgebraicGeometry.Scheme.Modules.affine_conormal_sections_existence`
(node `lem-weil-pbc-affine-conormal-sections-existence`) is the sole new sorry.
This is a strictly smaller component: it does not assert quasi-coherence.
The full original theorem still depends on sorryAx through this component.
This delivery is a reduction/decomposition, not a fully proved item. One original
hole closed and one lower hole added: net reduction zero.

Removed the first worker's unnecessary hole
`AlgebraicGeometry.Scheme.Modules.tensorPullback_ker_toModules_isQuasicoherent`
and its proposed node `lem-weil-pbc-affine-conormal-qcoherent` before delivery;
the existing library results close that component directly.

## No longer needed

Removed redundant direct proof imports from the existing module:
`Sheaf.AlgebraicGeometry.Coherent`,
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, and
`Sheaf.AlgebraicGeometry.TensorPullback`.
The affine comparison remains a planned dependency imported by the new helper;
tensor pullback remains supplied by the signature's public adjunction import.
Removed redundant `Coherent`, `TensorPullback` and upstream `Modules.Tilde`
imports from the helper. Its quotient-tensor and closed-immersion imports support
the detailed remaining proof plan, rather than adding new statements.

Every old direct proof_dep absent from the revised parent proof_deps is listed here:
`def-weil-closed-immersion`, `def-weil-affine-spectrum`,
`lem-weil-pbc-closed-immersion-affine-cover-criterion`,
`def-pc-module-pullback`, `pqf-def-coherent`,
`lem-weil-pbc-module-pullback-affine-sections`, and
`lem-weil-pbc-tensor-over-quotient-ring`.
These are signature dependencies or steps now carried by the affine-equivalence
helper, not abandoned mathematical steps. No existing DAG module is claimed
unreachable or pruned. The discarded new quasi-coherence node is not delivered.

## Where the brief, the DAG or earlier work was wrong

The original sandbox needlessly introduced a quasi-coherence sorry despite the
existing ordinary-pullback theorem and ideal-kernel tools. Its new nodes copied
old review/search records and contained a non-elementary step with no dependencies;
the parent node was not updated. Their docstrings did not give complete proofs.
The second reading repaired these faults and made fresh searches. LeanSearch
returned an Internal Server Error; its unavailability is recorded without drawing
a mathematical conclusion. LeanFinder, Loogle and local grep returned useful
ideal/ring tools but no complete affine conormal sections theorem with this unit formula.

## New nodes

`lem-weil-pbc-affine-conormal-sections-existence`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-conormal-sections-existence.json`,
is exactly the affine-equivalence conjunct, omitting the independently proved
quasi-coherence clause. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineConormalSectionsExistence.lean`.
Source: Stacks Morphisms 01R3 (2), supplemented by Schemes 01I9 and Algebra 00DF.
No change records are needed: no existing declaration signature or definition changes.

## Second reading by N1

1. PASS. Diff against the repository shows the existing declaration signature is
   byte for byte unchanged. Only its proof and private proof imports change.
   There are no definition changes, forced adaptations or hidden hypotheses.
2. PASS. Both delivered modules compile through lcompile.py in import order.
   There is one named theorem with sorry, listed above, and no forbidden declaration
   mechanism or data definition. Scratch #print axioms checks find only propext,
   Classical.choice and Quot.sound for the completed quasi-coherence proof, and
   these plus sorryAx for the parent and remaining helper.
3. PASS after repair. The remaining helper is precisely one conjunct, rather than
   the whole item under a new name. Its docstring now explains affine preimages,
   the quotient ring, ideal sections, quasi-coherence, the canonical tensor
   comparison, I/I², semilinearity and the unit formula. Checked against the local
   Stacks source at /home/ubuntu/work-bp/sheaf/literature/stacks-project/morphisms.tex,
   Lemma lemma-affine-conormal. Edge cases: I=0 gives zero ideal and conormal;
   I=R gives an empty preimage and zero conormal because I²=I; the zero ring is
   included in this case. No finiteness, flatness or nonempty hypothesis is needed.
   Fresh msearch LeanFinder/Loogle/grep searches and rg in both library roots found
   no duplicate of this affine-equivalence component. Existing kernel/pullback
   tools instead eliminated the proposed quasi-coherence split.
4. PASS after repair. The shorter existing-library route closes quasi-coherence;
   the remaining component follows the original affine/tensor route. The old
   direct proof dependencies and removed imports are accounted for above.
   dag/units/sk-thm-p1.json realized does not name this node or its helper as a unit
   statement or step; its realized route is unchanged and no unit step is bypassed.
5. PASS after repair. The parent node now follows the actual conjunction proof.
   The new node has the required creation/Lean/source/blueprint/search fields;
   proof_deps equals the union of its proof-step uses, and lean.statement is the
   exact signature in the new module. Removed stale inherited review and audit
   fields from the newly created node.

Second reading changed: proved quasi-coherence directly; removed its new theorem,
hole and node; filled the remaining docstring proof and fresh search records;
corrected the parent and helper DAG routes; removed redundant imports; replaced
the misleading progress report with explicit hole counts.
