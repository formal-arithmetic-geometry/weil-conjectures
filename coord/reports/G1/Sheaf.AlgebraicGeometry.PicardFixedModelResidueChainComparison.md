## What changed

Replaced the first worker's invalid two-hole decomposition with a real reduction. The existing
module `Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison` now obtains compatible
derived arrows, represents them using the existing `perfect_affine_map_representative`, constructs
`t` from their degree-one section maps and `e1.symm`, and proves annihilation by evaluating the
chain-map equation and using `hCzero`. Its existing signature and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison`, containing the remaining
geometric comparison obligation. It supplies compatible derived arrows, not arbitrary section
maps. It does not assert annihilation and does not need the degree-zero source basis `e0`.
The new imports in the parent are proof-only: `PicardFixedModelResidueDerivedComparison` and
`PerfectAffineMapRepresentative`. The new module's planned geometric proof dependencies are also
plain imports. Existing public imports are needed by the signatures and retain their visibility.
A local heartbeat allowance is documented; each file compiles alone within 60 seconds.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Scheme.picard_fixed_model_residue_chain_comparison` (node
`lem-sc-picard-fixed-model-residue-chain-comparison`) by an actual Lean reduction, including
construction of chain representatives and the annihilation calculation.

Added one named hole:
`AlgebraicGeometry.Scheme.picard_fixed_model_residue_derived_comparison` (node
`lem-sc-picard-fixed-model-residue-derived-comparison`). Its entire proof is `by sorry`, with
source and a complete natural-language construction in its docstring. The target therefore
still depends on `sorryAx`. This is a decomposition: one hole closed, one added, net zero;
no claim of a fully proved geometric target or closure-ledger improvement is made.

The first worker's proposed `picard_fixed_model_residue_chain_comparison_first` and
`picard_fixed_model_residue_chain_comparison_second` holes, modules and nodes were removed from
the sandbox. They are absent from the repository baseline and are not delivered.

## No longer needed

No baseline public import was removed and no baseline module is claimed pruned. The original
parent proof dependencies `def-sc-derived-fiber-betti`,
`def-sc-structure-sheaf-cohomology-pullback`, `def-weil-residue-field`,
`lem-pc-cohomology-sections-affine-base`, `lem-pc-module-pullback-adjunction`,
`lem-pc-rf-perfect-base-change`, and `lem-sc-field-pullback-rank-one-trivial` are no longer
called directly by the parent proof: they belong to the remaining derived-comparison obligation
and are recorded there. `lem-pc-perfect-affine-map-representative` is now actually used directly.
No geometric dependency is claimed globally unnecessary. The rejected First/Second modules were
never baseline modules, so removing them is not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's Second theorem claimed the compatibility equation for EVERY additive source
equivalence, annihilating section map and additive target map. Taking `t = 0` and `γ = 0` makes
its left side zero independently of the pullback on H-one. With one identity map on a proper
smooth genus-one curve over a field, structure coefficients, and minimal complexes with zero
differentials, the hypotheses hold and H-one is nonzero; the right side is the image of a
surjective equivalence under identity pullback. Thus the statement is false. Its copied
natural-language proof only justified specially constructed compatible maps, not arbitrary ones.

Both proposed nodes also copied the whole original target as their natural-language statement,
used placeholder Lean statements, had no actual proof dependencies, and copied unrelated review
fields. They have been discarded. The repaired parent node records the actual reduction and the
new node records the exact Lean signature and sourced geometric construction. The baseline parent
had listed geometric dependencies whose corresponding proof modules were not directly imported;
the new obligation imports the existing modules for field triviality, derived base change and
affine cohomology comparison. No statement or definition change record is needed: all existing
signatures and definitions are unchanged.

## Second reading by G1

1. Compared the full parent diff with the repository version. Its sole existing theorem's
signature is byte-for-byte identical, as is its docstring. Only proof imports, a documented local
heartbeat allowance, and the proof changed. The new theorem is explicitly declared as new.
Verdict: pass; no visible existing statement or definition changed.

2. Compiled both delivered modules through `lcompile.py`, in dependency order and individually
through the delivery probe. No errors or non-sorry warnings remain. There is exactly one textual
`sorry`, the complete proof of the named new theorem, and no `axiom`, `unsafe`, `opaque`,
`implemented_by`, `extern`, or definition containing `sorry`. Explicit axiom checks and the
launcher delivery probe verify the permitted axioms plus the expected remaining `sorryAx`.
Choices of chain maps come from the proved affine representative theorem and have specified
localization; no object is defined from an arbitrary witness of an unproved existence theorem.
Verdict: pass as a decomposition, not a completed target proof.

3. Rejected the false universal compatibility split using the zero-map test above. Checked the
replacement against Stacks Tag 0BF2, its cited base-change and perfect-complex arguments, and the
baseline complete geometric proof. It asserts compatibility for representatives of CHOSEN derived
arrows, which naturality justifies. Empty index sets give the unique product map, zero source
rank gives zero H-one, and changing a representative by a null-homotopic map preserves residue
homology. It omits the annihilation conclusion and e0 and is strictly the geometric part of the
argument. Its docstring explains source triviality, residue minimality, kernel projections and
naturality. LeanSearch was attempted and returned Internal Server Error, recorded as unavailable.
Searches with LeanFinder, Loogle and grep found no duplicate geometric result;
the existing affine representative theorem and HomologicalComplex.Hom.comm are used.
Verdict: pass.

4. The proof first uses the existing affine representative theorem for chain-map lifting, then
proves the bottom-differential calculation directly. The geometric part remains one sourced
obligation. New proof-only imports use plain `import`; public imports serve signature data.
The old parent proof dependencies are accounted for above and retained in the geometric node
where needed. Read `dag/units/sk-prop-av-cube.json`: its realized statement and step lists are
currently empty, and this parent is a below-unit node. No unit statement, step, or chapter route
was bypassed or changed. Verdict: pass.

5. Read both delivered node files against the Lean. The parent proof steps describe derived
comparison, representative construction, and the annihilation equation; proof_deps is exactly
the new comparison node plus the existing affine representative node. The new node has its own
statement, full verbatim Lean signature, source, complete proof steps with union proof_deps,
search records, creation metadata, chapter, unit and blueprint provenance. Its fields contain
no copied claims of a completed review. Verdict: pass.

Second reading changed the false decomposition, performed the chain-map reduction and
annihilation proof, replaced both proposed nodes with one accurate geometric obligation, updated
the parent DAG proof metadata, and corrected the report's progress accounting.

## New nodes

`lem-sc-picard-fixed-model-residue-derived-comparison` supplies the derived arrows and residue
identifications natural for every chain representative. It leaves only the geometric part of
Stacks Tag 0BF2's model comparison open; lifting to chain maps and annihilation are proved in the
parent from existing declarations. The module has a sourced full proof docstring and one named
hole. No definition or existing statement changed, and no change record or forced adaptation
is needed.
