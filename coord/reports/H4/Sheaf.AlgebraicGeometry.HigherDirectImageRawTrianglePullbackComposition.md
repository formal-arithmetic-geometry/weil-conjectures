## What changed

Proved `AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_comp` with its
signature and visibility unchanged. Added proof-only `import all` directives for
`Sheaf.AlgebraicGeometry.AbelianRawPullbackComposition` and
`Sheaf.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift` to use their already
proved private generic tools. No other existing module was changed.

The proved private helper `rawTriangleMap_comp` performs the functoriality, naturality,
and shift-coherence calculation over arbitrary categories. Its statement preserves the
rawTriangleMap and comparison-isomorphism heads. The main theorem substitutes the two
triangle equations, installs shift compatibility using `plusNatIso_commShift` and
`plusCompIso_commShift`, and specializes the helper with the existing `sourceComp`
calculation at module sheaves and the free sheaf on U. This follows the original node's
source/shift route, for arbitrary derived coefficients and every integer degree.

Updated the existing node's proof and direct proof dependencies to describe that code.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_comp`
(node `lem-sbc-raw-triangle-pullback-composition`). The new private helper
`AlgebraicGeometry.Etale.rawTriangleMap_comp` is fully proved. No sorry remains in the
item; no new holes, public declarations, axioms, definitions, or nodes were added.

## No longer needed

No imports were removed and no modules are claimed pruned. The direct DAG proof edges
to `lem-sbc-pullback-single-comp` (module
`Sheaf.AlgebraicGeometry.EtalePullbackSingleComp`) and
`lem-weil-pbc-exact-functor-derived-factorization` are unnecessary in this proof:
the already proved source and shift tools package their calculations. These results
remain transitive dependencies of those tools, so their modules are not claimed absent
from the import closure. The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. Although the public composition and transition
statements use abelian groups or single complexes, their proved private source and shift
tools are generic and apply to ModuleCat and arbitrary complexes. Direct rewriting on
concrete derived morphisms elaborated but exceeded the kernel-check limit. The library's
MorphismDefs implementation note describes this projection-normalization issue. Keeping
comparison isomorphisms and rawTriangleMap intact in the generic helper avoids it; no
shared definition or interface change was needed.

The semantic edge cases require no extra hypotheses: the generic proof uses only category
laws, functoriality, naturality, and shift compatibility, so it allows zero coefficients,
identity maps, empty schemes, and negative as well as zero degrees.

Searches used msearch grep for the theorem name, LeanFinder for derived pullback/shift
composition, Loogle for commShiftIso, and rg on both library roots. No existing complete
arbitrary-coefficient triangle-composition theorem was found; the proved tools above were
used. The unit record was read; its realized lists are empty, and this delivery keeps the
node's planned source and shift argument inside that unit.

## Second reading by H4

1. Compared the delivered module with the repository version. The public theorem signature and all existing declarations are unchanged; only proof-only imports, a private helper, and the theorem proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it is clean and contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declaration. Verdict: pass.
3. Checked the private helper and updated node against the library for duplicate statements. The helper is a strictly generic reduction, while the public theorem remains the original target; no new public split-off statement or node was added. Verdict: pass.
4. Checked the proof from the target downward and reviewed imports. The two added `import all` directives are proof-only uses of proved source and shift tools; the original public imports remain required. The unit's source and shift route is preserved, and obsolete direct proof edges are recorded above. Verdict: pass.
5. Checked the node's proof, proof dependencies, proof origin, and unit route against the Lean proof. The node records the generic helper route and its actual dependencies, with no statement change. Verdict: pass.

Changed only this report during second reading; no Lean declaration, statement, definition, or DAG statement was changed.
