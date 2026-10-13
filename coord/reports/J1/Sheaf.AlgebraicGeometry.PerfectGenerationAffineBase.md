## What changed

Proved `AlgebraicGeometry.perfectGeneration_affine_base` in
`Sheaf.AlgebraicGeometry.PerfectGenerationAffineBase` with the original signature.
The three conjuncts are proved separately: quasi-coherence by the single-complex
cohomology calculation, perfectness by an explicit degree-zero rank-one free local
model, and generation by the affine derived equivalence and cohomology detection.
The private proved helper `AlgebraicGeometry.freeModule_detects_zero` uses
`AlgebraicGeometry.derivedFreeModule_hom_homology` and the shift adjunction.
Restriction along `X.isoSpec` explicitly handles an arbitrary affine scheme and
its originally chosen morphism universe; standard localizations are used only
for the auxiliary spectrum and module category inside the proof.

Added proof imports for the existing free-module Hom calculation and
quasi-coherent free sheaves. Exact derived equivalences and homology detection
are already publicly provided by `DerivedCategory`. Updated only
`proof`, `proof_deps`, and `proof_origin` of
`lem-pc-perfect-generation-affine-base` to describe the compiled argument.
The public-import pruning is recorded in
`coord/changes/PerfectGenerationAffineBaseProofImports.md`.
The route through the affine equivalence is retained. The unit record
`sk-thm-picard-duality` has no realized statement or step that this proof bypasses.
The cited local literature files are absent in this clone; the original sources
were read from [Stacks 06Z0](https://stacks.math.columbia.edu/tag/06Z0) and
[Stacks 09IS](https://stacks.math.columbia.edu/tag/09IS), including its affine-base
paragraph, and agree with the delivered argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.perfectGeneration_affine_base`
(node `lem-pc-perfect-generation-affine-base`).
Also proved the private helper `AlgebraicGeometry.freeModule_detects_zero`.
No `sorry` remains in the delivered module; no holes or new modules were added.
This is a proof from existing declarations, not a decomposition. The affine
comparison still has unproved dependencies elsewhere in the library; this
submission does not claim that the theorem's entire axiom closure is closed.

Compiled the complete file with `lcompile.py`, with no errors or warnings.
Checked the empty scheme / zero-ring case: the rank-one free identification is
valid over the zero ring, the generator calculation requires no nonzero module,
and perfectness is vacuous when the scheme has no points. The proof permits
unbounded complexes, all integer shifts, and arbitrary original `w`.

## No longer needed

Removed `public import Sheaf.CategoryTheory.WeakTriangulatedGenerator`: the
statement uses the explicit shifted-Hom criterion and never uses either
`IsWeakTriangulatedGenerator` or `IsTriangulatedGeneratingFamily`. Its node
`def-pc-generators` remains the conceptual statement dependency, but that module
is not needed by this implementation. PerfectGeneratorExists independently imports the generator module;
KoszulAffineDetection never refers to its declarations.

Removed the temporary direct import
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`, already publicly
provided by the proof dependency `Sheaf.Algebra.Homology.DerivedFreeModuleHomology`.
The second reading also removed the redundant proof imports
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
Both are publicly provided through `Sheaf.AlgebraicGeometry.DerivedCategory`
and its `DerivedHomMayerVietoris` import.

No originally planned proof-dependency node is pruned: the affine comparison and
perfect-complex definition are both used. No additional modules are claimed
unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The DAG's module cohomology
calculation, formerly written inline in step 2, now uses the already proved node
`lem-pc-derived-free-module-hom-homology`. The affine equivalence is stated for
literal `Spec(A)`, whereas the item accepts arbitrary `[IsAffine X]`; the proof
supplies the missing exact transport along `X.isoSpec` explicitly. No signature,
definition, or module held by another group was changed.


## Second reading by J1

1. **Visible declarations: PASS.** Compared the sole delivered Lean module with
   the repository using `diff -u`, and independently compared the entire existing
   theorem signature as strings: it is byte for byte identical. No definition,
   universe binder, hypothesis, conclusion, or existing visibility changed.
   The removed public import is declared in
   `coord/changes/PerfectGenerationAffineBaseProofImports.md`. Checked both
   direct importers returned by `tools/downstream.py --direct`: they import this
   module privately; KoszulAffineDetection does not use the removed declarations,
   and PerfectGeneratorExists publicly imports their defining module itself.
   No forced adaptation is needed.

2. **Proof and axioms: PASS.** Independently compiled the delivered proof and a
   scratch copy printing both declarations' axioms with `lcompile.py`; no errors
   or warnings. The private `freeModule_detects_zero` uses only `propext`,
   `Classical.choice`, and `Quot.sound`. The public theorem uses those plus
   `sorryAx` through existing library dependencies, permitted for this partial
   library stage. No delivered declaration contains `sorry`; no axiom, unsafe,
   opaque, implemented_by, extern, or kernel-check bypass occurs. The local
   perfect model is an explicitly constructed single complex, not data chosen
   from a mere unproved existence theorem. Existential equivalences are eliminated
   within the theorem proof and do not define any exported object.

3. **Split statements: PASS (none).** No new open theorem or node was split off.
   Read the proved private helper and the existing free-module Hom calculation:
   the shift adjunction converts maps from A[-n] into zeroth cohomology of M[n],
   then homology shift and homology detection imply M=0. All integer degrees,
   unbounded objects, and the zero ring are covered. The empty scheme causes no
   problem: perfectness is pointwise and the rank-one/free-zero calculations
   require no nonzero ring assumption.

4. **Route and pruning: PASS after import cleanup.** Read the proof from the
   three top-level conjuncts downward. It uses the existing affine comparison,
   explicit rank-one local perfect model, and proved module calculation. Repeated
   Loogle search with `CategoryTheory.Limits.IsZero, DerivedCategory.homologyFunctor`
   and source searches using vanishing, projective-source, and generator terms;
   found no shorter complete affine-generator theorem. The existing upstream
   `DerivedCategory.isZero_of_forall_isZero_homology` is already used.
   Checked Stacks Tags [06Z0](https://stacks.math.columbia.edu/tag/06Z0) and
   [09IS](https://stacks.math.columbia.edu/tag/09IS), including the affine paragraph.
   Read `dag/units/sk-thm-picard-duality.json`: no realized unit statement or step
   is bypassed, and the planned affine equivalence remains in the proof.
   Every old `proof_deps` node is retained and used; `## No longer needed` lists
   all removed imports without claiming any globally unreachable module.

5. **Nodes: PASS.** The only changed existing node differs solely in `proof`,
   `proof_deps`, and `proof_origin`. Its four steps match quasi-coherence,
   the local perfect model, scheme-isomorphism/affine transport, and the module
   cohomology calculation. The dependency union is exactly
   `def-pc-perfect-complex`, `lem-pc-affine-qcoh-derived-equivalence`, and
   `lem-pc-derived-free-module-hom-homology`. No statement field or unit record
   changed and no new nodes require validation.

**Second-reader changes:** removed the redundant proof-only imports of upstream
`ExactFunctor` and `HomologySequence`, both already re-exported through
`DerivedCategory`; updated the import descriptions and pruning list above.
Kept the mathematical proof unchanged. Closed one original hole, added zero
holes; no decomposition and no additional claimed closure progress.
