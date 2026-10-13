## What changed

Proved `ExteriorAlgebra.exists_koszul_projective_resolution` in
`Sheaf.RingTheory.KoszulProjectiveResolution`, without changing its signature or public imports.
Added the proof-only imports `Mathlib.LinearAlgebra.ExteriorPower.Basis` and
`Mathlib.Algebra.Category.ModuleCat.Projective`. A proved private helper identifies the
first boundary with `Finsupp.linearCombination` under the degree-zero and degree-one
exterior-power equivalences.

The proof explicitly constructs the quotient augmentation with `ChainComplex.toSingle₀Equiv`.
It proves surjectivity and kernel-image exactness, identifies degree-zero homology by the
cokernel isomorphism, uses the supplied Koszul-regularity for every positive degree, and
bundles the original complex using exterior bases to prove every term projective.
The augmentation calculation adapts the existing proved argument in
`Sheaf.RingTheory.KoszulRegularSequenceDualComplex`; importing that file is impossible
because it reaches this item through `Sheaf.RingTheory.KoszulExtDualHomology`.
No arbitrary existence witness supplies data to a definition.

Updated the existing node's proof and proof_origin to describe the actual Lean argument.
Its three proof dependencies are retained. The unit `sk-thm-picard-duality` has no
realized statement or steps here, and its route is unchanged.

Searches through leanfinder, loogle and grep found the general projective-resolution
constructors and `ModuleCat.projective_of_free`, but no direct Koszul-resolution theorem
available without a cyclic import. Read the pinned Mathlib signatures and the existing
augmentation proof. Checked the sources [0623](https://stacks.math.columbia.edu/tag/0623),
[062E](https://stacks.math.columbia.edu/tag/062E), and
[0BQZ](https://stacks.math.columbia.edu/tag/0BQZ).

## Proved and sorry left

Closed the only original hole:
`ExteriorAlgebra.exists_koszul_projective_resolution`
(node `new-j3-koszul-projective-resolution`).
Added zero holes and split off zero statements. No `sorry` remains in the delivered module.
The private helper `ExteriorAlgebra.koszulBoundary_zero_quotient_formula` is proved.
This is a proof, not a decomposition. Upstream dependencies retain their existing status.

The proof covers `r = 0`, the zero ring, and `I = ⊤` without extra assumptions:
quotient surjectivity and kernel-image exactness still hold, and exterior bases permit
empty index types. No properness, positivity, or nontriviality is used.

## No longer needed

None. No original imports or proof-dependency nodes are removed; all three planned
nodes are used. The cyclic augmentation module was never an import of this item,
so avoiding it does not count as pruning a module from the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The planned argument matches the available
Mathlib APIs. The existing augmentation proof cannot be imported here because that
would create an import cycle; its needed degree-zero calculation is proved locally.

## Second reading by J4

1. Compared the delivered module with the repository version. The existing theorem signature and all
   public declarations are byte-for-byte unchanged; only two proof-only imports, a private helper,
   and the theorem proof differ. The node records the revised proof route and dependencies.
   Verdict: pass.
2. Compiled `lean/Sheaf/RingTheory/KoszulProjectiveResolution.lean` with the pinned
   `lcompile.py` tool. The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`; the only theorem hole originally present is closed. The construction uses
   `ChainComplex.toSingle₀Equiv`, proves the augmentation chain map, exactness, quasi-isomorphism,
   and projectivity directly. Verdict: pass.
3. Checked the private degree-one boundary formula and the quotient exactness argument on the
   edge cases `r = 0`, the zero ring, and `I = ⊤`; no extra properness or positivity hypothesis is
   introduced. No new public statement or split-off theorem was added, and the docstring gives
   the complete mathematical route. Verdict: pass.
4. Reviewed the proof from the top downward against Mathlib and existing Sheaf declarations.
   The three planned proof dependencies remain in use, and the cyclic augmentation module is
   avoided because importing it would create a cycle. No shorter available theorem was found;
   the two additional imports are proof-only and necessary. Verdict: pass.
5. Checked the DAG node against the Lean proof. Its proof steps, dependencies, origin, and
   unchanged unit route agree with the implementation; no realized unit statement or step is
   bypassed. Verdict: pass.

Changed nothing during second reading: the delivered proof and node already satisfy the checks.
