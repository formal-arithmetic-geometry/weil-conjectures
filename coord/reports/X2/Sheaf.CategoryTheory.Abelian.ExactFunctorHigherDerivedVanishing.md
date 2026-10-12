## What changed

Replaced the sole `sorry` in
`lean/Sheaf/CategoryTheory/Abelian/ExactFunctorHigherDerivedVanishing.lean`,
`CategoryTheory.Functor.isZero_rightDerived_obj_of_exact`, with a direct Mathlib proof.
Added the proof-only import `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
The declaration's signature and both existing public imports are unchanged.

Choose `I : InjectiveResolution M` using `HasInjectiveResolution.out`.
`I.cocomplex_exactAt_succ q` gives zero homology in degree `q + 1`.
Apply `v.map_isZero`, and transport along
`(I.cocomplex.sc (q + 1)).mapHomologyIso v` and
`I.isoRightDerivedObj v (q + 1)` to obtain the result.
The comparison is applicable because the finite-limit and finite-colimit hypotheses
synthesize `v.PreservesHomology`. This follows the existing node's three proof steps,
using the Mathlib realization of each dependency; no node changes are needed.

## Proved and sorry left

Proved `CategoryTheory.Functor.isZero_rightDerived_obj_of_exact`
(blueprint: `lem-sc-exact-functor-higher-derived-vanishing`).
One of one original sorries closed; zero sorries remain; none split off.
Local single-file compilation passes without warnings.
The required delivery dry run also checks the declaration's axioms and server compilation.

## No longer needed

None. Both original public imports support the unchanged statement.
The proof uses every original proof dependency:
`def-sp-left-exact-additive` through `InjectiveResolution.isoRightDerivedObj`,
`def-sp-injective-resolutions` through the chosen resolution and its positive-degree
exactness, and `lem-weil-pbc-exact-functor-complex-cohomology` through Mathlib's
`ShortComplex.mapHomologyIso`.
No Sheaf or WeilConjectures statement modules are needed, and none were imported originally.
The unit `sk-thm-curveestimate` realizes its statement only at
`thm-sc-proper-cohomology` and has no realized proof steps; this proof changes no unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The exact-functor cohomology dependency is already
a Mathlib leaf, and its comparison applies to the natural-number-indexed resolution
by taking its degreewise short complex. No integer-to-natural index bridge is needed.
The zero object, injective M, and lowest positive degree q + 1 = 1 are all covered by
the same proof; degree zero is not claimed to vanish.

## Second reading by X2

1. Compared the delivered module with the repository version. The theorem signature and
all existing declarations are unchanged byte for byte; only a proof and one proof-only
import were added. Verdict: pass.
2. Compiled the module locally and checked `#print axioms`; compilation is clean and the
theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. There are no sorries,
axioms, unsafe declarations, or hollow definitions. Verdict: pass.
3. The module has no split-off statements or new nodes. The existing statement is true
and unchanged, and searches found no duplicate Mathlib or upstream declaration. Verdict:
pass.
4. The proof follows the shortest available Mathlib route: choose an injective resolution,
use positive-degree exactness, transport through `mapHomologyIso`, then use
`isoRightDerivedObj`. The added import is proof-only and no unused imports or old proof
dependencies were found. Verdict: pass.
5. The node's proof, proof dependencies, and proof origin agree with the Lean proof; the
unit route and `realized` data are unchanged. Verdict: pass.

Changed only the theorem proof, added the proof-only `PreservesHomology` import, and
recorded this second reading. No pruning or node changes were needed.
