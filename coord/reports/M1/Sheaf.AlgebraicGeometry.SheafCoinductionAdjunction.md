## What changed

Reduced `AlgebraicGeometry.sheafHom_restrictScalars_adjunction` into the two actual steps of
its planned proof. Added proof-only imports of `SheafCoinductionAction` and
`SheafCoinductionCounit`. The first supplies the functor, internal-Hom identification, and
multiplication action, without asserting an adjunction. The second supplies natural Hom
bijections and the formula for their inverse, without assuming an adjunction. The original
module constructs `Adjunction.mkOfHomEquiv` from those bijections and derives the counit
formula by evaluating the inverse at the identity. Its existing signature is unchanged.

The module and both intermediate modules compile together with `lcompile.py --all`.
Sources checked online: Stacks Project https://stacks.math.columbia.edu/tag/0A6F and
https://stacks.math.columbia.edu/tag/0BUZ. The local literature files were absent.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.sheafHom_restrictScalars_adjunction` by a
compiling decomposition, not a complete proof independent of sorry. Added two named holes:

- `AlgebraicGeometry.sheafHom_restrictScalars_with_action`, node
  `lem-sc-sheaf-coinduction-action`: construction of H and its internal-Hom action.
- `AlgebraicGeometry.sheafHom_restrictScalars_counit`, node
  `lem-sc-sheaf-coinduction-counit`: natural Hom equivalences with evaluation inverse.

Original module: 1 of 1 holes closed. New modules: 2 holes added. Net holes: +1.
Neither new statement repeats the original conclusion: the first has no adjunction or
counit; the second assumes the functor and action and has no adjunction or counit.
No definitions select arbitrary objects from unproved existence statements; all data
are obtained locally inside the theorem proof.

## No longer needed

No imports removed. No original dependency modules or nodes pruned. The original direct
proof dependency `def-pur-sheaf-hom` moves to the two intermediate nodes, which both need it.

## Where the brief, the DAG or earlier work was wrong

The DAG labels both steps elementary, but their Lean implementation needs a construction
of module structures and restriction maps and a natural Hom-bijection. No existing theorem
covering change of a varying ring sheaf was found: the source constant-ring coextension
and tensor-Hom adjunction have different types.

An arbitrary adjunction between T and H does not force evaluation as its counit: scaling
an adjunction by a natural automorphism changes that counit. The final delivery therefore
asserts the natural evaluation Hom-bijections first and builds the particular adjunction
from them. Its inverse formula determines the counit correctly. No such false arbitrary-
adjunction statement remains in the delivery. Empty opens and zero-ring cases satisfy
both intermediate statements without extra hypotheses. The unit route is unchanged.

## New nodes

`lem-sc-sheaf-coinduction-action`, module `Sheaf.AlgebraicGeometry.SheafCoinductionAction`,
is exactly the construction-and-action part of the original node. It carries a detailed
proof describing the A-action, scalar compatibility, sheaf condition, and functoriality.

`lem-sc-sheaf-coinduction-counit`, module `Sheaf.AlgebraicGeometry.SheafCoinductionCounit`,
is the natural Hom-bijection part for any compatible H and i. Its detailed proof gives the
transpose and evaluation, proves their inverse identities, and explains both naturality
conditions. The original node now records the Lean adjunction assembly from these parts.

## Second reading by M1

1. Compared the delivered adjunction module with the repository version. The theorem
signature and all existing declarations are byte-for-byte unchanged; only proof-only
imports and the proof body were added. The two split-off modules and their node records
are included in this delivery.

2. Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds.
The only remaining `sorry`s are the two explicitly named split-off theorems, each with a
matching node and proof docstring. No forbidden declarations or hollow definitions were
introduced. The adjunction proof uses only the permitted construction and
`Adjunction.mkOfHomEquiv`.

3. Checked both split-off statements against the original target and searched the local
library and recorded Mathlib searches. The action lemma contains only construction and
action data; the counit lemma contains only the natural Hom equivalence and evaluation
formula. Neither restates the target, weakens it, or adds an unnecessary hypothesis.

4. The proof follows the planned unit route: action construction, evaluation Hom
bijections, then adjunction assembly. No shorter existing theorem was found. The
proof-only imports are exactly the two intermediate modules and are not public.

5. The DAG records agree with the Lean declarations: proof steps and dependencies point
to the two split nodes, and the unit route remains represented. No nodes or imports were
pruned because both intermediate results are used by the final proof.

Changed only the proof and imports of the target module, and added the two documented
intermediate modules and matching node files.
