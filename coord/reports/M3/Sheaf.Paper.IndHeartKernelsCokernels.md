## What changed

Implemented the square-category argument in Sheaf.Paper.IndHeartKernelsCokernels:
explicit identity-square and zero-source-square zigzags prove finality; Mathlib comma
colimits prove filteredness; the arrow equivalence on a small model proves essential
smallness; final reindexing and joint reflection reconstruct the canonical arrow colimit.
The constructible closure and smallness clauses are taken from their existing modules.
The generic exact-colimit calculation in Sheaf.CategoryTheory.ArrowExactColimits is also
fully proved, using pointwise (co)kernels and explicit canonical comparison equations.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.ProEtale.indHeart_kernelsCokernels
(det-ind-heart-kernels-cokernels): 1 of 1 original holes proved. Also proved the new
helper CategoryTheory.Limits.arrow_exact_colimits (lem-sfb-arrow-exact-colimits).
Holes added: none. Sorry left in either delivered module: none. The existing canonical
presentation, coefficient-heart closure and coefficient-heart smallness theorems remain
proof dependencies and are used with their unchanged signatures. No definition changed.
Both modules compiled together successfully through lcompile.py --all against the
current dependencies on 2026-10-19. The original theorem and all existing public
definitions retain their signatures.

## No longer needed

The direct sk-lem-coefficient-heart theorem is not used. The proof uses the narrower
det-lem-coefficient-heart-closure and det-lem-coefficient-heart-small declarations
instead; these provide exactly the closure, abelian structure and smallness needed. det-ind-heart-full-faithfulness is not needed directly: ind-constructibility
follows from ObjectProperty.of_essentiallySmall_index and the two mapped cocones.
The alternate transport via def-weil-pbc-internal-abelian-sheaf-module-equivalence,
lem-weil-pbc-ring-sheaves-grothendieck and sk-def-sfb-sheaf-tensor is replaced by the
existing internal-module Grothendieck instance lem-sfb-modobj-grothendieck; the proof-only
imports `Sheaf.CategoryTheory.SheafTensor` and
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` were removed.
The obsolete direct import
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses` was also removed;
the internal-module Grothendieck instance supplies the ambient exactness directly.
The direct imports `Sheaf.Paper.IndHeartFullFaithfulness` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` were also removed; the former
is not used directly and the latter is already available through the statement imports.
The `Sheaf.Paper.CoefficientHeart` proof import is replaced by the separate closure
and smallness modules. The obsolete top-level tool_uses approval for
lem-weil-pbc-ring-sheaves-grothendieck is removed from the node: the proof uses
lem-sfb-modobj-grothendieck instead.
The helper needs no import of
`Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels`: it proves the pointwise
universal properties directly using the more basic evaluation lemmas.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report described Sheaf.Paper.CoefficientHeart as absent. It is
present in the current shared sources; the proof uses its separate closure and smallness
dependencies directly, so no replacement of that parent module is needed. The direct
identity-square and zero-source-square finality arguments avoid finite-presentation
factorizations, as already prescribed by the repaired node proof. The unit route is kept.

## New nodes

lem-sfb-arrow-exact-colimits is fully proved and states only the generic commutation calculation of step 6,
with the ambient exact-colimit hypothesis explicit. It neither asserts square-category
filteredness/finality nor constructibility nor the canonical presentation theorem.
Empty schemes and zero arrows impose no extra restriction; arbitrary J is allowed only
when its colimits exist and are exact. The blueprint search found the parent proposition
and unrelated specializations, with no matching general node.

The exported `ZeroObject` scope addition is recorded in
`coord/changes/ind-heart-kernels-cokernels-zeroobject-scope.md` because the proof uses the
zero-source square.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
