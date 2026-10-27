## What changed

Only Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor and its own DAG node changed.
The public declaration signatures, public imports and existing definitions are unchanged.
Added private proof constructions and three private Mathlib imports for evaluation
adjunctions, pointwise AB5 and the special adjoint functor theorem. The unused section
variable linter is scoped off for actionGrothendieck to preserve its pre-existing
commutativity binder, which the generic diagram-category proof does not need.

Proved the Grothendieck action category by the already implemented separator argument
in DiscreteLattice.resolutions. Proved closedness using preservation of colimits and the
special adjoint functor theorem. Lifted the existing functorial flat resolution directly
to group actions. Constructed the normalized trivial-action adjunction with limit.lift
and the invariant inclusion, proved exactness and uniqueness, and applied uniqueness
of total derived pairs for the ordinary-derived comparison. Constructed the ordinary
strong tensor structure by identity maps and proved its uniqueness by faithfulness.
The docstrings and DAG now describe these actual arguments.

The constructions work for rank zero, zero modules and the zero coefficient ring:
none assumes a nontrivial group or coefficient ring, and all maps use the same limit,
identity and natural augmentation formulas in those cases.

## Proved and sorry left

Closed 7 of the original 8 holes, all in namespace Profinite.DiscreteLattice.DerivedCup:

- actionGrothendieck
- actionTensorLeftAdjoint
- actionFlatResolutions
- trivialProperties
- trivialAdjunctionExists
- ordinaryDerivedIsoExists
- trivialCoreExists

Added 0 holes; split off 0 statements. The one remaining hole is
Profinite.DiscreteLattice.DerivedCup.derivedCoreExists, attached to
def-sfb-lattice-derived-invariants-tensor. Its original full signature and natural-language
proof remain. This is a partial proof delivery, with a net reduction of seven local holes;
it does not claim that the complete target import closure is sorry-free.

For the remaining theorem, the source library already has
Functor.mapDerivedCategoryOplaxMonoidal and its invertible unit comparison in
WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal.
The remaining work is to match that strong structure to this module's particular
cochain and single-functor unit equations, and prove uniqueness of the full structure.
The existing rightExact_tensorComparison_existsUnique addresses the binary comparison
on flat K-flat models; it does not by itself supply the full unit-normalized
CoreMonoidal structure. No replacement statement was introduced for this step.

Validation: the complete final item module compiled remotely with exit code 0 in
51.3 seconds, below the 60-second limit, with no warnings or errors. The source scan
finds exactly the one named sorry above and no lines over 100 characters.

## No longer needed

No modules are withdrawn and no imports are removed. The action-site presentation,
transported action-site tensor-Hom adjunction and action-site flat-resolution transport
suggested by the original docstrings are not needed for the seven closed holes.
Ordinary Mathlib actions, pointwise (co)limits, the existing internal-module instances
and the universal derived-pair uniqueness theorem suffice. Those action-site results
are not declared proof dependencies of this node and are still needed elsewhere.
The existing public imports are retained as part of the unchanged public interface.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG node had no proof steps or proof dependencies, despite the eight explicit
proof holes documented in its Lean module. Its proof now records the actual seven
completed arguments and the remaining derived-core argument. The original action-site
routes for closedness and flat resolutions were unnecessarily indirect: both follow
directly by lifting the existing ordinary module constructions to Mathlib Action.
No mathematical statement or definition is changed or disputed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
