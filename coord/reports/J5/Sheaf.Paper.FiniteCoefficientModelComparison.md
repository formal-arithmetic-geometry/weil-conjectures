## What changed

Prove `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientModelComparison`
by comparing normalized section actions, constant scalar models, fixed-module sheaves,
and intrinsic ordinary module sheaves. Preserve the original strata and cover members;
remove empty members only in the explicitly designated clause. Transport boundedness
and all ordered cohomological intervals through the actual derived equivalence.

Add two separately proved comparison results under `Sheaf/Paper`: normalized encoding
commutes with pullback, and finite scalar models correspond to finite constant modules.
In the existing item, added imports are private proof imports and the public imports
are unchanged. The new modules publicly import what their statements need.

Correct the parentheses in the structure's interval clause; see
`coord/changes/finite-coefficient-model-comparison-intervals.md`. The outer theorem's
signature and the mathematical DAG statement are unchanged. No source-library file
or target declaration is edited.

## Proved and sorry left

The original item has one hole, in `finiteCoefficientModelComparison`. The delivery
replaces it by a complete proof. The new public results are `encoding_pullback_fixed`
and `finite_scalar_model_iff_constant`; neither adds a hole. There are no `sorry`s
in any delivered Lean file: one original hole closed, zero holes added, zero unresolved
statements split off. `lcompile.py --all` compiled all three modules without errors
or warnings: pullback comparison 16.2 seconds, scalar models 23.3 seconds, and the
item 21.1 seconds. The original false interval clause is repaired as recorded below.

The proof still uses existing declared results through its imports; this is the stage-3
proof-dependency convention, not a claim that every upstream theorem is axiom-free.

## No longer needed

Removed direct proof imports: `Mathlib.Algebra.Module.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Sites.Proetale`,
`Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`,
`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`,
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
`Sheaf.Paper.CondensedConstantConstructibility`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
The normalized pullback helper imports the operation-transport module for its proved
section-action identity, so that dependency is retained transitively. The scalar helper
uses finite-presentation theory directly, so that Mathlib dependency also remains.
The source-library module-object basics are still imported transitively.

The nodes `lem-sfb-proetale-object-inverse-image-restriction`,
`lem-pur-proetale-inverse-image-stalk`, and `lem-weil-proetale-constant-sheaf-stalk`
from the planned route are replaced by the existing slice geometric-stalk
comparison in `ProEtaleFiniteModelStalks`. Their obsolete top-level tool approvals
are removed from this node. `ProEtaleInverseImageStalk` and
`ProEtaleObjectInverseImageRestriction` leave this item's Lean import closure.
`ProEtaleConstantSheafStalk` remains available transitively through retained library
imports. The internal/ordinary abelian equivalence and finite presentation definitions
also remain available transitively. No module is withdrawn.

The larger unfinished `FiniteDiscreteEncodingConstructibility` theorem is unnecessary:
finite scalar models and normalized pullback give its local-model clause directly.
No public import of the adopted source library is changed and no source declaration
is deleted or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original interval field parsed as
`(a ≤ b → vanishing K) ↔ vanishing (E K)`. For reversed endpoints its left side is
vacuous and its right side demands vanishing in every degree, contradicting a
nonzero degree-zero constant module. Parenthesize the equivalence to place both
sides under the hypothesis `a ≤ b`, exactly as the source and DAG intend.
`tools/downstream.py --uses FiniteCoefficientModelComparison` finds two downstream
modules: `IntegralResidueCriterion` privately imports this module and
`IntegralOpenDirectImage` uses its unchanged theorem. Neither statement mentions
the comparison structure or depends on its interval field, so no adaptation is
needed. Both are listed in the change record, which requests renewed target-meaning
review if applicable.

The proof plan understated the distinction between the monoid structure obtained
from the composed constant-sheaf functor and the one obtained from ring-presheaf
sheafification. A proved identity scalar restriction reconciles these structures.
The bridge has an explicit module-category interface and an explicitly constructed
constant presheaf, avoiding repeated unfolding of the monoidal sheafification data.
No coefficient data are selected from an unproved arbitrary-existence theorem.

## New nodes

`lem-pe-finite-discrete-encoding-pullback-fixed`: the normalized section action
commutes with direct image by canonical-section naturality; conjugation of right
adjoints and uniqueness of left adjoints give the inverse-image comparison.
This is a proved separate tool, not an unresolved replacement of the item.

`lem-pe-finite-discrete-scalar-constant-models`: one-point continuous functions
identify the scalar ring with A. Finite presentation agrees with finiteness over
finite A. Invertible scalar extension, monoidal constant-sheaf comparison and module
sheafification identify the encoded model with the constant finite ordinary module.
This is a proved separate tool, not an unresolved replacement of the item.

Change record: `coord/changes/finite-coefficient-model-comparison-intervals.md`.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
