## What changed

Replaced the only remaining sorry in
AlgebraicGeometry.Scheme.residuePerfect_quotient_models_succ with a complete Lean
combination of two strictly smaller coefficient-filtration statements and the
already proved
DerivedCategory.exists_bounded_finite_projective_model_of_torAmplitudeIn.
The first new statement supplies bounded finite-module models, without
projectivity. The second detects algebraic Tor amplitude of any given constant
local model from the perfect residue. The existing theorem converts those two
properties into finite-projective models with the required fixed interval.
The proof then transports its algebraic derived isomorphism through exact
universe lift, scalar restriction, constant realization, actual derived
coefficient change and the exact restriction comparison.

The existing definitions and standard instances moved verbatim to
Sheaf.Paper.FinitePerfectQuotientModelData, publicly reexported by the item, so
both lower statements can use them without a cycle. Every old public type and
body remains identical, including both residuePerfect theorem signatures.
No source-library file, target, consumer or unit route is changed.
Change record: coord/changes/D2-finite-perfect-quotient-model-data.md.

Remote lcompile --all passed without warnings: data module 6.4 s, finite-module
step 2.3 s, Tor detection 2.6 s, assigned item 18.7 s. The five unchanged direct
importers also passed against the delivery: FinitePerfectAdicRealization 15.5 s,
FinitePerfectAdicTowerExtraction 9.3 s, IntegralResidueStratumInput 42.1 s,
IntegralResidueStratumLift 40.2 s and ResidueLissePerfectLift 29.5 s. Their temporary
verification copies were removed; no consumer changes are delivered. Exact textual
checks confirmed every relocated definition body and all three retained public
theorem signatures are unchanged. The delivery tool runs the final axiom/sorry
probe and packet checks.

## Proved and sorry left

This delivery is a decomposition, not a complete proof of the mathematical
successor statement: one upper hole is closed and two strictly smaller holes
are added (textual net holes: +1; no closure-ledger progress is claimed).
The item itself has zero sorry; the new definition
module has zero sorry. The unchanged normalization and uniform-induction
proofs are retained.

Closed upper hole:
AlgebraicGeometry.Scheme.residuePerfect_quotient_models_succ
(lem-weil-pbc-residue-perfect-finite-quotient-models).
Its final algebraic perfectness and isomorphism-transport argument is complete.

Added holes, one whole public theorem per new module:

- AlgebraicGeometry.Scheme.finiteQuotient_finiteModule_models_succ,
  in Sheaf.Paper.FiniteQuotientFiniteModuleModels,
  node lem-weil-pbc-finite-quotient-finite-module-models.
  Its conclusion supplies finite modules, with no projectivity or Tor assertion.
- AlgebraicGeometry.Scheme.finiteQuotient_model_torAmplitude,
  in Sheaf.Paper.FiniteQuotientModelTorAmplitude,
  node lem-weil-pbc-finite-quotient-model-tor-amplitude.
  It proves only Tor amplitude of an already given local model, has no
  previous-level premise, and asserts no local finite or projective realization.

Both carry source citations, complete natural-language arguments and matching
DAG nodes. Neither is the original successor theorem with renamed hypotheses.
No new data is selected from an unproved existence theorem in a definition.

## No longer needed

The connected-etale-perfect-constant step
(lem-sfb-connected-etale-perfect-constant,
Sheaf.SixFunctors.ConnectedEtalePerfectConstant) is not needed by this route:
finite-module descent followed by the already proved algebraic bounded-finite-Tor
perfectness theorem replaces it. This removes that planned dependency for this
node, not the module from the library or from other consumers.

All other original planned dependencies remain in the two smaller nodes, or
in the exact restriction used by the combination. The original five public
import lines were consolidated into the data-module public reexport; all five
remain public imports of that lower module. No existing declaration, import
visibility, module or source-library dependency is withdrawn. New proof imports
are precisely the two obligations, BoundedFiniteTorPerfect,
CommutativeSiteDerivedConstantModuleFunctor, RingedDerivedRestrictionGeneral,
and ShortExact (the latter two already used by the existing restriction proof).
No unused proof-dependency modules were added.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies supply the general descent, lissity and tensor APIs,
but none directly states the concrete coefficient-filtration glue between this
module's actual completed reductions and its local-model predicate. That glue
is now exposed as the two independent remaining statements. The plan's final
connected-perfect argument can be shortened using the existing algebraic
BoundedFiniteTorPerfect theorem; no unit-level route is bypassed.

Edge cases were checked against the new statements: n=0 uses the same residue
interval; a=b is permitted; zero objects and zero coefficient rings need no
nontriviality assumption; no completeness of M is added. Empty charts cannot
detect an arbitrary algebraic model's Tor amplitude. Accordingly the first
statement chooses the zero complex on empty charts and the second explicitly
requires a nonempty chart or a zero model. No assumption that the ideal is
principal, maximal, or defines a field quotient is made.

## New nodes

lem-weil-pbc-finite-quotient-finite-module-models: the coefficient triangle,
weak Serre property, finite-ring derived origin and bounded constant descent
produce finite-module complex models in the interval. One remaining sorry.

lem-weil-pbc-finite-quotient-model-tor-amplitude: a geometric stalk recovers an
algebraic constant model; the finite I-adic filtration and derived balancing
propagate the residue Tor interval to every quotient module. One remaining
sorry; no local-model existence is asserted.

def-weil-pbc-finite-perfect-quotient-model-data: records the existing concrete
model predicates and their auxiliary real constructions in the lower module.
This relocates the existing names and bodies and adds no duplicate notion or
proof hole. Change record: coord/changes/D2-finite-perfect-quotient-model-data.md.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
