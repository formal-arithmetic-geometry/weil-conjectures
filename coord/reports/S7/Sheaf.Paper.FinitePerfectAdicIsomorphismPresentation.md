## What changed

Replaced the proof hole in `finitePerfectAdic_isomorphism_presentation` by an assembly
of an explicit constant diagram, actual finite-quotient descent data, and a proved
construction of the reduction maps on the actual etale Isom presheaves. The original
statement, presentation structure, quotient homomorphisms, transport construction,
and public imports are unchanged. No other existing Lean module was changed.

The constant diagram is constructed termwise from the supplied algebraic tower:
exact module-universe lift, coefficient transport along the ULift ring equivalence,
and exact constant sheaves. Its transition is the supplied algebraic transition,
transported through an explicitly constructed coefficient-restriction comparison.
Boundedness and finite locally constant cohomology are proved from perfectness.

`etaleUniversalNormalization_presheaf` is proved without any finiteness or descent
assumptions. Objectwise universal arrows transport isomorphisms; their coefficient
and etale restriction coherence gives naturality by uniqueness. The resulting
factorization equation proves the precise generator normalization square required
by the original presentation. Thus the remaining descent statement does not assume
any Isom-presheaf map or its normalization equation.

The assembly is a decomposition, not a completed proof of finite quotient descent.
The two remaining statements concern distinct parts: normalization of the explicitly
constructed constant algebraic diagram, and descent/scalar comparison for the actual
quotients against that fixed diagram. Neither asserts existence of the original
presentation or supplies its Isom-presheaf reduction maps.

Validation: the first full packet compiled all five Lean modules. Delivery preflight
then detected an import cycle through the old normalization-transport module. The
three elementary universal-factorization/square helpers have been reproduced as
proved private helpers, removing that proof import. The revised `lcompile.py --all`
compiled all five modules with exit code 0, each within 60 seconds (8.6, 39.5, 42.0,
56.4, and 48.3 seconds respectively).

## Proved and sorry left

Closed the original one hole:

- `AlgebraicGeometry.Scheme.finitePerfectAdic_isomorphism_presentation`
  (`lem-weil-pbc-finite-perfect-adic-isomorphism-presentation`).

Added two holes, each a public theorem in a separate new module with source, proof
in words, and matching DAG node:

- `AlgebraicGeometry.Scheme.finitePerfectAdicEtaleConstant_normalization`
  (`lem-weil-pbc-finite-perfect-adic-constant-normalization`). It concerns only the
  specified constant algebraic transition, independently of M, markings, actual
  quotients, realization functors, and maps of Isom presheaves.
- `AlgebraicGeometry.Scheme.finitePerfectAdic_actual_normalization`
  (`lem-weil-pbc-finite-perfect-adic-actual-normalization`). It supplies actual
  quotient descent, its universal arrows, and scalar realization comparisons against
  the explicit constant diagram; it has no constant-model cohomology or universality
  fields and no Isom-presheaf reduction map.

There are zero holes left in the item module and two in the delivery. This is one
upper hole decomposed into two lower holes, not a net decrease of the sorry count.
The generic presheaf theorem, coefficient-universe comparison, explicit constant
objects and transitions, and constant cohomology theorem have complete Lean proofs.
No definition uses a sorry theorem to choose its data.

## No longer needed

No original import was removed, and no module is withdrawn. The new generic module's
proof import of `Sheaf.Paper.NormalizedDerivedIsomorphismTransport` was removed:
its three elementary categorical helpers are now proved privately in the new module.
That older module imports downstream scalar-extension and proper-base-change
applications, so importing it here would create a cycle. The dependency
`lem-weil-pbc-normalized-derived-isomorphism-transport` is not needed by this proof;
no global withdrawal of that existing module is claimed. No global pruning is
claimed. The original direct proof dependencies are now used below the new descent
and constant-normalization nodes rather than directly by the assembly. In particular,
finite-ring constructible origin, constant normalization universality, scalar
extension/pullback, and completed-ring comparisons remain needed mathematics.

The old plan's separate arbitrary choice of constant etale models is unnecessary:
the models and their transitions are explicitly constructed from T. The Isom-presheaf
maps are not a further descent obligation: universal factorization constructs them
and proves both their naturality and normalization squares.

## Where the brief, the DAG or earlier work was wrong

Delivery preflight caught an import cycle that the server's compilation against the
last green library did not expose. The correction removes the old proof import and
uses only the elementary comma-category API, without changing any shared file. An
import-graph check with the sandbox overlay now finds no cycle in the item closure.

No statement is disputed or weakened. No target, adopted source declaration, shared
definition, or other group's module is changed. The unit's route is preserved.

The original presentation node bundled constant models, finite quotient descent,
scalar comparisons, and presheaf-map naturality. The updated proof records distinguish
these tasks and give a complete categorical proof of the last task. Earlier splits
are not used as justification for moving the same existential presentation to a new
name: its constant half is now explicit and its presheaf-map half is proved.

The edge cases of the new statements include the zero quotient ring and empty
schemes. The categorical construction uses universal properties rather than points;
constant cohomology uses finite modules; and the remaining stalk assertion is
vacuous on an empty chart. There is no nonemptiness or nonzero-ring hypothesis.

## New nodes

`def-weil-pbc-etale-universal-normalization` records the canonical coefficient mate
and the sourcewise universal-arrow property with etale restriction coherence.

`lem-weil-pbc-etale-universal-normalization-presheaf` records the proved construction
of a natural normalized map on the source-site Isom presheaves from two such arrows.

`def-weil-pbc-finite-perfect-adic-constant-normalization` records the universe-lift
instances, coefficient restriction comparison, and explicit constant diagram and
transition constructed from T.

`lem-weil-pbc-finite-perfect-adic-constant-cohomology` records the proved boundedness
and finite lisse cohomology of those explicitly constructed constant levels.

`lem-weil-pbc-finite-perfect-adic-constant-normalization` records the remaining
universal-arrow and restriction-coherence statement for the explicit constant
transition. Its source proof is independent of actual quotient descent.

`def-weil-pbc-finite-perfect-adic-actual-normalization` records the actual-quotient
and scalar-comparison data against the fixed constant diagram, omitting all
Isom-presheaf reductions and constant-model cohomology/universality requirements.

`lem-weil-pbc-finite-perfect-adic-actual-normalization` records the remaining finite
quotient descent and scalar-comparison step.

The original presentation node's proof, proof dependencies, and proof origin are
updated to the written assembly. No change record is needed: no existing definition
or statement has changed and no other existing module or node is edited.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
