## What changed

Proved `AlgebraicGeometry.ProEtale.qlbar_tail_finite_free_algebra_presentation`
without changing its signature or the public imports. The finite-field tail is final,
so the existing abelian coefficient colimit restricts to it. The filtered ring-object
colimit theorem supplies ring descent; its equation at E supplies algebra descent.
The existing Cartesian-coefficient theorem gives the specified rank, and the already
proved tail module-colimit theorem gives the final sectionwise universal property.
Updated the node proof and dependency list to match this implementation.
Added local irreducibility settings for the point inverse-image constructions, and
scoped the existing backward elaboration option to the theorem. These settings
prevent unnecessary unfolding while checking the categorical constructions. They
do not change any imported module's elaboration environment. The conservative
command check requires a record; see
`coord/changes/Q3-qlbar-tail-presentation-proof-settings.md`.
`tools/downstream.py` and the direct-import search find no current downstream
modules; no consumer adaptation is needed.

Validation: single-file server compilation succeeds. The delivery preflight checks
all declarations and their axioms. No target, definition, or public interface changed.

The generic filtered ring-object lifting theorem
`lem-sfb-filtered-ring-object-cocone-colimit` is used as a tool: it upgrades the
underlying abelian colimit without replacing any unit-level route. The other new
proof dependency, `lem-sfb-qlbar-tail-module-colimit`, is the existing exact module
universal property. Maintainer tool approvals, if needed, remain with the maintainer.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.qlbar_tail_finite_free_algebra_presentation`
(node `lem-sfb-qlbar-tail-finite-free-algebra-presentation`).
Zero holes remain in the item. Zero holes added; zero split off.
The finite-free clause uses the existing declared
`AlgebraicGeometry.ProEtale.cartesianCoefficients_finiteFree`, whose proof is still
`sorry`; that existing dependency is unchanged and is not counted as a new proof here.

## No longer needed

Removed private imports:

- `Sheaf.Paper.FiniteSubextensionsDirected`: the existing directed-order instance
  already supplies the common overfields; the stronger finite-subset and degree claims
  are unused. Its node remains a conceptual dependency for finite composita.
- `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`: the Cartesian-coefficient
  theorem already includes the existence of the required integral basis.
- `Sheaf.CategoryTheory.DirectedRingSheafModuleColimit`: the final module property
  follows directly from the already proved `qlbar_tail_module_colimit`.

Removed direct proof dependencies and obsolete tool approvals for
`lem-sfb-local-field-integral-basis` and
`lem-sfb-directed-ring-sheaf-module-colimit`. Also removed the direct dependency on
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`: its transport is already
encapsulated by the tail module theorem. These nodes may still be needed by other
consumers or transitively; no module is withdrawn and no global pruning is claimed.
All three existing public imports are retained. The private import
`Sheaf.Paper.CompletedCondensedCoefficients` is retained as a required unit-route
module, although the proof uses the source abelian coefficient cocone directly.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The planned proof repeats a module-colimit result that is
now proved, and requests a separate integral-basis theorem although the declared
Cartesian-coefficient comparison already includes its existence. Finality and the
existing filtered ring-object lifting theorem replace the planned explicit extension
of tail cocones by composita. The unit statement and its realized steps are unchanged.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
