## What changed

Proved `AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.scalar_kflat_descent`
in its original module, preserving every existing signature, definition and public import.
Added proved private helpers for good-model preservation, resolving-class descent,
canonical counit component formulas, normalized descent, and isomorphism cancellation. Added private proof
imports for the actual algebraic inverse image, topos exactness, K-flat resolutions,
tensor-flatness transport, resolving-class extension, and derived fractions.
The node now records this shorter resolving-class route. Local transparency options
and local irreducibility avoid repeatedly unfolding large functor and localization
implementations; the counits
use an explicit composition of natural squares and proved component formulas.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.scalar_kflat_descent`
(node `lem-weil-isomorphism-scalar-kflat-descent`). Added zero holes and split off zero
statements. No `sorry` remains in the delivered Lean module. Every new private helper
is proved. The complete module compiled cleanly with `lcompile.py` in 47.3 seconds.
The theorem uses the existing library dependencies as permitted by stage 3.

## No longer needed

Removed private import
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
Node `lem-weil-pbc-site-derived-tensor-descent` is not needed by this proof: directly
extend on the resolving class using `lem-sc-nattrans-from-resolving-class`, then use
full faithfulness of the existing derived localization. This avoids the separate
localization equivalence and all two-variable tensor-descent machinery. Historical
maintainer tool approvals are left untouched. No module is withdrawn; other users
may still need that theorem. All other original imports remain because they expose
the existing statements or are directly used by the proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The plan's separate localization model
is unnecessary: the library already proves extension from a resolving class. The
supplied `comm` and `HomotopyCompatible` hypotheses are retained, although this
assembly needs only chain naturality of `b`: the actual additive functors preserve
homotopies, and their derived targets already identify homotopic maps. Edge cases
include zero/empty schemes, identity resolutions, arbitrary unbounded complexes,
and nonflat coefficient maps; no extra hypothesis was used.

Searched with the required LeanFinder, Loogle and grep services and local `rg`.
The hits supply exact-functor comparison, localization full faithfulness and resolving
extension; no existing theorem states the whole supplied-comparison descent result.
The newly used resolving-class theorem is already Lean-proved, and the algebraic
inverse-image and topos-functoriality declarations supply generic operation/limit
interfaces required by the existing pullback theorem; none replaces a unit step.
No new nodes or consumer adaptations are needed. `tools/downstream.py` reports zero
import consumers of the item and only the item as a textual user of its theorem.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
