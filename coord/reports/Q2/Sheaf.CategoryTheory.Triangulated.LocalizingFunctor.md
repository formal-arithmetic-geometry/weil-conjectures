## What changed

Proved both declarations in `Sheaf.CategoryTheory.Triangulated.LocalizingFunctor`.
The general theorem proves the localizing intersection properties, uses the target
closure's full inverse image as a candidate, and restricts exactness and coproduct
preservation using Mathlib's full-subcategory API. Retained the proof-only import
`Sheaf.Paper.LocalizingClosureExistence` for its declared ambient coproduct existence.

The pro-etale theorem applies the general result after proving that the two indexing
conventions give equal closures. The private comparison proof injects nonzero
summands into endomorphisms, removes zero summands by the universal property, and
shrinks the support. The small-support calculation follows the proved private helper
in `Sheaf.CategoryTheory.CompactTestsRightAdjointCoproducts`; its module is not needed
as an import. Updated the existing node's proof and proof_origin to describe this
argument. All existing public signatures and visibility remain unchanged.

## Proved and sorry left

Holes closed (2 of 2):
- `CategoryTheory.Functor.maps_localizingClosure`.
- `AlgebraicGeometry.ProEtale.maps_localizingClosureProEtale`.

Holes added: zero. No sorry remains in any delivered module. The specialization
uses the existing stated theorem `AlgebraicGeometry.ProEtale.localizingClosure_exists`
(node `det-def-localizing-closure-existence`), whose proof has since landed in the
current sources. No dependency theorem is changed by this delivery.
This is a proof from the declared dependencies, with no decomposition into new holes.

Validation on resumption (2026-10-19): the current-source interface comparison
reports no public signature changes, both original holes closed, and zero added holes.
A fresh `deliver3.py --no-push` passed compilation, axiom checking and preflight
at dry-run commit `3e151fbc39` (review class CODEX because the existing node proof
was updated). No lines exceed 100 characters. The retained earlier standalone
`lcompile.py` check also compiled the complete module without errors or warnings
in 7.0 seconds.

## No longer needed

No existing imports, nodes, or modules were removed or pruned. All four recorded
proof dependencies are used. The source closure need not be intersected with the
inverse image: minimality applies directly to the latter. This simplifies the
candidate without bypassing a unit or dropping any dependency.

## Where the brief, the DAG or earlier work was wrong

The existing `localizingClosure_exists` signature supplies coproduct existence and
closure properties but does not expose the equality of the two indexing conventions
mentioned in its proof. That equality is proved here, with empty support covered
by the same universal-property argument. No statement or definition repair was needed.
The compiler service intermittently returned exit 124 (busy or unreachable); retries
were made without changing the compile limit or launcher scripts.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
