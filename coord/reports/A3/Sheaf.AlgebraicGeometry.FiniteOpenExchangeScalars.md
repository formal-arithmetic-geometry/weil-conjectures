## What changed

Completed both remaining proofs in
`lean/Sheaf/AlgebraicGeometry/FiniteOpenExchangeScalars.lean`.
`openResMap_isIso` transports the existing scalar pullback comparison through
the constant-ring coordinate equivalences, pastes inverse mates, and uses the
proved ordinary open scalar mate. `exchange_restrictScalars_component` compares
the adjuncts of the actual inverse exchanges, using identity-on-sections
normalized direct-image compositors and open-unit compatibility.

Added proved private coordinate and compositor helpers. Reused private generic
mate lemmas through proof-only imports of
`Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport` and
`Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare`. Updated the two existing
nodes to describe the proofs and their actual dependencies. Public statements,
data definitions, adjunction normalizations, and the unit route are unchanged.
The existing complex and coefficient-coherence proofs are retained. The private
sequence_iso helper now takes explicit forward/inverse component maps and their
inverse equations. The two tower proofs use this API, preserving the same tower
construction while avoiding repeated reduction of dependent mapIso records.
Local proof-elaboration commands are recorded in
`coord/changes/FiniteOpenExchangeScalarsCompletedProofCommands.md`.

## Proved and sorry left

Closed 2 original holes, with prefix
`AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars`:

- `openResMap_isIso` (node `lem-cbc-finite-open-exchange-scalars`).
- `exchange_restrictScalars_component`
  (node `lem-cbc-finite-open-exchange-scalars-component`).

Added 0 holes. Split off 0 statements. The delivered module has 0 `sorry`.
All added private helpers are fully proved. The final lcompile.py --all run
compiled the complete module and generated its artifacts without warnings in
51.8 seconds. The argument does not assume a
nonempty open or a nonzero coefficient ring; finite ring assumptions and all
other original binders are retained.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`

Their requisite declarations are already available through the retained imports.
No module is withdrawn and no declaration is removed. In particular these are
redundant direct import removals, not claims that their source modules can be
removed from the whole library. The proposed fresh summand-by-summand proof of
openResMap invertibility is unnecessary: the existing constant-coordinate and
ordinary scalar-mate proofs supply it. The component proof no longer directly
uses the planned profinite-coefficient inverse-image or extension-presheaf
construction nodes; the normalized pullback, module-compositor, open-adjunction,
and finite-exchange constructions remain in use.

## Where the brief, the DAG or earlier work was wrong

No original statement is changed or disputed. The existing ordinary restriction
composition theorem has coefficients in Type u, whereas this module needs
Type (u + 1). Its generic mateSquare and pasteTransport lemmas are reusable, so a
proved private compositor helper supplies the required universe without changing
that module's interface. The old main-node proof_deps listed only the component
node despite the other proof steps; the updated list is the union of actual step
dependencies. The first delivery compile exceeded 60 seconds although a full diagnostic compile
had passed in 53.8 seconds. Profiling identified the dependent mapIso projections
in the tower proofs as a major kernel-checking cost; the existing private
sequence-construction API was changed to accept the explicit maps instead. No
file or theorem was split, and no public data definition changed. No new node or
unsupported assertion is needed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
