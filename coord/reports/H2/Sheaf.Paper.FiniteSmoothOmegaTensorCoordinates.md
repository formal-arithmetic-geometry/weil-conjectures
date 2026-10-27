## What changed

Completed `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothOmegaTensorCoordinates`
from the existing arbitrary-base étale unit-tensor normalization. The statement, definitions,
and public imports are unchanged. Added proof imports for that normalization and the existing
private graph-comparison and tensor-mate calculations. All edits are in the assigned module
and its own DAG node.

The proof first identifies the supplied normalized comparison with the canonical graph map:
monicity gives equality on sheaves, and localization extensionality gives equality on all
homotopy representatives. The selected compactification self-comparison is the identity.
Right-adjoint uniqueness then identifies the supplied coordinates with the canonical mate.
The exact-pullback tensor equation transports to left-derived pullback using tensor interchange
and unitor naturality. Finally, braiding naturality cancels the inverse unit orientation;
the braiding/unitor identity and cancellation of the right-adjoint isomorphism finish the proof.

Searches used Lean Finder for an adjunction tensor mate at the unit orientation, Loogle for
`rightAdjointUniq`, and Mathlib grep for the concrete tensor-map names, together with `rg`
through both project roots. The project normalization theorem gives the needed geometric
input; Mathlib supplies the adjunction, braiding and unitor identities.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothOmegaTensorCoordinates`
(node `lem-pur-finite-smooth-omega-tensor-coordinates`). Added no holes and no split-off
statements. The assigned module contains zero `sorry`s. The five new private helper theorems
are proved in full. Validation: `lcompile.py` compiled the complete module cleanly in 10.7 s,
with no errors or warnings; the original theorem statement and docstring were also compared
verbatim against the source.

## No longer needed

No imports removed and no modules withdrawn. The old proof-dependency edge to
`lem-pur-etale-support-map-compatibility` is removed: its existential projection family is
unnecessary because the existing arbitrary-base tensor normalization already computes the
canonical graph mate. Its module remains in the existing public statement-import chain.
The graph normalization, common-refinement identity, arbitrary-base tensor equation and
canonical tensor braiding are still needed.

## Where the brief, the DAG or earlier work was wrong

The old first step cited the existence theorem `etaleSupportMapCompatibility` while requiring
uniqueness for an arbitrary supplied comparison family. That uniqueness is now proved explicitly
from monicity and the homotopy normalization. The remaining transport is categorical and uses
existing proved private calculations; no further geometric obligation or statement repair was
needed. The argument includes empty sources and zero coefficients, since every cancellation is
by a specified isomorphism and imposes no nonemptiness assumption.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
