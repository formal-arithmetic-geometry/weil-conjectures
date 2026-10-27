## What changed

Filled `AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_restriction` in
`Sheaf.AlgebraicGeometry.SemilinearAlphaRestriction`, preserving its signature and docstring.
Added proved private helpers for beta restriction, the clopen projector restriction,
open-composition restriction, section-factor restriction with equality transport, and
factorization of the inverse-image square. The proof expands the specified
beta-projector-compositor word and cancels its
intermediate open units by naturality. The naturality calculation is proved first for
arbitrary functors, then applied to an arbitrary clopen factorization, and finally to
the canonical fibre product. These proved private abstractions keep the concrete
fibre-product and adjoint constructions out of the algebraic calculation.

The proof-only import of `Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence` uses
`import all` to access its already proved ordinary inverse-image associativity calculation,
`ordinary_coherence`. Its node is in the same unit. This is used for the two three-map
composition identities; no derived alpha or alpha-pullback compatibility is assumed.
The item's node now records these actual steps and this dependency. No shared interface,
definition, public import or consumer was changed.

Local and service searches found the generic Mathlib adjunction-composition and
unit-conjugation identities, but no existing complete semilinear alpha restriction theorem.
The proof follows the existing plan without another split.

Validation: `lcompile.py --all` compiled the completed item and its unchanged direct
importer `Sheaf.AlgebraicGeometry.SemilinearAlphaPullback`. The temporary consumer copy
and debugging options were then removed. The final delivery runs its own clean compilation
and axiom checks.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_restriction`
(node `lem-sf-semilinear-alpha-restriction`).

There are zero remaining holes in this module, zero holes added elsewhere, and zero
split-off statements. All private helpers have complete proofs.

## No longer needed

None. No imports were removed and no original declared dependency was pruned.
`def-sp-varying-ring-operations`, `def-sp-varying-ring-proper-open-arrows` and
`def-cbc-strict-tower-proper-open-arrows` remain used. The additional proved dependency is
`lem-sf-semilinear-compositor-coherence`.

## Where the brief, the DAG or earlier work was wrong

No statement or mathematical correction was needed. The former prose plan did not name the
already proved ordinary compositor-coherence calculation needed to assemble the factored
square; the updated proof dependencies record it explicitly.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
