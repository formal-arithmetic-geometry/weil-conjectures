## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.nonempty_normalizedProjectiveLineAdjunction` with a
complete coefficient-transport argument. Its signature and public imports stay
unchanged. The proof extracts a positive invertible annihilator, pulls its
invertibility to the specified projective line, applies the existing
`exists_arbitraryBaseFiniteP1Integrals`, invokes the finite diagonal-kernel
assembly, and transports its right adjoint through the comparison of the concrete
finite-root line with the normalized abstract Tate object. The final natural
isomorphism is explicitly obtained by mapping the inverse coefficient isomorphism
through derivedTensor.flip, whiskering with shiftFunctor(2), and whiskering with
Lq^*. Adjunction.ofNatIsoRight performs the transport.

Added two proof imports and their new modules:
`Sheaf.SmoothPurity.NormalizedTateLineComparison` and
`Sheaf.SmoothPurity.FiniteP1AdjunctionOfIntegrals`. Updated the item's node to match
this proof and added nodes for the two outstanding geometric steps. No existing
statement, definition, consumer, unit route, or source-library declaration changes.

## Proved and sorry left

Closed the item's one textual hole:
`AlgebraicGeometry.Etale.nonempty_normalizedProjectiveLineAdjunction`
(`lem-normalized-projective-line-adjunction`). Its proof combines the following
strictly separate obligations; this delivery is a decomposition, not a full proof
of projective-line duality.

Added two holes, one named theorem per new module:

- `AlgebraicGeometry.Etale.nonempty_normalizedTateLineComparison`
  (`lem-sp-normalized-tate-line-comparison`): compare only the degree-one derived
  object with the finite root-of-unity line. It asserts no adjunction or trace.
- `AlgebraicGeometry.Etale.nonempty_finiteP1AdjunctionOfIntegrals`
  (`lem-sp-finite-p1-adjunction-of-integrals`): assemble the concrete finite-line
  adjunction from supplied splitting, base-change and diagonal-integral identities.
  It has no normalized abstract Tate datum and does not assert the existence of
  the splitting or the integral identities supplied as hypotheses.

The item has zero sorry left. The delivery adds two sorry statements; the net
textual reduction is minus one hole (one closed, two added). Existing imported
obligations are not counted as holes closed by this delivery.

Validation: lcompile.py --all completed with exit code 0 and no diagnostics.
FiniteP1AdjunctionOfIntegrals compiled in 43.4 seconds,
NormalizedTateLineComparison in 30.5 seconds, and the unchanged-signature item in
35.9 seconds. Each file is below the 60-second limit.

## No longer needed

No existing imports were removed: both original public imports supply names in
the unchanged signature. No modules are withdrawn.

The item no longer directly invokes `thm-amb-p1-adjunction`
(`Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction`), whose concrete-line
interface assumes a Noetherian base, or `lem-amb-p1-diagonal-integrals`
(`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals`), which has the same
restriction. The arbitrary-base splitting/integrals theorem is used instead.
These older nodes and modules are not globally pruned: the finite integral
module still imports the diagonal data, and the coefficient-comparison plan can
use the Noetherian concrete-line theorem in its local calculation.

`def-weil-pbc-composite-adjunction` is no longer a direct dependency of the item:
its proof transports a single adjunction instead of composing adjunctions. The
new finite-kernel assembly still uses the ordinary adjunction/unit/counit API.
`def-kun-derived-tensor` is retained: its functor action supplies the explicit
coefficient transport. No claim is made that any target-closure module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original dependencies do not directly imply the stated arbitrary-base,
normalized-datum result by application: ProjectiveLineFullAdjunction and
ProjectiveLineDiagonalIntegrals assume IsNoetherian and use a concrete finite
root-of-unity twist, while the item has neither that base restriction nor a
chosen concrete twist. The missing comparisons cannot be supplied by treating
the two twist models as definitionally equal. The actual existing arbitrary-base
integral theorem supplies the required geometric input without changing the base.

The normalization comparison is isolated from kernel assembly; the former is an
object isomorphism and the latter is conditional on already supplied geometric
identities, so neither is the original obligation under a new name. The source
for the comparison is the item's existing proof step 1, refined using the
normalized Kummer boundary and normal generic-point descent. The source for the
assembly is the displayed unit and two triangle computations in the latest
blueprint thm-amb-p1-adjunction.proof.md. All proofs in words are agent-written.

Edge cases checked: the coefficient ring can be zero, including N=1; no
nontriviality premise is added. The base and its projective line can be empty.
The comparison at X uses only the selected N being invertible at X; it does not
silently substitute a different annihilator. Finite commutative rings need not
be fields or free modules over Z/N. Both derived variables remain unbounded.
The coordinate type is exactly Option (ULift (Fin 1)). All shifts are two, so
moving a shifted line past itself introduces no sign. The finite assembly is
conditional on both integral equations, not just an equality of cohomology
classes or stalkwise detection of arbitrary derived morphisms.

The unit record sk-prop-sf-cbc has empty realized.statement and realized.steps;
no unit record or chapter route is changed. No definition or statement repair
record is needed, since existing signatures and definitions are unchanged.

## New nodes

`lem-sp-normalized-tate-line-comparison`, in
`dag/nodes/sec-smooth-purity/lem-sp-normalized-tate-line-comparison.json`, owns
`Sheaf.SmoothPurity.NormalizedTateLineComparison`. The local rank-one normalized
boundary compares the lines over Q; full faithfulness for finite locally
constant sheaves over the normal universal base extends that isomorphism, then
pullback gives the arbitrary-base object comparison. This is independent of
projective-line kernel assembly. The docstring gives the zero-ring case and the
descent argument explicitly.

`lem-sp-finite-p1-adjunction-of-integrals`, in
`dag/nodes/sec-smooth-purity/lem-sp-finite-p1-adjunction-of-integrals.json`, owns
`Sheaf.SmoothPurity.FiniteP1AdjunctionOfIntegrals`. It takes concrete splitting,
base-change and diagonal identities as hypotheses, constructs the natural unit
and counit, contracts the two coordinates, and applies the triangle criterion.
It realizes the categorical assembly portion of the original source proof. The
specified Option coordinates are related to the existing splitting coordinates
by a projective-space coordinate isomorphism.

Searches included remote LeanSearch, LeanFinder, Loogle and Mathlib grep, plus
repository searches by HasTateTwist.IsNormalized, finiteEtaleTateLine, projective
adjunction and trace-contraction names. Whole-blueprint searches for normalized
Tate, diagonal kernel, Tate line and projective-line adjunction found no exact
arbitrary normalized-line comparison or conditional finite-integral assembly.
The existing affine-base trace adjunction does not cover arbitrary bases. The
existing Noetherian concrete-line adjunction does not cover either new interface.
No change records were added.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
