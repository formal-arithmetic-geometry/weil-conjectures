## What changed

Completed the denominator-clearing reduction in
`Sheaf.RingTheory.Derivation.DetectNonPthPower`. The private proved helper
`Derivation.clear_denominators` clears a common denominator on finite algebra
 generators and extends integrality to their algebra by `Algebra.adjoin_induction`.
The proof of `Derivation.exists_domain_derivation_of_fraction_derivation` then
constructs the domain-valued derivation and proves nonvanishing by fraction-field
injectivity. Every existing declaration signature and visibility is unchanged.

Added the proof-only import
`Sheaf.RingTheory.Derivation.FiniteCoefficientPreparation`, with one new public
intermediate theorem. This isolates normalization and the relative-differential
argument, before any denominator clearing or construction of a domain derivation.
Updated the domain node to record this reduction.

Replaced the fraction-field theorem's differential-to-derivation helper application
with Mathlib dual separation, `LinearMap.compDer`, and restriction of scalars.
Replaced its proof-only helper import with `Mathlib.LinearAlgebra.Dual.Lemmas` and
updated its node. Added `Mathlib.RingTheory.Localization.Integer` for common
 denominators. No public imports, definitions, or target statements changed.

Both delivery modules compile cleanly against the shared library. The earlier
attempt's unrelated dependency copies were moved outside the delivery's `lean/`
tree; no existing dependency module is adapted or delivered.

## Proved and sorry left

Closed the item's one remaining hole:
`Derivation.exists_domain_derivation_of_fraction_derivation`
(node `lem-weil-pbc-domain-derivation-from-fraction`). Its proof is complete from
coefficient preparation; the denominator-clearing, derivation construction, and
nonvanishing steps have no holes.

Added one hole:
`Derivation.exists_finite_coefficient_derivation`
(node `lem-weil-pbc-finite-coefficient-detecting-derivation`), in the new module
`Sheaf.RingTheory.Derivation.FiniteCoefficientPreparation`. Its entire proof is
`by sorry`; its docstring and node give the normalization, coefficient-subfield,
and relative-differential argument. This is a decomposition (one hole closed,
one added), not an unconditional proof of the detection theorem.

The already proved `Derivation.exists_fraction_field_derivation_of_not_pth_power`
and `Derivation.exists_apply_ne_zero_of_not_pth_power` remain proved. No sorry is
left in the item's module. No sorry is added in a definition or private helper.

## No longer needed

Removed the proof-only import
`Sheaf.RingTheory.Derivation.NonzeroDifferentialToDerivation` and the fraction-field
node's edge to `lem-weil-pbc-nonzero-differential-to-derivation`. Its two-line
conversion is performed directly using Mathlib dual separation and the universal
 derivation. That module and node are not needed by this item's proof; other
users may still need them.

The normalization, p-basis, power-series subfield, and subfield-intersection nodes
remain needed in coefficient preparation; none of them is claimed pruned. No
unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original denominator-clearing docstring suppresses an essential condition:
one cannot bound the denominators of an arbitrary absolute derivation using a
finite set of algebra generators unless it vanishes on the coefficient subring.
The supplied fraction-field derivation need not vanish on the original complete
local base. The new intermediate theorem selects a different detecting derivation
that does vanish on a suitable coefficient subring. Thus this delivery does not
claim that an arbitrary multiple of the supplied derivation preserves B.

The earlier sandbox report described a different, absent integral-values lemma
and contained two purported second readings. It has been replaced. The actual
remaining statement is coefficient preparation, and the independent reader's
section is left for that reader.

The new statement was checked on the finite-field case (the detection hypothesis
is impossible), f=0 and pth powers (also impossible), a polynomial ring over an
imperfect field (pth-power coefficient subring suffices), and a power-series ring
over an imperfect field (a finite-index coefficient subfield and pth-power
variables are required). The source argument applies to f as an element of M;
normalization supplies a finite fraction-field extension even when f is not in
its finite intermediate algebra. B remains finite type over the embedded
polynomial ring, and hence over its finite coefficient subring. The proved
common-denominator helper also covers an empty generator set: the derivation
then vanishes on B.

## New nodes

`lem-weil-pbc-finite-coefficient-detecting-derivation`, in
`dag/nodes/sec-proper-base-change/`, states the coefficient preparation from Stacks
Tag 07PH (`lemma-find-D`). It is strictly the preparation part of the original
argument: it gives a fraction-field derivation and a coefficient subring, leaving
common-denominator integrality and the domain-valued derivation construction to
the complete Lean proof in the parent. Its module is
`Sheaf.RingTheory.Derivation.FiniteCoefficientPreparation`. The node records the
existing normalization and differential dependencies and the searches performed.
LeanSearch returned a service error (recorded as unavailable); Loogle returned
no result; LeanFinder returned unrelated differential-extension results in
characteristic zero; source grep located the common-denominator Mathlib theorem
used in the parent but no coefficient-preparation theorem. No change record is
needed: there is no modification to an existing interface.

## Second reading by M3

1. Compared the delivered `DetectNonPthPower.lean` with the repository version. Existing declaration signatures and visibility are unchanged; the item changes are proofs and proof-only imports. The new coefficient-preparation module has one deliberately split public statement with its matching node.
2. Compiled both sandbox modules with `lcompile.py --all`. The denominator-clearing proof has no `sorry`; the only remaining `sorry` is the named coefficient-preparation theorem. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was introduced.
3. Checked the split statement against its source and edge cases recorded above. It is a strict reduction: it supplies a coefficient subring and fraction-field derivation while leaving denominator clearing to the parent theorem. It is not a restatement of the parent target, and the node records its proof dependencies and source.
4. Checked pruning and the route. The old nonzero-differential conversion import is removed; Mathlib dual separation and `compDer` provide that conversion directly. The unit route is preserved through coefficient preparation and denominator clearing, and the updated node proof and `proof_deps` follow the Lean proof.
5. Checked the new node and module metadata: the node has the required statement, source, proof steps, searches, Lean declaration record, chapter, and unit. No target statement or definition was changed.

Changed only the report after this reading; no proof or interface edits were needed.
