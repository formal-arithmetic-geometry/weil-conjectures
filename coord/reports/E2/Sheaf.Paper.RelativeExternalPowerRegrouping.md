## What changed

Proved `WeilConjectures.RelativeExternalPower.relative_external_power_regrouping`
without changing its signature or the existing definitions. Private proved helpers handle
isomorphism transport, pullback preservation, binary tensor preservation, the tensor-prefix
induction, geometric permanence, and the coordinate structure-map identities. The main
proof applies these helpers to the actual projections, and then establishes both next-factor
pullback domains. The already constructed canonical `regroup` is unchanged.

Updated the node proof and dependencies to describe the K-flat comparison used to apply
`finiteCoefficient_tensor_ctf` to the native tensor. No source-library file changes. Added private proof imports for
`KFlatResolutionGeneral` and `ProEtaleBoundedConstructibleTriangulated`; the original
pullback and tensor preservation imports are now used directly. The extra dependencies
are generic resolution and isomorphism-closure tools, not alternate purity arguments.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.RelativeExternalPower.relative_external_power_regrouping`
(node `lem-pur-relative-external-power-regrouping`). Added zero holes. No `sorry` remains
in the item, and no new module or unfinished theorem is introduced. The result still uses
the published preservation and comparison theorems and inherits their existing dependencies.

## No longer needed

Removed the private import `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
The fixed left association uses only the native tensor bifunctor, already provided by
`Sheaf.Algebra.Homology.RingedDerivedTensorNative`; no closed adjunction or reassociation is
used. Removed `lem-sf-ringed-derived-closed-symmetric-monoidal` from the node's proof edges
and its obsolete tool approval. This is local pruning, with no claim that other consumers
of that module disappear. All other original mathematical dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original plan's reference to associators is
unnecessary with its specified left association. Binary preservation is stated on cochain
representatives, so applying it to the native tensor requires the explicit one-K-flat
comparison and isomorphism transport supplied by the private helper. Boundary cases:
`j=0` uses the identity projection and a single tensor factor; `r=1` has no next-factor
assertion; empty schemes are allowed throughout. No target signature, coefficient ring,
finite-Tor predicate, or chosen geometric product is changed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
