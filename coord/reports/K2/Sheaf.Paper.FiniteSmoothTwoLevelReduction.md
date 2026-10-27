## What changed

Restored and reduced `Sheaf.Paper.FiniteSmoothTwoLevelReduction` from its preserved
quarantine source (the shared checkout restored the same source during this work).
The original theorem statement and public import are unchanged. Its proof now
assembles all ten fields of `ReductionData`, with the original canonical arrows.

Added four supporting modules. `QuotientIntrinsicCtf` proves scalar preservation of
the intrinsic constructibility/Tor predicate on arbitrary schemes.
`QuotientInverseOrientation` specializes the existing proved
`normalizedOrientation_scalar` theorem; the two geometry witnesses are propositions
and therefore proof irrelevant. `FiniteProCoefficientCounitTransport` proves the
formal counit calculation through the actual origin and compact site comparisons.
Only `QuotientRootLineComparison` remains an obligation. It constructs the normalized
root/sheaf/derived line comparison, without asserting any smooth purity property.

The private proved helpers are accessed by proof-only `import all` imports. No
existing shared definition, interface or consumer was changed. No change record
or forced adaptation is required. The DAG now follows the actual Lean proof.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothTwoLevelReduction`
(node `lem-pur-finite-smooth-two-level-reduction`); the item itself has zero holes.
This is a decomposition: one original hole is replaced by one strictly smaller
root-line obligation, so it is not claimed as a net decrease of holes.

The following new theorems have complete proofs, with no added holes:

- `AlgebraicGeometry.Etale.FiniteSmoothPurity.quotientIntrinsicCtf`
  (`lem-pur-quotient-intrinsic-ctf`).
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.quotientInverseOrientation`
  (`lem-pur-quotient-inverse-orientation`).
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteProCoefficientCounitTransport`
  (`lem-pur-finite-pro-coefficient-counit-transport`).

The only added `sorry`, the entire proof of a public theorem, is
`AlgebraicGeometry.Etale.FiniteSmoothPurity.quotientRootLineComparison`
(`lem-pur-quotient-root-line-comparison`). Its docstring gives the construction and
proof, including equal levels and empty schemes. Its kernel inclusion, scalar/root
generators and derived normalization determine its data; it is not an arbitrary
witness of existence.

The arbitrary-scheme constructibility proof first compiled in 5.8 seconds, the
original full assembly in 11.8 seconds, and the complete counit calculation in
12.5 seconds. All five final modules compiled together. Delivery validation is through
`deliver3.py`, including its timing and packet checks.
The counit theorem explicitly records both the finite-Tor source locus and the
bounded-below target exceptional origin needed by the total compact site maps.
The assembly supplies these from ordinary smooth exceptional-domain preservation.

## No longer needed

No original import was removed: the item originally imported only its statement
module. No module is withdrawn, and no `WeilConjectures` declaration is changed.
New modules publicly import only their statement dependencies.

Removed the direct proof dependency on `lem-pur-finite-smooth-quotient-coherence`
(`Sheaf.Paper.FiniteSmoothQuotientCoherence`). Two-level counit and naturality
calculations require no triple-level associator/cocycle. Other parents, including
the general-base system assembly, still need that module; it is not globally pruned.

Replaced the direct dependency on `lem-pur-finite-reduction-constructibility`
(`Sheaf.Paper.FiniteReductionConstructibility`) with the proved intrinsic scalar
realization calculation, which covers arbitrary test schemes. The existing module
remains imported by other coefficient APIs. `det-sp-scalar-extension-functor`
remains needed through `det-sp-reduction-direct-image` and is not globally pruned.

The four old direct geometry dependencies are replaced by the existing proved
`lem-sp-finite-normalized-orientation-scalar` and its declared proof route:
`lem-pur-diagonal-orientation-compatibility`,
`lem-asd-ordinary-finite-p1-adjunction`, `lem-amb-affine-space-top-trace`, and
`def-amb-vector-integration`. Their declarations are preserved.
`lem-asd-etale-finite-twist-pullback` is retained in the root-line node for local
rank-one models. `lem-weil-pbc-comparison-pullback`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-comparison-direct-image-canonical-mate`, and
`lem-cbc-proetale-extension-zero-comparison` remain constituents of the unchanged
canonical maps and the reused origin/site transport APIs. Their modules are not
withdrawn. `lem-pur-exceptional-coefficient-comparison` remains a direct dependency.

## Where the brief, the DAG or earlier work was wrong

The older plan obtains a compact-support cocycle from triple-level coherence
before using a two-level mate. The actual mate is an adjunction transpose; its
ordinary counit equation is immediate, and naturality comes from the existing
compact coefficient natural transformation. The pro counit calculation follows
by naturality and comparison triangle identities on the stated bounded-below loci.

The ordinary/pro tensor calculations and arbitrary-scheme scalar transport APIs
already have proved private helpers. A targeted project search also found the
proved divisible-exponent `normalizedOrientation_scalar`; unlike the older
finite-field/common-exponent orientation theorem, it fits this item directly.
No new geometric orientation obligation is needed.

The blueprint ancestor utility returns no ancestor for the original item's
current target-chain metadata. The new nodes name its recorded unit
`sk-thm-purity-transport`, Step 1 (finite reductions), and the current
`sk-lem-sp-reduction` proof. The unit's realized statement and steps are unchanged.

## New nodes

`lem-pur-quotient-root-line-comparison` constructs only the normalized root/sheaf/
derived line comparison. Its equations determine the data, and its proof uses
etale local primitive-root coordinates. This is the sole remaining hole.

`lem-pur-quotient-inverse-orientation` records the proved specialization of
`normalizedOrientation_scalar` to the two quotient levels. It asserts only the
coefficient-unit equation, without arbitrary inputs or pro-etale transport.

`lem-pur-quotient-intrinsic-ctf` records the proved intrinsic scalar-realization
bridge to the ordered fixed-module `IsCtf` predicate on arbitrary schemes.

`lem-pur-finite-pro-coefficient-counit-transport` records the proved counit transport
through comparison adjunctions and proper/open compact site maps. It assumes no
smoothness, orientation or exceptional-map invertibility, and asserts no purity.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
