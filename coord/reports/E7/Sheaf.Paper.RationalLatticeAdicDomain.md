## What changed

Proved all four theorems of `Sheaf.Paper.RationalLatticeAdicDomain`, preserving every
public declaration signature and public import. The geometric base uses finite-type
Noetherian ascent, the existing finite-dimension bound and coefficient-prime stalk units.
The integral comparison applies `integralStratifiedPerfectDetailed`, after detecting the
global unit on stalks. The reduction Tor theorem applies the already proved
`integral_residue_tor`, with residue-field inverses obtained from those stalk units.
The final theorem extracts the common residue interval and constructs representatives
using the equivalence induced by restriction along the canonical coefficient isomorphism.
The two private helpers prove its inverse laws on sections. PBC constructibility is
transported along the representative isomorphism using the existing isomorphism closure.

The node now records this shorter proof. No definitions or statements were repaired.
The unit route is unchanged: this item supports the rational-stage lattice assertion.
Empty schemes, zero objects and torsion representatives require no extra hypotheses;
the ordered common interval already belongs to the detailed integral predicate.

Validation: the completed module compiled through `lcompile.py`; final import-pruned
compilation and the delivery preflight are run with this packet.

## Proved and sorry left

Closed four original holes, all attached to `lem-pur-rational-lattice-adic-domain`:

- `WeilConjectures.rational_lattice_adic_base`.
- `WeilConjectures.rational_lattice_integral_comparison`.
- `WeilConjectures.rational_lattice_reduction_tor`.
- `WeilConjectures.rational_lattice_adic_domain`.

Zero holes remain in the item; zero holes are added or split off. Existing imported
theorems retain their proof obligations, in particular `integralStratifiedPerfectDetailed`.
This delivery proves the item from those existing declarations, as stage 3 requires.

## No longer needed

Removed unused private proof imports:

- `Mathlib.AlgebraicGeometry.Noetherian` (available through the used source-library API).
- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.ProEtaleResidueTorTest`.

The node no longer directly uses `def-weil-pbc-adic-coefficient-datum`,
`def-weil-integral-derived-reduction`, `lem-pur-derived-change-of-rings`,
`lem-weil-l-adic-extension-integers-dvr`, or `lem-sf-proetale-residue-tor-test`
as proof dependencies. Their tensor-normalization and residue-test work is already
encapsulated by `lem-coef-integral-residue-tor`; these remain available transitively,
so no claim is made that their modules leave the targets' closure. Removed the obsolete
direct residue-test entry from `tool_uses`, retaining the existing integral-comparison
approval. No module is withdrawn. Public statement imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

The planned explicit K-flat and Artinian-residue argument was unnecessary here:
`Sheaf.Paper.IntegralResidueTor` already proves exactly the required uniform-interval
result, and its import passes the import-direction check. The original final proof plan
also left coefficient transport's essential surjectivity implicit. The delivery supplies
proved inverse restriction isomorphisms and uses the existing induced derived equivalence.
No mathematical statement was found false and no target statement changes.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
