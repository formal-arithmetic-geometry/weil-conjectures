## What changed

Restored the archived Sheaf.Paper.A1FiniteEtaleWeilFibreComparison source from the
quarantine path in coord/rework.tsv. All original declarations, signatures and imports
are retained. The timed-out definition is repaired by making the long canonical
base-change mate irreducible and caching the inherited finite-type/quasi-compact
instances for its finite fibre. The canonical map's literal construction is unchanged.
The new inherited instances are recorded in the existing node's Lean attachment.

The preliminary proofs use Mathlib's residue-point structure-map identity,
cardinality of a finite-dimensional vector space, algebraicity in a field tower,
pullback projection identities and the fibre homeomorphism. Closed-image preservation
uses that the fibre over a closed point is a closed immersion. The heart assertion uses
constructible_pullback_t_exact and the factorization of its heart functor through the
inclusion. A proved private categorical helper transports the object property.

Change record: coord/changes/F1-a1-finite-fibre-elaboration.md.
No consumer adaptation is necessary. The quarantined parent was read in full and
its unfinished proof does not unfold the now-irreducible mate. The blueprint unit
sk-thm-dl-a1-upper and the parent route remain unchanged.

## Proved and sorry left

The archive had 17 holes. Closed 9 original holes; added 0 holes and split off 0.

Proved:

- WeilConjectures.a1ResidueField_properties
- WeilConjectures.a1ResiduePoint_over
- WeilConjectures.a1ResidueInclusion_compatible
- WeilConjectures.a1ResidueStageCarrier_eq
- WeilConjectures.a1FiniteFibreProjection_over
- WeilConjectures.a1FiniteFibreSquare
- WeilConjectures.a1FiniteFibrePoint_over
- WeilConjectures.a1FiniteFibreClosedImage_mem
- WeilConjectures.a1FiniteFibreWeilComplex_mem

Remaining eight holes, all attached to node lem-a1-finite-etale-weil-fibre-comparison:

- WeilConjectures.a1ResidueInclusion_return
- WeilConjectures.a1ResidueStageComparison
- WeilConjectures.a1FiniteFibreLocalReturn
- WeilConjectures.a1FiniteFibreLocalFrobenius
- WeilConjectures.a1FiniteEtaleWeilImage_mem
- WeilConjectures.a1FiniteFibreStageCoordinates
- WeilConjectures.a1FiniteFibreLinearComparison
- WeilConjectures.a1FiniteEtaleWeilFibreComparison

The two added inherited-geometry instances have complete proofs. This is a timeout
repair with additional preliminary proofs; the remaining comparison and equivariance
assertions are not claimed as proved.

## No longer needed

None. No import, node, module or declaration is withdrawn. The remaining named
assertions still need the original planned dependencies. In particular zero current
live importers is caused by quarantine and does not authorize pruning this item or
its archived parent.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it is quarantined, not withdrawn. Its archive
and DAG attachment are preserved. The archived module compiled cleanly in 42.8 s;
the baseline profile reported 24.1 s in instance inference. The revised data-definition
and instance setup reduced an intermediate compile to 28.2 s (that intermediate still
had a fibre-square proof error). The local irreducibility of the chosen pullback and
t-structure reduced the next compile to 31.3 s; that run exposed a subsingleton-instance
mismatch, which is now identified explicitly. The final complete module compiled through
lcompile.py in 58.2 s with exit code 0 and no warnings. The assigned timeout repair is
implemented by inherited-instance caching, keeping the canonical mate irreducible, and
local opacity for chosen categorical constructions. Every original signature and the
literal mate body were compared against the archive and are unchanged.

Searches ran through msearch.py: Lean Finder for residue-point composition returned
the scheme residue-field functoriality identities; Loogle for IsAlgClosure and
IsScalarTower returned the closure tower API; Mathlib grep located
Module.natCard_eq_pow_finrank. Direct source search found the already-proved
closedPoint_iff_residueField_trdeg_zero_and_finite and the pullback t-exactness interface.
No new mathematical statement or alternate unit route was introduced.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
