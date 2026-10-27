## What changed

Reduced constant_purity_frobenius_square to two independent coefficient-comparison
statements. The first is constant-unit coherence for an arbitrary morphism of
arithmetic models. The second identifies the two published common-stage pullback
square normalizations, for an arbitrary common-stage object. Neither statement
contains smooth purity, a compactification, or the conclusion of the item.

The proof uses the existing common-stage clause of
rational_weil_purity_naturality_mate. A proved private categorical helper identifies
the purity Frobenius conjugate with the specified inverse-exchange mate by the
counit equation and injectivity of the adjunction hom-equivalence. Another proved
private helper carries constant-unit coherence through the tensor bifunctor and
its natural pullback comparison. The existing beta component normalization
identifies the two compact-support exchanges. Its original component calculation
is factored into a proved private helper, reused by the existing uniqueness proof
and by the exchange equality; the public signatures stay unchanged.

Moved the seven constant-unit constructors, unchanged, to the new prerequisite
CommonConstantUnitFrobenius and publicly reexported it. This permits the unit-only
comparison to be a separate item without an import cycle. The constructors and
Square retain their statements and meanings; no data is chosen from a mere
existence theorem. The change record is
coord/changes/C4-constant-unit-proof-data.md. No other existing module is changed.

The profile identified about 15 seconds in the identity morphism's finite-type
instance search in systems. The returned System type is preserved; only that
proposition proof now uses the public Mathlib open-immersion implication
explicitly. See coord/changes/C4-systems-identity-instance.md. This change is
definitionally immaterial by proof irrelevance and needs no consumer adaptation.
The final packet hit the 60-second limit, so the same explicit identity proof
also replaces the corresponding search in Square and in the new theorem proof.
The change to Square is a single proposition-proof argument; its three identities
and every morphism are unchanged, and proof irrelevance gives definitional equality.
See coord/changes/C4-square-identity-instance.md.

## Proved and sorry left

Closed the original hole in
WeilConjectures.ConstantPurityFrobenius.constant_purity_frobenius_square by a
complete reduction. The item originally had one hole and now has zero textual
holes. This is a decomposition, not a net proof gain.

Added two holes, each the whole proof of a named public theorem:

- WeilConjectures.ConstantPurityFrobenius.commonUnit_frobenius,
  node lem-pur-common-constant-unit-frobenius.
- WeilConjectures.commonFrobeniusSquare_eq,
  node lem-pur-common-frobenius-square-normalization.

The final item compiled without warnings through lcompile.py. Both new modules
also compiled through lcompile.py; the final delivery check compiles the packet.

The seven moved constructors contain no holes. The existing beta construction,
its normalization proof, and exceptionalMate_isIso are preserved.

## No longer needed

The main proof uses the existing rational/common-stage naturality-and-mate theorem
instead of reconstructing its strict-data specialization. It therefore does not
separately use lem-pur-completed-unit-pullback-tower, def-pur-tate-datum,
thm-pur-weil-equivariance-of-purity-and-trace, def-pur-compact-support-transport,
or cor-pur-adic-and-rational-smooth-dualizing-complexes as proof dependencies.
The constant-ring composition and tower-substitution work belongs to the new
unit-only prerequisite. Existing statement dependencies and the unit route stay.
Removed the item's direct proof import of ConstantGeometricStalkUnit; its use is
now confined to the relocated constructors in CommonConstantUnitFrobenius.
No existing module is withdrawn and no global pruning is claimed: several of
these dependencies remain reachable through the existing rational-purity theorem.

## Where the brief, the DAG or earlier work was wrong

The initial compile saw a stale compiled interface for
RationalWeilPurity.rationalExchange and requested IsSeparated X₀.hom in
FrobeniusCompactRationalNormalization. Explicitly recompiling the unchanged
current RationalWeilPurityNaturalityMate source succeeded; no signature repair
was needed. Its temporary unchanged sandbox copy is excluded from the delivery.

The original proof plan implicitly identifies zlFrobeniusSquare with the
podCommonSquarePullbackComponent used in the statement. Their underlying
compositors are separately chosen by normalization theorems. The new normalization
statement makes this comparison explicit. The previously stated generalized
rational-purity naturality-and-mate theorem already supplies the geometric purity
and counit argument, so no new strict-data applicability result is necessary.

The two new statements were checked on identity morphisms, zero relative
dimension (which they do not assume), empty source or target, and arbitrary
finite-stage representatives. Neither introduces a stable-lattice hypothesis.

## New nodes

lem-pur-common-constant-unit-frobenius records the normalized constant-unit
Frobenius equation independently of every Tate and purity operation. Its proof
follows constant-section composition, whole-system realization, rationalization,
and common-stage inclusion. Its module also owns the verbatim moved constructors.

lem-pur-common-frobenius-square-normalization records equality of the actual
common-stage pullback-square components from their shared integral composition
normalization. It contains no coefficient-unit or purity assertion. The remaining
mate and tensor calculations are proved in the item, not left in either node.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
