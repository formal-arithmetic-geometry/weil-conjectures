## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility
(coord/retire-items.tsv row 2900). The current module already has zero holes. It is
withdrawn through deleted.txt, and its node is attached to the existing, unchanged
AlgebraicGeometry.Etale.strictLocal_exchange_compatibility in
WeilConjectures.AlgebraicGeometry.StrictLocalExchangeCompatibility.

The adopted theorem uses the full affine-neighbourhood colimit. The withdrawn
theorem uses the small representative ring colimit. These are canonically
isomorphic but not definitionally equal. Both consumers therefore retain their
original small-model signatures and definitions and derive their formulas directly
from the general representative APIs. No replacement public theorem or module is
introduced.

In Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization, replaced the specialized
application by the complete affine-germ colimit calculation. On each representative,
exchange_pointed_representative computes exchange; unitSectionRestriction_comp
computes restriction; the two small-model leg projections, hpoint, hqt and hq
identify the graphs by pullback hom-ext. The existing he₀ formula and associativity
close the equality. Added the explicit private GeometricFibreExchangeRepresentative
import and removed the private import of the retired module.

In Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization, proved hc′
by the same calculation. The existing remaining argument then gives the formula
for all pointed neighbourhoods by cancelling the source isomorphism and d.hom.
Removed the retired private import and the now unused private transportedIso_hom
and local he. All public signatures, public imports and definition bodies in both
consumers are unchanged. Their node proofs and dependencies record this route.

The retired node's statement_change records the full/small presentation difference
and audits both parent citers. The adopted source declaration, proof and imports
are unchanged. No blueprint unit statement or realized proof step changes.

Both adapted consumers compiled cleanly through lcompile.py (16.7 and 17.7 seconds
in the final proof run before removal of the unused helper). The delivery tool
performs the final compile and axiom checks on the actual packet. Source comparison
found no changed public signatures or definition bodies and no added holes.

Change record: coord/changes/D3-strict-local-exchange-compatibility-retirement.md.
It contains both exact signatures and the census of 840 transitive consumers.

## Proved and sorry left

The item had 0 sorry holes. Closed 0; added 0; split off 0; remaining 0.
The two adapted consumer modules also had and retain 0 holes.

The preserved adopted theorem is
AlgebraicGeometry.Etale.strictLocal_exchange_compatibility
(lem-weil-pbc-strict-local-exchange-compatibility). The complete consumer proofs are
AlgebraicGeometry.Etale.qcqs_geometricExchange_factorization
(lem-weil-pbc-qcqs-geometric-exchange-factorization) and
AlgebraicGeometry.Etale.strictHenselizationModuleFibre_factorization
(lem-sbc-strict-henselization-module-fibre-factorization).
There is no declaration left with sorry in this delivery and no new assumption.
This is a duplicate-module retirement, not a net hole closure or decomposition.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility and both private
imports of that module. Both consumer nodes no longer need
lem-weil-pbc-strict-local-exchange-compatibility as a proof dependency: their proofs
now use the already declared affine-germ and unit-composition facts directly.

The retired module's unused private module_inverseImage_stalk_germ disappears with
it. The fibre-factorization consumer's transportedIso_hom helper and local he are
also unnecessary after proving hc′ directly.

No other dependency module is claimed pruned. In particular, the adopted source
StrictLocalExchangeCompatibility still uses the adopted StrictLocalSectionPullback;
both declarations and their dependencies remain. The general unit restriction and
small limit-leg modules remain needed by the two consumers. No public import is
removed from either consumer or any adopted source file.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed module, but the live source is already
fully proved and coord/retire-items.tsv explicitly lists this duplicate for
retirement. The actual baseline is 0 holes, not an unfinished compatibility proof.

The adopted twin's signature cannot be substituted verbatim for the old one:
strictLocalization/strictHenselizationAffineCone/strictLocalizationToBase and
IsQcqsStrictLocalModuleComparison differ from the small representative scheme,
cone, structural map and expanded germ hypothesis. The node attachment is updated
to the exact adopted signature, and the statement_change makes the presentation
change explicit. Both original small-model parent statements remain proved in this
packet, so no parent conclusion is weakened or dropped.

Read the source's theorem-higher-direct-images (Tag 03Q9) and
lemma-proper-base-change-f-star (Tag 0A3U), the adopted and old theorem proofs, the
declared proof dependencies, both parent nodes, and their unit records. The only
DAG citers of the retired specialization are the two adapted consumers. The
initiality, colimit hom-ext, unit composition and pullback uniqueness arguments
require neither nonempty schemes nor a nonzero coefficient ring; all original
edge cases and hypotheses are retained.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
