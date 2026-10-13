## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_divisor_charts`
from the stalk-normalization generic comparison, regular-divisor root-model normality,
normal dense-open normalization, smooth regularity ascent, and one new punctured Kummer
chart input that retains a specified equation. All added imports in the existing module
are proof-only. Existing signatures and public imports are unchanged.

The proof constructs the affine structural ring map explicitly, proves regularity of its
uniformizer quotient by residue-field base change, proves closed-fibre prime membership,
constructs the full finite normal root model and its dense punctured open, and proves the
normalization comparisons and their projection equalities. Private proved helpers retain
compatibilities that existing public interfaces omit; their arguments follow the already
proved helpers in SmoothTraitAffineGenericOpen and TraitGenericNormalizationCharts.
Both delivered modules compile cleanly through lcompile.py in import order.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_divisor_charts`
(node `lem-sbc-stalk-normalization-trait-divisor-charts`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_prescribed_punctured_root_chart`
(node `lem-sbc-regular-divisor-prescribed-punctured-root-chart`), in the new module
`Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart`.
Its entire proof is `by sorry`. This is a decomposition, not a net hole-count reduction:
one hole closed and one hole added. The new input concerns only the punctured cover on a
regular principal divisor, and does not include trait localization, a section, normality
of the full root model, relative normalization, or normalization-base-change assembly.
There are no other new holes and no data definitions with postponed proofs.

## No longer needed

No existing imports were removed; the original node had no proof-dependency imports.
The route does not need the unspecified-equation interfaces in
`StalkNormalizationTraitCharts`, `TraitGenericNormalizationCharts`,
`TraitGenericRootModel`, `TraitGenericPuncturedRootChart`, or
`RegularDivisorGaloisPuncturedRootChart`; these are candidates examined, not modules
newly disconnected from the targets by this delivery. No global pruning is claimed.
The unit's tame-chart and normalization route is retained. Its realized statement
and step arrays are empty in the repository; this delivery leaves that record unchanged.

## Where the brief, the DAG or earlier work was wrong

The item's original node had a single long step with no proof dependencies. Its plan is
now assembled in Lean and its dependencies recorded. The available
`regular_divisor_punctured_root_chart` allows an arbitrary output g and says nothing
relating g to the input f. It cannot yield the required rho(varpi) equation. The new
input records precisely this missing compatibility, at a point on the divisor. The
strict-henselization and descent paragraphs of Stacks 0EYG use the specified f itself.
Source read: https://stacks.math.columbia.edu/tag/0EYG (lemma-abhyankar-one-divisor),
https://stacks.math.columbia.edu/tag/0EYH, and
https://stacks.math.columbia.edu/tag/09EB (lemma-galois-conclusion).

The existing `smooth_trait_affine_generic_open` existentially gives an algebra structure
and smoothness, but omits equality of its Spec map with the structural morphism. The
private proved construction retains that equality rather than changing the interface.
Generic-section equations hsq and hsj are unused, as intended by the original docstring;
the actual section and its identity are used to locate the point on the closed fibre.

`lem-weil-pbc-regular-ring-smooth-ascent` is used as a generic tool from another unit:
it is the existing ring-theoretic smooth regularity theorem, not a replacement of the
spreading unit's route. Blueprint searches for equation and Kummer found no node giving
this prescribed-equation punctured chart. The ancestor tool returned None for the
module-valued created.item, so the new node uses the explicit ancestor already recorded
on the item's blueprint.from, sbc-thm-spreading-finite-etale-galois.

## New nodes

`lem-sbc-regular-divisor-prescribed-punctured-root-chart` states the prescribed-equation
Kummer input, with its self-contained statement, source, proof in words, search records,
and new module. The input point must contain f. This rules out unit f and the zero ring;
empty torsors use m=0, disconnected torsors use stabilizer groups, and arbitrary residue
characteristic is allowed because the group order is a unit. The smooth trait reduction
proves every hypothesis, including the divisor-point condition. No change records or
forced adaptations were needed.

## Second reading by N1

1. PASS: Compared both delivered modules against the read-only repository. The item
   has exactly the original theorem signature, byte for byte, and unchanged public
   imports and docstring. Its four added helpers are private proved theorems. The
   prescribed-equation module is new; no existing definition or statement changes.
2. PASS: Compiled both files independently in import order with lcompile.py: no
   errors or warnings (about 3 and 24 seconds). Checked the forbidden constructs
   and the only sorry, which is the whole proof of the named new theorem. Scratch
   copies with #print axioms checked all four private helpers and both public
   declarations; only the three standard axioms and permitted upstream sorryAx
   occur. There are no new data definitions or arbitrary data choices from holes.
3. PASS: Read the split theorem against Stacks 0EYG, including its displayed
   prescribed-f equations and descent, and 09EB. IsRegularRing includes
   Noetherianity. The divisor-point hypothesis excludes units and the zero ring;
   a trivial torsor has exponent one, disconnected torsors use stabilizers,
   positive-characteristic ramification is tame because the group order is a
   unit, and the empty product represents the empty scheme. This is strictly the
   punctured-cover input; it omits all trait and normalization assembly. Repeated
   leanfinder, loogle and grep searches with different queries and searched both
   Lean roots. The existing arbitrary-g chart cannot give the required equality
   with the uniformizer image. No existing usable prescribed-equation interface
   was found, and this substantial classical input cannot be closed in minutes.
4. PASS: Reviewed the proof from the target down through generic comparison, the
   explicit structural affine chart, divisor prime membership, normality and
   density, and normalizationDesc inverse maps and projection equalities. Each
   added import is used; none of the original proof_deps (empty) was discarded.
   The new input retains the unit's tame-chart step and the proof assembles its
   normalization step. The unit realized arrays are empty, not newly populated;
   no unit node or route is bypassed. No pruning or net hole reduction is claimed.
5. PASS: The existing node differs only in proof, proof_deps and proof_origin.
   Its dependency union names exactly the five Sheaf theorem inputs used. The
   new node has its self-contained statement, verbatim Lean signature, source,
   proof, three search kinds, split status, provenance and ancestor route.

Changes by the second reader: completed the new theorem's docstring and DAG
proof with the exponent-invertibility argument from 0EYG, corrected its author
credit to N1, appended independent search records, and corrected the report's
claim about the currently empty unit realized arrays. No Lean proof or signature
needed repair; the hole accounting remains one closed and one added.
