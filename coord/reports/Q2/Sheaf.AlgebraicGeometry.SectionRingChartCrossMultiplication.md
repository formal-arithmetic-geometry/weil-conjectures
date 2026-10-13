## What changed

Proved `AlgebraicGeometry.Scheme.Modules.sectionRing_chart_cross_multiplication` with its
signature unchanged. Added one proof-only import,
`Sheaf.AlgebraicGeometry.ProjChartPullbackFractionRelation`, whose theorem
`AlgebraicGeometry.Proj.chart_pullback_fraction_relation` is fully proved from Mathlib.
The new theorem is generic in a graded commutative ring and knows nothing about invertible
modules, free generators or the coefficient equation hρ.

The main proof takes p=t^n*t^k and r=ξ*t^k, transports their degree to (n*e)*d, and uses
the generic scalar fraction relation. Two instances of hρ, restricted from U to W,
turn this ring equality into the module equality by smul_smul. DirectSum.of_mul_of,
tensorPowAddIso naturality, and tmulSection_map identify the left numerator with the
displayed tensor product. Both modules compile locally without warnings. The resumed worker reread both complete
proofs, checked the unchanged statement and the unit realization, and reran lcompile.py
--all successfully. The delivery dry run printed OK; nothing was pushed.

The generic proof moves the fractions to the homogeneous localization at t*s, proves their
product relation by explicit localization cross multiplication, and applies the chart
section pullback. Private proved helpers identify inclusion restriction with topIso and
the inverse chart pullback with ΓSpecIso.inv. No data or interface of an existing
declaration changed. The parent node's proof, proof_deps and proof_origin now follow this
Lean argument; the unit's realized statement and route are unchanged.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.sectionRing_chart_cross_multiplication`
(lem-sc-section-ring-chart-cross-multiplication).

Also proved the new theorem `AlgebraicGeometry.Proj.chart_pullback_fraction_relation`
(lem-sc-proj-chart-pullback-fraction-relation) and its two private helpers,
`inclusion_top` and `away_top`. No sorry remains in either delivered module; no hole is
added or split off. This is a proof, not a decomposition. The compilation and server
preflight checks passed through deliver3.py --no-push. The independent second reading is recorded below.

## No longer needed

No imports were removed: the two original public imports remain necessary for the unchanged
statement. No module is asserted to have become globally unreachable.

The parent's proof no longer directly depends on def-sc-local-free-generator,
def-sc-invertible-module, def-pc-proj, or lem-weil-pbc-morphism-into-affine-scheme.
The first two still occur in its statement dependencies; the last two are used by the
new generic chart theorem. In particular, this proof needs no local basis, local
free-generator coefficient cancellation, or sheaf-separation/gluing argument.
The new generic theorem even permits t to have degree zero. The original hs and e>0
hypotheses are retained unchanged, although this argument does not need them.

## Where the brief, the DAG or earlier work was wrong

The original proof plan listed definitions and the affine-map correspondence, but none of
those declarations directly supplied its fraction-comparison or tensor calculation.
The needed geometric part is now an explicit, fully proved generic theorem. The local-basis
route was unnecessary: the two given numerator equations hρ suffice, with no cancellation.

Searches were run through msearch.py: LeanFinder found localization/chart lemmas but no full
section-ring formula; Loogle found Away.mk and later Proj.awayMap_awayToSection; grep located
Mathlib's chart/restriction identities and the source's specialized coordinate-ratio proofs.
LeanSearch returned Internal Server Error, recorded as unavailable. The whole-blueprint
searches for fraction and homogeneous localization returned 31 and 5 nodes; none states
the new generic relation. The ancestor command returned None because the module-created
chain is not traversed by that node-only helper; the new node inherits the explicit
lem-sc-pic-proper-ntorsion ancestor and via chain from the item's existing blueprint record.

The local repository lacks literature/stacks-project and the imported blueprint text files.
The source was read at https://stacks.math.columbia.edu/tag/01N8 and
https://stacks.math.columbia.edu/tag/01NK, and constructions.tex was downloaded only into
the sandbox scratchpad. The relevant labels are lemma-converse-construction and
lemma-invertible-map-into-proj. The explicit common-localization expansion is recorded
as agent-written. Edge cases checked in the argument: n=0, d=1 (k=0), N=0, t=0,
nilpotents, and empty chart intersections. No positivity cancellation or nonzero denominator
assumption is used. The generic localization calculation uses witness 1 and therefore
works in rings with zero divisors.

## New nodes

`lem-sc-proj-chart-pullback-fraction-relation`, in
`dag/nodes/sec-curve-estimates/lem-sc-proj-chart-pullback-fraction-relation.json`, is a
fully proved generic scalar comparison between projective charts, implemented by
`Sheaf.AlgebraicGeometry.ProjChartPullbackFractionRelation`. It assumes the homogeneous
numerator identity ξ*p=r*t^n and concludes the scalar equality after pullback; it has no
module sections, tensor multiplication, or coefficient hypotheses hρ. The main theorem
uses two hρ equations and tensor naturality to pass from this strictly geometric result
to its module-valued conclusion. No change record is needed for existing interfaces.

## Second reading by Q2

1. PASS: Compared the delivered main module with the repository using diff. The only
   changes are the added plain proof import and replacement of the theorem's sorry by
   its proof. The existing signature, visibility, definitions and docstring are byte
   for byte unchanged; no change record or forced adaptation is needed. The other
   module is new and contains only proved theorems and private proved helpers.
2. PASS: Independently compiled both complete modules in import order with lcompile.py
   --all; no errors or warnings. Scratch copies with #print axioms checked the main
   theorem, the generic chart theorem, inclusion_top and away_top: each uses exactly
   propext, Classical.choice and Quot.sound, with no sorryAx. Text inspection found no
   sorry or forbidden declaration in either delivered module. No definition chooses
   data from an unproved theorem; all numerators and fractions are explicit.
3. PASS: No statements are left split off and no holes are added. Read the new generic
   theorem and its full docstring proof. Its homogeneous degrees make all three
   fractions degree zero. The localization calculation uses witness 1 and no
   cancellation, covering n=0, N=0, t=0, nilpotents and empty overlaps; e=0 also needs
   no positive-degree chart isomorphism for t. For d=1 the main proof has k=0, and
   for n=0 all degree transports still agree. Independent searches through msearch.py
   (grep and Loogle) and rg on both project roots and Mathlib found the chart maps and
   related specializations, but no replacement for the generic theorem. In particular,
   awayMap_mk_one_eq_mul and appTop_awayMk_eq_mul require equal degrees and exponent
   one; AffineBlowup.awayMap_chartFrac and projective-space ratio lemmas specialize
   the graded ring or numerators. The new result is a scalar geometric lemma, not a
   renamed copy of the module-valued item, and is itself fully proved.
4. PASS: Read the proof from its conclusion downward. The scalar comparison followed
   by two hρ identities avoids local generators, cancellation and gluing. The main
   theorem then identifies the explicit direct-sum product with tensor multiplication
   and applies naturality. Both original public imports are required by the unchanged
   signature; the new import is correctly plain, and the new module's only public
   import supplies its signature. No shorter applicable existing theorem was found.
   Checked the original proof_deps against the new ones: all four removed direct
   dependencies are listed under No longer needed. They are not claimed to be globally
   pruned modules. The unit sk-thm-curveestimate still realizes its statement through
   thm-sc-proper-cohomology and has no realized steps; this delivery changes only a
   supporting node's route below that level.
5. PASS: Compared the old and delivered parent node: only proof, proof_deps and
   proof_origin change. Its new steps describe the actual degree transport, scalar
   relation, hρ restrictions and tensor naturality. Read the new node whole: its
   statement and Lean record match the theorem, its dependency union matches its
   proof steps, and it records source, searches, creation, chapter, unit and blueprint
   provenance. Existing node metadata and the unit are unchanged.

Second reading changed only this report: completed the independent review and replaced
its pending-review sentence. No mathematical or Lean repair was necessary. One existing
hole is closed, zero holes are added, zero are split off, and no module is pruned.
