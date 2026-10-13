## What changed

Reduced `AlgebraicGeometry.Etale.sourceLocalizedSectionsIso_germ` without changing its
signature or any existing definition. Its proof now moves the derived-sections comparison
across the presheaf germ, uses the characterizing equation of the unique stalk restriction,
and reduces an arbitrary derived Hom element to an actual single-source cocycle. A local
proved cancellation calculation identifies the evaluation isomorphism on that cocycle.

Added two proof dependencies, in new modules `SourceLocalizedCocycleHomology` and
`SourceCocycleExactRestriction`. The first compares localization with the actual homology
section on the base site. The second compares degreewise application of an arbitrary
natural transformation into exact strict-local sections with that homology section; it
requires no K-injectivity. Added the genuinely constructed helper definition
`sourceCocycleHomologySection`: lift the cycle, project to homology, transport along the
specified representative, and evaluate the free generator. It uses no existence witness.
The original module imports only the second new module privately; the second publicly
imports the first because its statement uses this definition.

Updated the original DAG proof to the actual cocycle reduction. Added matching nodes with
sources and complete proof plans for the two remaining compatibility statements. No unit
statement or realized unit step is bypassed; `sk-prop-h2.realized` contains no binding of this
item to a unit step.

## Proved and sorry left

Closed the original module's only hole,
`AlgebraicGeometry.Etale.sourceLocalizedSectionsIso_germ`
(node `lem-weil-pbc-strict-local-localized-hom-germ`), by decomposition into two strictly
smaller cocycle comparisons. This is a decomposition, not an unconditional proof or a
net reduction in holes: one hole closed, two holes added, net minus one.

The new remaining holes are exactly:

- `AlgebraicGeometry.Etale.sourceLocalizedCocycleHomology`, node
  `lem-weil-pbc-source-localized-cocycle-homology`, module
  `Sheaf.AlgebraicGeometry.SourceLocalizedCocycleHomology`.
- `AlgebraicGeometry.Etale.sourceCocycleExactRestriction`, node
  `lem-weil-pbc-source-cocycle-exact-restriction`, module
  `Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction`.

Repaired the earlier attempt's timeout by keeping transparency respected in the main proof,
writing the composite application explicitly before the cocycle rewrite, and restricting the
final normalization to the two local constructions. The module compiles without warnings.

The original module has no remaining sorry. Its private germ-leg helper and local
isomorphism cancellation calculation are fully proved. All existing declarations retain
their signatures and visibility.

Edge-case checks: both new comparisons accept every integer degree, including negative
degrees; zero cocycles produce zero on both sides by additivity; boundaries give zero by
the homology projection and functoriality. The second comparison allows the zero natural
transformation, for which both sides vanish, and requires no acyclicity of the inverse-image
complex. The statements contain no division, degree-range restriction or choice of a
representative section. An arbitrary derived Hom element is reduced using the existing
K-injective localization isomorphism, quotient surjectivity and single-source cocycle
surjectivity, rather than an extra existence assertion.

## No longer needed

None. The only original public import, `StrictLocalInjectiveSourceComparison`, is required
by existing definitions and the proof. All three original proof-dependency nodes remain
used: `def-weil-pbc-canonical-derived-cohomology-germs`,
`def-weil-pbc-strict-henselization-restriction`, and
`def-weil-pbc-strict-local-injective-source-comparison`. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The three original proof steps do not have declarations for
the explicit cocycle compatibility equations; those are the two new items. Existing
localization and homology definitions supply the constructions, but not these equalities.
LeanSearch was unavailable (Internal Server Error); actual attempts are recorded in
`searches.jsonl`. LeanFinder, Loogle and direct source searches found generic Hom-complex,
cycle and exact-functor homology infrastructure, rather than either new explicit equality.

The literature files are absent in this machine's read-only clone; the cited Stacks pages
were read directly at https://stacks.math.columbia.edu/tag/03Q8,
https://stacks.math.columbia.edu/tag/03Q9 and https://stacks.math.columbia.edu/tag/03QO.
The detailed comparison calculations are marked as agent-written elaborations of those
constructions. No changes to another holder's module were needed.

## New nodes

`lem-weil-pbc-source-localized-cocycle-homology` isolates the base-site calculation:
the localized class of an actual cycle is sent to the section constructed from its cycle
lift and homology projection. It has no geometric point or stalk-restriction conclusion.
The associated module also constructs `sourceCocycleHomologySection` directly.

`lem-weil-pbc-source-cocycle-exact-restriction` isolates the exact-functor calculation:
apply an arbitrary natural transformation to a cocycle degreewise, then compare its
localized homology with application to the cycle's homology section. It has no
K-injectivity, localized-Hom germ leg, stalk, direct image or base-change mate. These
statements combine only after the original module's proved germ calculation and cocycle
reduction; neither restates the original theorem. No change record is needed.

## Second reading by V3

1. Compared the entire existing module with the repository version using `diff`, and
   separately checked the five existing declaration signatures byte for byte. All are
   identical. Existing definition bodies and docstrings are unchanged. The only added
   import is private, and there are no forced adaptations or interface change records.
   Verdict: pass.

2. Compiled the three modules in dependency order with `lcompile.py`. The first main-module
   compile reached the 60-second limit under substantial machine load; its separate retry
   compiled cleanly in 52.7 seconds. Scanned all three sources: precisely the two reported
   named public compatibility theorems have `sorry`; no definition has one, and none of the
   prohibited trust-bypass declarations occurs. The cocycle homology section is constructed
   by a cycle lift, homology projection and specified isomorphisms. The inherited stalk
   restriction is chosen from a uniqueness statement whose characterizing equations are
   used by the proved helper. Explicit `#print axioms` scratch probes compiled for all public declarations: only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the two open comparisons
   and the theorem using them. The new helper definition uses only the three permitted
   axioms. Verdict: pass.

3. Read both split-off statements and their docstring arguments against the constructions
   in `StrictLocalInjectiveSourceComparison`, `StrictLocalCohomologyGerms`, and the cited
   sources [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [03Q9](https://stacks.math.columbia.edu/tag/03Q9), and
   [03QO](https://stacks.math.columbia.edu/tag/03QO). Checked zero cycles, boundaries,
   negative degrees, identity transport, and the zero natural transformation. Neither
   comparison needs acyclicity of the pulled-back complex. The second is compatible with
   arbitrary natural transformations by naturality on the cycle inclusion and homology
   projection into an exact target. The base-site comparison has no restriction or stalk;
   the exact-target comparison has no K-injectivity or localized-Hom germ leg. They are
   strictly separate parts of the original argument, not renamed copies of its conclusion.
   Independent LeanFinder, Loogle and grep searches used different queries (recorded in
   `searches.jsonl`). Read `liftCycles_shift_homologyπ`, the Hom-complex homology projection
   lemmas, `ShortComplex.homologyMap_mapNatTrans`, and the upstream single-source homology
   calculation. These supply infrastructure, not either complete displayed equality; the
   upstream calculation is degree zero for a bounded-below complex, whereas this reduction
   uses an arbitrary specified unbounded representative and its shift/localization
   comparisons. No split-off statement was immediately closable. Verdict: pass.

4. Followed the proof from its original conclusion: germ naturality and unique stalk
   restriction first, then existing localization/quotient/cocycle surjectivity, then the
   two remaining calculations. The cancellation step is proved locally. Imports are
   minimal for the exposed definitions and the new theorem statements; the new proof-only
   dependency of the original module is private. Compared the original proof dependencies:
   all three remain used, so `No longer needed: None` is complete. Read
   `dag/units/sk-prop-h2.json`: its realized statement and step arrays are empty; this item
   has no realized unit step to bypass. Verdict: pass.

5. Read all three delivered node files, compared the existing node with the repository,
   and matched their declarations and proof plans against the Lean. The original node
   changes only its Lean record, proof, proof dependencies and proof origin. Each new
   node supplies its source, dependencies, searches, creation and blueprint ancestry,
   chapter/unit, and verbatim normalized Lean statement. The definition helper is listed
   in the base-site node's declaration inventory. Proof-dependency unions agree with the
   proof steps, including both new comparisons in the original reduction. Verdict: pass.

Second reading changed this report only; no mathematical or Lean repair was warranted.
The delivery remains a decomposition: one original hole closed and two smaller holes
added, net minus one, with no pruned nodes or modules.
