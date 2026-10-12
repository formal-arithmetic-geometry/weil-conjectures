## What changed

The signature of `Algebra.Smooth.exists_standardSmooth_retract` is unchanged. Its proof now
uses the existing `Algebra.smooth_retract_relative_global_complete_intersection`, obtains an
explicit polynomial localization from a new chart lemma, and constructs the section and
retraction in Lean. The proof extends evaluation at zero through localization, checks the
composite on every element of A, composes smooth maps, and transports the resulting algebra
through ULift to the required universe.

Two new modules accompany the reduction:

- `Sheaf.RingTheory.SmoothConormalBasisEtalePolynomialChart`: the concrete chart construction
  in steps 2--12 of the original node, restricted to a supplied smooth quotient with its
  equation-class conormal basis. It asserts a localizing element of constant coefficient one
  and an etale map from the n-variable polynomial algebra into that explicit localization.
  It asserts no arbitrary algebra, no section, no retraction, and no standard smoothness.
- `Sheaf.RingTheory.EtalePolynomialStandardSmooth`: completely proved from Mathlib's etale
  characterization, polynomial differential basis, and standard-smooth composition. It
  replaces steps 13--14's square-presentation construction.

All three modules compile cleanly with lcompile.py in import order. No definitions, existing
signatures, public imports, or target statements change. No existing module is adapted.
The original node and both new nodes record the actual route.

## Proved and sorry left

Closed the original hole:
`Algebra.Smooth.exists_standardSmooth_retract`
(node `lem-weil-pbc-smooth-retract-standard-smooth`).

Also proved the new, reusable theorem
`Algebra.isStandardSmooth_of_etale_polynomial`
(node `lem-weil-pbc-etale-polynomial-standard-smooth`).

Added exactly one hole:
`Algebra.exists_etale_polynomial_chart_of_conormal_basis`
(node `lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart`). Its proof is exactly
`by sorry`, in its own module, with the source and complete proof plan in its docstring.
There are no sorries left in the original module or in EtalePolynomialStandardSmooth.
This is a decomposition: one upper hole closed and one concrete lower hole added, net zero.
The existing dependency `Algebra.smooth_retract_relative_global_complete_intersection`
remains unproved and is not changed by this delivery.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.EtaleRingMapConormalCriterion`.
The node `lem-weil-pbc-etale-ring-map-conormal-criterion` is not needed by the resulting
proof or the new chart lemma. Mathlib now supplies the final etale-to-standard-smooth step.
The original proof's separate final use of
`lem-weil-pbc-conormal-free-presentation-basis` is also unnecessary; that node is still
needed indirectly by the existing relative-complete-intersection retract theorem, so this
is not a claim that its whole module leaves the targets' closure.

The following original imports move to the chart lemma's proof plan and remain necessary
there; they are not globally pruned:
`Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`,
`Sheaf.RingTheory.ClosedPointDimensionLocalRing`, `Sheaf.RingTheory.Depth`,
`Sheaf.RingTheory.FlatOfFlatClosedFiber`,
`Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`,
`Sheaf.RingTheory.MiracleFlatness`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`,
`Sheaf.RingTheory.SingularIdeal`,
`Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension`,
`Sheaf.RingTheory.SmoothFibreRegularLocal`, and
`Sheaf.RingTheory.SmoothLocalizationConormalSplit`.

All other former construction dependencies remain in the new chart node's plan, or are
used by the original theorem's proved map construction and smooth composition. No node
realizing a unit statement or unit proof step is bypassed; this item and its new helpers
are below the fixed realized nodes of unit sk-thm-p1.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The full square-presentation argument in step 13
can be replaced by the already proved Mathlib characterization
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`, then standard-smooth
composition. Freeness alone would not suffice: Mathlib explicitly cautions that a smooth
algebra with free differentials need not be standard smooth; the proved polynomial lemma
uses a basis consisting of exact differentials, and the chart hypothesis supplies etaleness.

The source is Stacks 07CH, read at https://stacks.math.columbia.edu/tag/07CH; the canonical
literature/stacks-project/smoothing.tex path is absent on this worker machine. The supplied
node and docstring give its numbered argument, retained in the chart node. The chart's
docstring excludes the old step 6's construction of A's retraction, which is now proved in
the original module.

LeanSearch returned Internal Server Error for both new-node searches. This is recorded as
unavailable, without a no-match verdict. LeanFinder/Loogle and Mathlib grep were available;
the relevant signatures were read. Searches of the whole blueprint and the DAG found no
existing node for either new helper statement. The existing smooth-section differential
basis statement concerns etale base extension along a section, not this explicit chart.

Edge cases checked mathematically: with c = 0 the quotient has no equations, g = 1 and the
identity polynomial chart work; with C the zero ring, its polynomial algebra and its
localization are zero, constant coefficient 1 equals 0, and etaleness is vacuous. No
nontriviality or c <= n hypothesis is imposed. The standard-smooth polynomial theorem
also admits n = 0 and the zero algebra. The arbitrary universes of the original statement
are handled by the explicit ULift equivalence.

## New nodes

`lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart` records the explicit chart
construction in Stacks 07CH. The prescribed quotient, polynomial extension, and localization
make this strictly a part of the argument; the original theorem still supplies its input
from 07CG and proves its section, retraction, smooth inclusion, and standard smoothness.
The theorem's conormal basis hypothesis is exactly what step 2 uses; the relative fibre
dimension assertion from 07CG is not used independently.

`lem-weil-pbc-etale-polynomial-standard-smooth` records the proved Mathlib argument that an
etale algebra over a finite polynomial algebra is standard smooth over the original base.
Its complete proof and node document the replacement of steps 13--14. It adds no hole.

No change record is needed: no existing statement, definition, or interface changes.

## Second reading by Y2

1. Compared the delivered target module with the repository version. The existing theorem
signature and all target-visible declarations are unchanged; the proof-only rewrite removes
only unused imports and introduces the two declared helper modules.

2. Compiled all three delivered modules with `lcompile.py --all`. They compile without errors
or warnings. The target module has no `sorry`; the sole remaining `sorry` is the named chart
theorem, with its source, proof plan, and DAG node. No forbidden declarations or hollow
definitions were found.

3. Checked both new statements against the construction in Stacks 07CH and against small
cases recorded above. The chart statement is a strict concrete reduction and the
étale-polynomial statement is proved from Mathlib; neither duplicates the target. Searches
and the node records document the unavailable LeanSearch calls and the available searches.

4. Checked the proof route and pruning. The target still uses the relative complete-intersection
retract and the chart unit route; the direct conormal-criterion import and its final square
presentation are no longer used. Imports in each module are minimal for statements versus
proofs, and the unit's realized route remains represented by the chart and target nodes.

5. Checked the DAG records against the Lean declarations, including proof dependencies,
proof origins, new-node metadata, and the unchanged unit/chapter. No statement or definition
change record is required.

Changed during this second reading: appended this review; no Lean proof or statement changes
were needed.
