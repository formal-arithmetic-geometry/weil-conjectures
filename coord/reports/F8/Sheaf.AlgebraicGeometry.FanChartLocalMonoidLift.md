## What changed

Replaced the proof of `AlgebraicGeometry.fan_chart_local_monoid_lift` with a complete
combination of three strictly smaller geometric statements and the existing
`Algebra.integral_monoid_free_sharpening_splitting`. The theorem's signature is unchanged.

The new proved private algebra helpers extend a monoid equivalence to group completions,
transport a finite integer basis and a group splitting, and prove that **every** prescribed
group section restricts to a monoid section. For p choose a representative r; the element
s(p)/r lies in the quotient kernel, hence is represented by a unit v. Then v*r represents
s(p). Injectivity into the group completion proves multiplicativity and the section identity.
This algebraic argument is written in Lean, rather than moved into another hole.

The three geometric modules isolate the ordinary-stalk comparison, finite-data spreading,
and the characteristic criterion for being a chart. Their docstrings and nodes include the
source locations and complete mathematical proofs. The criterion uses the definition of
IsChart on all geometric stalks directly. The existing three quotient constructions moved
verbatim into FanChartStalkModel, publicly reexported by the item, to avoid an import cycle.
Change record: `coord/changes/fan-chart-stalk-quotient-location.md`.

Validation: `lcompile.py --all` compiled all four modules; the completed item took 7.8 s.
The three geometric modules previously compiled in 3.9--5.3 s each. Checked the main
signature and relocated definition bodies byte-for-byte against the original. All Lean
lines satisfy the 100-character limit. Overlay DAG traversal found no cycle through any
of the four delivered nodes. The delivery tool supplies the independent declaration/axiom probes.

## Proved and sorry left

Closed the item's one syntactic hole:
`AlgebraicGeometry.fan_chart_local_monoid_lift`
(node `lem-trf-fan-chart-local-monoid-lift`). Its proof and all private helpers are complete.
There are zero holes left in the item module.

Added three holes, one theorem in each new module:

- `AlgebraicGeometry.fan_chart_stalk_model` (`lem-trf-fan-chart-stalk-model`): ordinary
  stalk sharpening, integrality, fs/free properties and normalized fan localization.
- `AlgebraicGeometry.fan_chart_germ_spreading` (`lem-trf-fan-chart-germ-spreading`):
  spreading a given monoid section with exact germ and characteristic; no chart assertion.
- `AlgebraicGeometry.fan_chart_section_is_chart` (`lem-trf-fan-chart-section-is-chart`):
  the geometric-stalk pushout chart test for any already supplied section homomorphism.

This is a decomposition of one hole into three, not a completed proof of the full result
from sorry-free premises. It also uses the existing holed integral-monoid splitting theorem.
No holes occur in definitions. The relocated definitions are unchanged real constructions.

## No longer needed

Removed these proof imports from the item itself:
`Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation`,
`Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks`,
`Sheaf.AlgebraicGeometry.AffineFanLocalizationSections`, and
`Sheaf.TraceFormula.FsFaceSharpening`. Their mathematical inputs remain needed by the new
geometric statements, and their nodes are retained below those statements in the DAG.

`lem-weil-pbc-sets-etale-iso-on-geometric-stalks` is no longer a dependency of this
argument: the chart criterion proves the surjectivity and kernel equality defining
IsStalkChart, so it does not construct a global logification isomorphism and then invoke
conservativity. `lem-trf-affine-fan-hom-universal` is also unnecessary as a proof step:
the spreading statement restricts the original fan morphism itself, fixing both its point
map and sheaf maps. Its public import is preserved for the existing interface.
No existing module is withdrawn and no unit route is bypassed. These dependency removals
are local to this argument, not a claim that other targets cease to need their modules.

## Where the brief, the DAG or earlier work was wrong

The original proof sketch is mathematically consistent, but its declared theorem interfaces
do not directly provide the normalized ordinary-stalk comparison, the Zariski extension
with a prescribed characteristic morphism, or the exact pushout chart criterion in the
item's types. The three new statements expose precisely those geometric subarguments.
In particular, the existing splitting theorem supplies one section, while the item requires
every section; the unit-kernel argument supplying this extra clause is now proved in Lean.

The current source path for ZariskiLogStalkUnitExtension was absent when read, despite its
node's Lean attachment. No archived module is withdrawn or replaced here; its mathematics
is retained as a dependency of the stalk model and chart criterion.

Read the ILO passages VI 3.7(a), VIII 3.1.8, 3.1.10(ii), 3.3.12--3.3.13 and proof of
3.3.15. Checked edge cases: trivial characteristic (rank zero), empty generator/relation
tuples, arbitrary torsion in log units, and points where every chart generator becomes
a unit. The group proof never assumes torsion-free units, and the geometric statements
require no log-regularity or saturation of the entire target fan.

## New nodes

`lem-trf-fan-chart-stalk-model`: canonical comparison of Associates of the ordinary log
stalk with the fan stalk, retaining normalization and fs/free properties. Its module also
holds the three existing canonical quotient constructions verbatim.

`lem-trf-fan-chart-germ-spreading`: extends a monoid section using finite generators,
finite relations, and equality after shrinking; its output has no log-chart claim.

`lem-trf-fan-chart-section-is-chart`: tests an already supplied lift by its characteristic
fan morphism and proves the chart property through geometric-stalk pushout bijectivity.

All inherit the parent's chapter and unit. The source is ILO and the expanded parent
argument. Searches used LeanSearch, Loogle/LeanFinder, repository searches and Mathlib grep;
no equivalent existing statement was found. The unit's realized fields are unchanged.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
