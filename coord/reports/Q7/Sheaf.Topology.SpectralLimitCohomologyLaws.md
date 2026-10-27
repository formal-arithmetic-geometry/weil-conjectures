## What changed

Reduced `TopCat.Sheaf.spectralLimit_cohomology_laws` to normalized identity and
binary composition for individual cohomology f-maps. The original theorem
statement, docstring and public imports are unchanged. Its proof establishes the
colimit leg equation on every open section using `hP`, the adjunction unit
formula, cancellation of `eP`, and the coprojection cocone equation, then applies
the two f-map lemmas to construct all three fields of `CohomologyMapLaws`.

New proof imports: `Sheaf.Topology.SpectralLimitCohomologyMapIdentity` and
`Sheaf.Topology.SpectralLimitCohomologyMapComposition`. Each has exactly one
public named theorem with `:= by sorry`, a source and full proof in words.
The identity lemma concerns one space and one map equal to the identity; the
composition lemma concerns three spaces and two composable maps. Neither has an
indexing system, a colimit, or the cocone-leg assertion of the item. The parent
DAG proof now records the real combination argument. A local irreducibility
attribute bounds unfolding of the canonical-map construction while applying its
API; see `coord/changes/Q7-spectral-limit-cohomology-proof-scope.md`. No definitions or source
library files change, and the unit statement and steps are preserved.

## Proved and sorry left

This is a decomposition, not a net proof gain: the original hole in
`TopCat.Sheaf.spectralLimit_cohomology_laws`
(`lem-weil-pbc-spectral-limit-cohomology-laws`) is replaced by a complete proof
from two strictly smaller statements. There is no `sorry` in the item module.

Added two holes, and no others:

- `TopCat.Sheaf.spectralLimitCohomologyMap_id`, node
  `lem-weil-pbc-spectral-limit-fmap-identity`.
- `TopCat.Sheaf.spectralLimitCohomologyMap_comp`, node
  `lem-weil-pbc-spectral-limit-fmap-composition`.

## No longer needed

Removed private proof imports
`Sheaf.Topology.SpectralLimitCohomologyDegreeZero`,
`Sheaf.CategoryTheory.SiteCohomologyPullbackComposite`, and
`Sheaf.CategoryTheory.SiteCohomologyPullbackUnique` from the item. The new
assembly does not instantiate `spectralLimit_section_laws`; the module
`Sheaf.Topology.SpectralLimitCohomologyZeroLaws` remains publicly imported to
supply the existing structure `CohomologyMapLaws`.

Removed from this item's proof dependencies:
`lem-weil-pbc-site-cohomology-pullback-composite`,
`lem-weil-pbc-site-cohomology-pullback-unique`,
`lem-weil-pbc-spectral-limit-cohomology-degree-zero`, and
`lem-weil-pbc-spectral-limit-cohomology-zero-laws`.
The new f-map lemmas may use the general site lemmas in their eventual proofs;
this is not a claim that those modules have no other users. No module is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. A previous sandbox report claimed a
complete zero-hole proof before a successful compile; this report corrects that
claim. The initial complete draft repeatedly exceeded the fixed 60-second limit
while elaborating concrete sheaf/Ext/adjunction instances. Explicit types,
abstract Ext dimension shifting, local instance parameters and transparency
changes exposed further definitional-equality failures, rather than producing a
verified full proof. The delivered reduction isolates the mathematical identity
and composition steps, while retaining the actual colimit assembly in the item.
No timeout or limit increase is used to justify a blocked answer.

The sources read are Stacks Cohomology Tags 01F7, 01F8 and 0A37, including the
setup of `lemma-colimit`, and the current blueprint's `sk-thm-p1` statement.
Searches used LeanFinder, Loogle, LeanSearch, source grep, and the blueprint
reference search. No existing theorem giving these normalized topological f-map
laws was found. The general site composition interface uses precoverages and
compares pure pullbacks; the new statement additionally packages coefficient
f-maps and equality of continuous composites. Edge cases checked: degree zero,
identity maps, zero sheaves and empty spaces; neither new statement assumes
nonempty spaces. The directed-system hypotheses of the original are retained.

## New nodes

`lem-weil-pbc-spectral-limit-fmap-identity` states the identity law for one
normalized cohomology f-map. Its proof compares identity inverse image with the
identity adjunction in degree zero and uses injective dimension shifting for
positive degrees. Its module is
`Sheaf.Topology.SpectralLimitCohomologyMapIdentity`.

`lem-weil-pbc-spectral-limit-fmap-composition` states binary composition for
normalized cohomology f-maps, including transport along an equality of continuous
maps and sectionwise identification of the composite coefficient arrow. Its
proof uses the unit-compatible inverse-image comparison, boundary naturality,
and induction on degree. Its module is
`Sheaf.Topology.SpectralLimitCohomologyMapComposition`.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
