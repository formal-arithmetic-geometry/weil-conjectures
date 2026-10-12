## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isInvertible_tensorPullback_iso_of_isClosedImmersion`
with its signature unchanged. The proof follows Stacks 09NY: form the categorical kernel
sequence of units, use dimension-one second-cohomology vanishing and the long exact sequence,
then use the canonical comparison and Hilbert-90/Picard naturality.

Added two proved modules: `Sheaf.AlgebraicGeometry.ClosedImmersionUnitsEpi` proves local lifting
of units using surjective local stalk maps and basic opens;
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitsCohomologyComparison` proves bijectivity of the
particular canonical comparison in every degree using exact direct image and the source
library's `Adjunction.mapExtCounit_bijective`. The private proof of preservation of epis is
adapted from the private helper in `ClosedImmersionPushforwardCohomology`; that helper is
inaccessible from an ordinary import. Both new public theorems are proved, not deferred.

The unit route is retained. The unit `sk-thm-curveestimate` has no realized proof steps that
this delivery bypasses. Sources read: Stacks 09NY and 02UV on the official Stacks website
(the local TeX copies are absent on this machine).

## Proved and sorry left

Proved the item's one sorry:
`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_tensorPullback_iso_of_isClosedImmersion`
(node `lem-sc-pic-lift-closed-immersion-dim-le-one`).

Also proved:
- `AlgebraicGeometry.Scheme.epi_unitsSheafToPushforward_of_isClosedImmersion`
  (`lem-sc-closed-immersion-zariski-units-epi`).
- `AlgebraicGeometry.Scheme.bijective_unitsPushforwardCohomologyComparison_of_isClosedImmersion`
  (`lem-sc-closed-immersion-units-cohomology-comparison-bijective`).

No sorry remains in any delivered module; none was split off. The main proof uses the
existing stated vanishing and Picard compatibility theorems, which still contain sorry in
the base library. Local compilation of all three files passed without warnings. The
comparison proof uses a local 400000-heartbeat limit because identifying the concrete
Ext maps unfolds the sheaf-adjunction construction; compilation remained below 60 seconds.

## No longer needed

Removed the direct proof import `Sheaf.Topology.ClosedImmersionPushforwardCohomology` and
replaced that node in the item's direct proof dependencies with the proved canonical
comparison specialization. The bare existential cohomology isomorphism is not used in this
proof. Its module/node remains transitively imported through Picard compatibility, so this
is not a claim that it can be deleted from the whole targets' closure. The old direct proof dependency `def-weil-closed-immersion` is also no longer used
as a proof step: the new units-epimorphy lemma supplies that step. Its closed-immersion
hypothesis and statement import remain necessary. No unit node was removed.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically correct, but its interfaces omitted local epimorphy
of the units restriction. Its cohomology comparison theorem only returns `Nonempty` of an
unspecified isomorphism; this cannot establish bijectivity of the particular map occurring
in Picard naturality. The two proved specializations supply these interfaces. No existing
statement or definition was changed. The three search kinds were performed for both new
nodes; LeanSearch returned Internal Server Error and was recorded as unavailable. Local
source searches found the usable general Ext-adjunction theorem.

Edge cases checked in the argument: identity immersion; empty closed subscheme (empty
inverse-image units group is trivial); zero-dimensional and empty ambient schemes (the
existing vanishing lemma applies); degree zero of the comparison (the Ext-adjunction
bijection also applies).

## New nodes

`lem-sc-closed-immersion-zariski-units-epi` records the proved epimorphy of the canonical
units map, in `lean/Sheaf/AlgebraicGeometry/ClosedImmersionUnitsEpi.lean`.

`lem-sc-closed-immersion-units-cohomology-comparison-bijective` records the proved bijectivity
of the canonical comparison, in
`lean/Sheaf/AlgebraicGeometry/ClosedImmersionUnitsCohomologyComparison.lean`.

Both are strictly parts of the 09NY argument and neither restates line-bundle lifting.
No change records are required: only the main theorem's proof and proof imports changed;
the two additional modules expose new proved theorems.

## Second reading by G3

1. Compared the delivered main module with the repository by `diff -u`. Its existing
   theorem signature is byte for byte unchanged; no definition or existing public import
   changed. The two additional modules are new. No change record is needed.
2. Compiled all three modules locally with the required launcher, in import order:
   30.2 s, 3.6 s, and 10.4 s, with no errors or warnings. Inspected every proof, including
   the private exact-pushforward helper. No delivered module contains `sorry`, an axiom,
   an unsafe/opaque declaration, or a foreign implementation. Scratch `#print axioms`
   checks show only propext, Classical.choice and Quot.sound for both new public theorems.
   The main theorem additionally uses sorryAx through existing dependencies; it is a
   reduction closing the item's one hole, not an axiom-free closure of its dependencies.
3. No statement was split off with sorry. Both new proved statements are strictly parts
   of the argument. Checked local unit lifting using the surjective local stalk map,
   basic-open invertibility and the ambient neighbourhood obtained by removing the
   closed image of the complement. Checked exact direct image and the precise order of
   Ext precomposition and counit composition in the canonical comparison. Identity,
   empty closed subscheme, degree zero, and zero-dimensional ambient cases cause no
   additional hypotheses. Independent LeanFinder search for exact closed-embedding
   direct image and Loogle search for isUnit_map_iff found components but no replacement.
   Searched both source roots and Mathlib for unit epimorphy, closed-embedding pushforward,
   Ext-counit bijectivity, and H/H-prime comparison. The general proved Ext-adjunction
   theorem is already used. The existing identical private pushforward helper cannot be
   imported; duplicating its proof here avoids exposing a changed upstream API.
4. Read the proof from the lifting conclusion downward. The kernel/vanishing/long-exact
   sequence, canonical comparison and Picard naturality are all needed. Proof imports
   are ordinary imports; public imports supply signature notions. The new canonical
   comparison avoids relying on an unspecified isomorphism. The old direct dependencies
   no longer used are lem-sc-cohomology-closed-immersion-pushforward and
   def-weil-closed-immersion (the latter still supplies a signature notion). The report
   now lists both. The former remains transitively imported: no whole module is pruned
   from the targets' closure. Read dag/units/sk-thm-curveestimate.json: its realized
   statement is thm-sc-proper-cohomology and it has no realized steps, so none is bypassed.
5. Compared the existing node's old and new proof/dependency lists, and read both new
   nodes in full. Their Lean declarations and verbatim signatures match; dependency
   unions match their proof steps; sources, proof origins, creation/blueprint records,
   and three search kinds are present. The main node records the actual kernel and
   canonical-comparison route. Its historical Lean docstring describes the original
   09NY plan, while the updated node and this report name the proved specializations.

Changes by the second reader: completed the list of old direct proof dependencies no
longer used and added this review. No Lean proof or statement required repair. Closed
one existing hole; added zero holes; split off zero statements with sorry. Scratch axiom
probes were removed before delivery.
