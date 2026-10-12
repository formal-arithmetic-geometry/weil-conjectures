## What changed

Added two lower representative calculations, and proved
`AlgebraicGeometry.Etale.strictLocal_exchange_compatibility` by cancelling its source
stalk comparison and applying colimit hom-ext on the initial affine pointed
neighbourhoods. The existing declaration signatures and definitions are unchanged.
The two new imports in the assigned module are proof-only.

The second reader also proved `AlgebraicGeometry.Etale.exchange_pointed_representative`
by adapting the existing representative calculation in `geometricFibreExchange_germs`:
the unit identity for exchange, marked-neighbourhood restriction, pullback hom-ext,
and terminal/global-section transport. It works for a commutative square without
assuming that it is cartesian.

Returned-delivery repair: removed the duplicate private declarations
`AlgebraicGeometry.Etale.sourceStalkIso_germ` and
`AlgebraicGeometry.Etale.eval_eq_res` from the new representative module. Added
proof-only `import all Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms` and
`import all Sheaf.AlgebraicGeometry.UnderivedGlobalGermExchange`, so the existing
private helpers are used directly. No existing library module, signature, or
visibility changes. The representative node records both actual helper dependencies.
All three sandbox modules compile cleanly after the repair.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Etale.strictLocal_exchange_compatibility`.

The first worker's added hole
`AlgebraicGeometry.Etale.exchange_pointed_representative`
(node `lem-weil-pbc-exchange-pointed-representative`) is also closed by the second reader.

One hole is added in this delivery and remains:
`AlgebraicGeometry.Etale.strictLocal_section_pullback`
(node `lem-weil-pbc-strict-local-section-pullback`). Its entire proof is `by sorry`.
There are no holes in definitions and no arbitrary data chosen from existence holes.
This delivery is a decomposition: one original hole closed and one lower hole added,
so its local net is zero. It does not claim that the target's import closure is sorry-free.

## No longer needed

Removed direct proof imports from the assigned module:
`Sheaf.AlgebraicGeometry.StrictHenselization` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`. Both remain available and
needed transitively through the replacement imports; no module is pruned.
The two duplicate local helper proofs are removed;
their existing library declarations remain needed and are imported directly. Of the original node's `proof_deps`,
`def-weil-pbc-geometric-stalks`, `lemma-openclosed-stalk-upperstar`, and
`def-weil-pbc-underived-exchange` are no longer separate steps of the main theorem's
proof: their calculation is now in `exchange_pointed_representative`, which uses them.
`def-weil-pbc-strict-henselization-limit` remains a direct dependency.
These nodes remain needed transitively; no module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified two private helper statements duplicated
word for word. Both have now been deleted from the new module; `import all` makes
the existing private declarations available only to this proof, avoiding any
visibility change or adaptation of their owners.

The first report called the upper hole proved without recording its cost as a
decomposition. Its two new holes were not searched independently: the first of them
has essentially the same representative calculation inside the already proved
`geometricFibreExchange_germs`. The second reader used that calculation and closed it.
The new nodes initially had empty proof dependencies despite describing non-elementary
unit and restriction arguments; these records have been corrected.

## New nodes

`lem-weil-pbc-exchange-pointed-representative`, in
`lean/Sheaf/AlgebraicGeometry/GeometricFibreExchangeRepresentative.lean`, is now proved.
It computes one representative, without strict-local data, a comparison map, or
cartesianness. Its source and complete argument are recorded in the docstring and node.

`lem-weil-pbc-strict-local-section-pullback`, in
`lean/Sheaf/AlgebraicGeometry/StrictLocalSectionPullback.lean`, is the remaining hole.
It computes one strict-local section restriction and has neither the stalk-colimit
argument, exchange, nor the comparison map a in its statement. Its source and complete
projection/unit argument are recorded in the docstring and node.

## Earlier second reading (a previous round; superseded)

1. Compared all delivered modules with the read-only repository. The assigned module's
existing signatures and definitions are byte-for-byte unchanged. The two sibling modules
are new. No target statement, public import, or definition of an existing module changes.
No change record or forced adaptation is required.

2. Compiled the three modules locally in import order. The assigned theorem contains
no sorry. The representative theorem now has a complete kernel-checked proof. Only the
named strict-local section pullback theorem has sorry. No forbidden declarations or
hollow definitions occur. Explicit scratch-copy #print axioms checks give exactly propext, Classical.choice,
and Quot.sound for exchange_pointed_representative. The main theorem and remaining
split also include sorryAx from their named open dependencies. No other axioms occur.
The three final modules compile cleanly in import order, and the delivery dry run passes.

3. Read both split statements and their definitions. Their projections and units give
exactly the maps claimed. Identity squares reduce to the usual unit/terminal-section
equalities. Zero coefficients make both sides zero; empty X or X′ cause no issue,
and an empty base has no supplied geometric point. Neither split merely restates the
item. Independently searched leanfinder for marked etale neighbourhood pullback section
compatibility, loogle for baseChangeMap, and local rg for unit_map_baseChangeMap_app,
geometricFibreSectionRestriction, and section pullback. Mathlib search returned only
topological sheaf or unrelated geometric lemmas. Local search found the proved
representative calculation in GeometricFibreExchangeGerms, used to close the first split.
No matching strict-local pullback theorem was found.

4. Read the colimit hom-ext reduction from the top downward and checked associativity
of the three equalities he, hr, and ha. The old dependency calculation is retained in the
proved representative theorem; there is no unit bypass. The unit sk-thm-iff retains its
statement and step realized by lemma-weil-pbc-property-iff-acyclicity. Imports remain
needed for signatures or proofs; no proof-only public import was added. The no-longer-
needed section lists all original dependencies removed from the direct node plan.

5. Compared the node statements against the Lean signatures and the main proof plan
against the actual uses of strict-henselization initiality and the two representative
calculations. New nodes have source, docstring proof, searches, creation, blueprint,
chapter/unit and Lean records. Corrected their dependency records and cited the node
whose module defines the geometric-fibre restriction maps.

Checked the cited Stacks sources: [03Q9](https://stacks.math.columbia.edu/tag/03Q9)
constructs restriction from pointed affine representatives to the strict-local limit;
[03Q1](https://stacks.math.columbia.edu/tag/03Q1) gives the inverse-image stalk
identification; [0A3U](https://stacks.math.columbia.edu/tag/0A3U) uses the proper
closed-fibre comparison. The new formulas are the explicitly expanded compatibility
calculations, not a new invertibility claim for arbitrary morphisms.

Second reading changed: closed exchange_pointed_representative using the existing
proved representative calculation; corrected dependency records and decomposition
accounting. Existing main proof and signatures were retained.


## Second reading by U3

1. PASS. Compared the assigned module with the repository using diff and extracted
all existing declaration signatures: both `module_inverseImage_stalk_germ` and
`strictLocal_exchange_compatibility` retain byte-identical signatures. No existing
public import, definition, visibility, or target statement changes. The two sibling
modules are new and require no existing-interface change record.

2. PASS, as a decomposition. Compiled all three delivered modules in import order
using lcompile.py, then compiled scratch copies with explicit #print axioms checks.
`exchange_pointed_representative` uses exactly propext, Classical.choice, Quot.sound.
`strictLocal_exchange_compatibility` and `strictLocal_section_pullback` additionally
use sorryAx, as allowed for their named open dependencies. There is exactly one
syntactic hole in the delivery, the entire named theorem strictLocal_section_pullback;
no forbidden constructs, hollow definitions, or witness choices from unproved mere
existence statements occur. One original hole closes and one lower hole is added:
local net zero, not a completed proof of the import closure.

3. PASS. Read the unit/limit-leg, fibre-lift, global-section pullback and comparison
definitions. The remaining split says only that restriction of one representative
commutes with pullback along q. It omits a, ha, exchange, stalks, colimit hom-ext and
cartesianness, so is strictly a part of the parent argument. Its docstring supplies
the full unit/naturality and projection proof and its node names the construction.
For identity maps the formula is the unit/composition and terminal-evaluation law;
for zero coefficients both maps are zero; for empty X' the terminal section module
is zero; an empty Y admits no supplied geometric point. The equations hq and hqt,
followed by hpoint at j, identify the two inner lift projections; the outer projection
is identity. Independently searched LeanFinder for inverse-image units and composite
section restriction, Loogle for adjunction unit uniqueness, and rg for restriction,
globalSectionsUpperStarMap and unit composition in both library roots. Found only
Zariski analogues, generic adjunction laws, neighbourhood refinement naturality, and
a holed integral existential comparison. None states the required arbitrary-q map
identity. Formalizing its terminal transport and unit-composition calculation is
substantial; it is retained as the documented named hole.

4. PASS. Read the proof downward: cancellation of e reduces to colimit hom-ext on
initial affine neighbourhoods, then he, hr and ha give the equality in that order.
Read the proved representative calculation against geometricFibreExchange_germs;
its adaptation removes the unused cartesianness restriction without changing any
existing declaration. Both import-all uses reuse existing private helpers. Public
imports in the new modules supply definitions occurring in their statements; the
assigned module's new imports are proof-only. Corrected the pruning report to name
both removed direct imports and explain that their modules remain needed transitively.
All three old dependencies removed from the direct proof plan are listed there.
The unit sk-thm-iff and its realized statement/step
lemma-weil-pbc-property-iff-acyclicity remain unchanged; no unit route is bypassed.

5. PASS after metadata repair. All three node Lean statement records agree with the
source signatures modulo whitespace. Every proof_deps list is the union of its
steps' uses. The main node records initiality and the two representative formulas;
the representative node records both imported private-helper owners. Added
lem-sbc-geometric-fibre-exchange-germs to the remaining split's proof dependencies,
because its final lift identification uses that node's geometricFibreSectionLift
and geometricFibreSectionRestriction definitions. New nodes contain the required
source, proof, origin, searches, creation, blueprint, chapter/unit and Lean records.
The cited [03Q9](https://stacks.math.columbia.edu/tag/03Q9),
[03Q1](https://stacks.math.columbia.edu/tag/03Q1), and
[0A3U](https://stacks.math.columbia.edu/tag/0A3U) were checked online because the local
Stacks source is absent. The formulas here are the agent's expanded representative
compatibilities underlying those comparisons; no finiteness or invertibility
conclusion is inferred for arbitrary morphisms.

Current second reading changed: corrected removed-import accounting; added the missing
geometric-fibre-definition proof dependency and independent search records; appended
this current review. Lean proofs and signatures were retained.
