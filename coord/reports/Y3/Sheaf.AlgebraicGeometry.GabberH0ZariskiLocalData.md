## What changed

Reduced `AlgebraicGeometry.gabber_h0_zariski_local_data` without changing its signature
or any existing definition. `GabberH0ZariskiConstructions` constructs the canonical
restriction sheaves, preimage-open isomorphism, top section lift, and section comparison
isomorphism explicitly. It proves continuity from `zariski_to_etale_core`, the first
projection identity from Mathlib's restriction/pullback identities, and constructs
the target section by the inverse of the section isomorphism. Its sole use of
Classical.choose is the existing composition comparison, whose unit characterization
uniquely determines it.

The original theorem now assembles those constructions, proves the target-section
image equation by the isomorphism inverse law, and constructs the preimage cover and
its sections. It applies the one-open representative equation and the top-unit equation
from two new proof-only imports. All four modules compile through lcompile.py.

The comparison and lift have explicit function types. Using an inferred categorical
morphism as the lift, or expanding the function composition when applying the top-unit
statement, made the kernel unfold the comparison construction excessively. The final
function interfaces and matching composition formula compile each file in under ten
seconds; no timeout workaround or existing interface change is used.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.gabber_h0_zariski_local_data`
(node `lem-weil-pbc-gabber-h0-zariski-local-data`).

Added two strictly narrower holes, so this is a decomposition, not an axiom-free proof:

- `AlgebraicGeometry.gabber_h0_zariski_representative_equation`
  (node `lem-weil-pbc-gabber-h0-zariski-representative-equation`): a single-open
  representative equation for the explicitly constructed sheaves and target section;
  no cover or existential construction conclusion.
- `AlgebraicGeometry.gabber_h0_zariski_top_unit_equation`
  (node `lem-weil-pbc-gabber-h0-zariski-top-unit-equation`): top-unit compatibility;
  no closed immersion hypothesis, representative, target section, or cover.

No sorry remains in the original module or in the constructions module. The latter
also proves `gabberOpenEtale_continuous` and `gabberPreimageEtaleIso_fst`.

Edge cases: the representative equation permits the empty open and arbitrary morphism
h; the top-unit equation permits empty schemes and arbitrary i,h. For an empty cover
index, the main proof of the preimage cover still works: hW forces Xprime empty and
hence the fibre product empty. No injectivity, gluing, or global preimage is asserted
by either intermediate theorem.

## No longer needed

Removed the direct proof imports
`Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites` and
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`.
The composition-units module is still needed through the existing public import
`FiniteSurjectiveSetDescentInjective`; it is not pruned from the dependency closure.

This proof does not need node
`lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites` or its stronger finite-limit
and exactness conclusions. It uses `lem-weil-pbc-zariski-etale-core` instead.
Thus `Sheaf.Paper.ZariskiEtaleSheafLeftExact` is not needed on this proof's route.
The other original proof dependencies (etale sheaves, fibre products, topological
inverse image, and etale composition with units) remain needed by the explicit
constructions or the equation lemmas. No unit realization or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

Removed the prior attempt's unused tautological helper `gabber_h0_zariski_cover_eq_top`.
The prior abandonment was unnecessary. The geometric data can be constructed directly
from Mathlib restriction/pullback isomorphisms and the existing unit-characterized
composition comparison. Only two compatibility equations have been split off.

`tools/blueprint_refs.py ancestor lem-weil-pbc-gabber-h0-zariski-local-data` returns
None because the chain's created.item fields contain module names. The new nodes
record the relevant blueprint ancestor `lemma-weil-pbc-proper-strict-henselian-h0`, the
Tag 09ZF paragraph, and the intermediate local-data/gluing/finite-section nodes.
The unit `sk-thm-iff` and its realized statement and step are unchanged.
The sources are available in the local literature mirror and were read there.
LeanSearch returned Internal Server Error; the search logs record it as unavailable.

## New nodes

`def-weil-pbc-gabber-h0-zariski-constructions` records the explicit canonical
restriction and transport data, including the inverse section comparison and local
representative. Its module contains real definitions and proved supporting facts.

`lem-weil-pbc-gabber-h0-zariski-representative-equation` records the single-open
representative equation, sourced to Tag 09ZF's construction of tPrime and its local
restrictions, with unit naturality and composition coherence written out.

`lem-weil-pbc-gabber-h0-zariski-top-unit-equation` records only the top-unit equation,
sourced to the same paragraph and the preceding functoriality paragraph.
There are no change records or forced adaptations.

## Second reading by Y3

1. Compared the delivered `GabberH0ZariskiLocalData` module with the repository version.
The target theorem signature and all existing declaration signatures are unchanged; the
only target change is replacement of its proof. Verdict: passes.

2. Compiled all four delivered modules with `lcompile.py --all`. The only remaining
`sorry`s are the two named split-off theorems, each public, documented, and represented
by a DAG node; no definition contains `sorry`, and no forbidden declarations occur.
Verdict: passes (the two open proof obligations are explicit `sorryAx` dependencies).

3. Checked the two split-off statements against the constructions and edge cases. The
representative equation is a single-open compatibility assertion, while the top-unit
equation is only top-unit compatibility; neither repeats the target conclusion or adds
unneeded hypotheses. Empty opens, empty schemes, and empty index types are covered by
their stated types and the main proof's cover argument. Verdict: true and strictly
narrower decomposition.

4. Traced the proof and imports. The proof uses the canonical restriction/pullback
constructions and the existing unit-characterized comparison; removed imports and the
unused cover helper are recorded above. The `sk-thm-iff` unit statement and realized
steps remain in the route. Verdict: pruned and route preserved.

5. Checked the four DAG nodes against the Lean declarations, including statements,
proof dependencies, sources, blueprint references, and `realized` unit metadata. No
change records or forced adaptations are needed. Verdict: agrees.

Changed only the report in this second reading; no proof or statement edits were needed.
