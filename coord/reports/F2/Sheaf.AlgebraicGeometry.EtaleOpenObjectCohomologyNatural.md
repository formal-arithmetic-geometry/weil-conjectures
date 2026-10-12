## What changed

The statement of `AlgebraicGeometry.etaleOpenObjectCohomology_natural` is unchanged.
Its proof now constructs the comparisons from an explicit additive map, upgrades that
map using bijectivity, and proves the required naturality by Ext algebra. The private,
fully proved helper `canonicalMap_naturality` expands the maps, applies the degree-zero
generator coherence, uses `exactFunctorCompositionComparison`, and cancels the
composition comparison with its inverse.

Three new modules provide the explicit map, its bijectivity obligation, and its
identity-generator coherence obligation. `etaleOpenFreeSheafSection` is constructed
from the actual free generator using the sheafification unit and the inverse of the
localization restriction comparison. `etaleOpenFreeSheafUnit` classifies this section
using the constant-sheaf adjunction. `etaleOpenObjectCohomologyMap` applies inverse image
to an Ext class and precomposes with that specified morphism. No definition contains
sorry and no arbitrary witness is chosen from an unproved existence statement.

The item now imports `EtaleOpenObjectCohomologyMapBijective`,
`EtaleOpenFreeSheafUnitCoherence`, and `ExtExactFunctorCompositionComparison` for its proof.
The node records the actual reduction, and the two new obligations are separate items.
All four modules compile with lcompile; the delivery dry run checks them and their axioms.
The change record is `coord/changes/etaleOpenObjectCohomologyMap.md`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.etaleOpenObjectCohomology_natural`
(node `lem-weil-pbc-etale-open-object-cohomology-natural`). The item's module now contains
no sorry. `canonicalMap_naturality` is fully proved from the sheaf-level coherence lemma
and the existing exact-functor Ext comparison.

Added two holes, each strictly part of the original argument:

- `AlgebraicGeometry.etaleOpenObjectCohomologyMap_bijective`, node
  `lem-weil-pbc-etale-open-object-cohomology-map-bijective`: bijectivity for the fixed,
  explicitly constructed map at a single open, with no naturality assertion.
- `AlgebraicGeometry.etaleOpenFreeSheafUnit_coherence`, node
  `lem-weil-pbc-etale-open-free-sheaf-unit-coherence`: a degree-zero equality of specified
  sheaf morphisms, with no coefficient sheaf, cohomological degree, or Ext class.

This is a decomposition: one original hole closed, two lower holes added, net -1.
It is not a claim of a proof free of sorry in its transitive dependencies. The four
construction definitions are complete and introduce no holes. The two remaining
statements were checked on degree zero (for bijectivity), equal opens, and the empty
open: the generator construction reduces to evaluation, the equal-open identity is
an adjunction/composition coherence equation, and sections over the empty site are zero.
No extra scheme hypothesis is used.

## No longer needed

Removed all five original proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`;
- `Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit`;
- `Sheaf.Paper.SiteRestrictionInjectives`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The general cohomology pullback functoriality node
`lem-weil-pbc-cohomology-pullback-functorial` and its module are unnecessary for this
argument: naturality is proved directly from Ext composition and a degree-zero generator
identity. The other four removed direct imports remain needed through the new construction
and obligations. Their nodes are not globally pruned. The old item proof dependencies for
injective resolutions, restriction injectives, inverse-image restriction, open immersion
etaleness, object cohomology, open restriction units, open fibre products, and inverse-image
composition remain ingredients of the new definition and lower obligations, rather than
being claimed as eliminated. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies give ingredients but no declaration assembling the lifted free
representable comparison used in this item's signature. Mathlib's pinned
SheafCohomology.Basic explicitly lists the object/localized-site comparison as TODO.
The existing `cohomology_over_object_localization` uses ordinary Yoneda and identifies
slice object cohomology; it does not specify the needed lifted map or open naturality.
The existing `etaleCohomologyOverOpen` has global `Sheaf.H G q` as its source and so does
not supply this object's comparison. It was not used; no signature was weakened.
Loogle reported an `Adjunction.extEquiv` in `Ext.MapAdjunction`, but the reported module
is absent from the pinned Mathlib checkout, so that search result cannot be used here.
LeanSearch was unavailable (HTTP 500), which was recorded as unavailable, not no match.

The literature was read at Stacks Tags 03F3 and 09AX. The first supplies the restricted
injective-resolution argument; the second motivates the subsequent neighbourhood
application and is not required for the Ext-algebra reduction. Blueprint searches for
03F3, identity generator, and restriction unit found no matching imported blueprint node.

## New nodes

`def-weil-pbc-etale-open-object-cohomology-map` records the real construction in
`Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap`: the lifted free sheaf functor,
the identity-generator section, its adjoint sheaf morphism, and the induced Ext map.

`lem-weil-pbc-etale-open-object-cohomology-map-bijective` records the single-open
bijectivity obligation in `Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMapBijective`.
Its docstring and node give the restricted-resolution proof and identify the constructed
map degreewise by the free/Yoneda and constant-sheaf adjunctions.

`lem-weil-pbc-etale-open-free-sheaf-unit-coherence` records the degree-zero identity in
`Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafUnitCoherence`. Its docstring and node explain
how to evaluate the open-restriction unit identity on the generator and cancel the
identity comparison. This is precisely the remaining generator step; the transport from
it to all cohomological degrees is already proved in the item's module.

The additive construction is documented in
`coord/changes/etaleOpenObjectCohomologyMap.md`; it changes no existing definition or
statement used by the targets.

## Second reading by F2

1. I compared the delivered target module with the repository version. The theorem
   `AlgebraicGeometry.etaleOpenObjectCohomology_natural` has the same signature,
   hypotheses, and conclusion byte for byte; only proof imports, a private proof helper,
   and the proof body changed. Verdict: pass.

2. I compiled all four delivered modules with `lcompile.py --all`. They compile without
   errors or warnings. The target theorem has no `sorry`; the only remaining holes are
   the two named public split theorems, each with a matching node and a complete source
   proof description. No definition contains `sorry`, and no forbidden declaration or
   explicit axiom occurs. A scratch `#print axioms` check for all four construction
   definitions returned only `propext`, `Classical.choice`, and `Quot.sound`; the two
   split theorems and the target additionally use `sorryAx`, as reported. Verdict: pass.

3. I checked the new statements against their constructions and edge cases. The
   bijectivity obligation concerns one fixed explicit map and asserts no naturality;
   the unit-coherence obligation is a degree-zero equality of the displayed sheaf maps.
   Both are strictly smaller than the original theorem and are true for equal and empty
   opens. Searches of the library and pinned Mathlib found no existing declarations that
   supply either result. I independently ran LeanFinder on the derived evaluation
   comparison, Loogle on adjunctions and Ext, and grep on free Yoneda and constant-sheaf
   naturality. Loogle's `Adjunction.extEquiv` is absent in the pinned checkout. The
   upstream `mapExtCounit_bijective` has the opposite adjunction orientation and does
   not itself establish this generator map's bijectivity. I also read Stacks Tag 03F3:
   its restricted injective-resolution argument supports the bijectivity proof plan.
   Verdict: pass.

4. I checked the proof from the top down. The target uses the explicit map, its
   bijectivity, the degree-zero generator coherence, and the existing Ext composition
   comparison. Removed imports are listed under `## No longer needed`; the new imports
   are proof-only where appropriate, and the unit route remains represented in the DAG.
   Verdict: pass.

5. I checked the target and new node records against the Lean declarations. Their
   `proof`, `proof_deps`, and `proof_origin` describe the actual reduction, and the
   unit `sk-thm-p1` has unchanged `realized` fields. This auxiliary node is not itself
   one of its realized statement or step nodes, and the reduction bypasses none of
   those nodes. Verdict: pass.

I restored the original single space before the target theorem's `:=` so its signature
is byte-for-byte unchanged, and added this review record. No mathematical statement,
definition, or proof body was altered during the second reading.
