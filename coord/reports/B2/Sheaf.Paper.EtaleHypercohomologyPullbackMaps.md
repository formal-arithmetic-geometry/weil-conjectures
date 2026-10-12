## What changed

Reduced `AlgebraicGeometry.Etale.exists_etaleHypercohomology_pullback_maps` to two
strictly separate arguments, in new modules:
`Sheaf.Paper.EtaleHypercohomologyFilteredResolutionMaps` supplies the filtered CE construction
and computes its abutment by a concrete map of global-section complexes;
`Sheaf.Paper.EtaleKInjectivePullbackAbutment` identifies that concrete map with the canonical
unbounded derived-adjunction unit followed by Leray and the coefficient map.

The parent proof constructs the K-injective lift itself using the proved
`CochainComplex.IsKInjective.precomp_bijective_of_quasiIso`, lifts its homotopy class to a
chain map by quotient surjectivity, and supplies the augmentation homotopy. A proved private
lemma establishes naturality of `globalSectionsUpperStarMap` using the underived adjunction
unit and the terminal-section comparison. The parent constructs the global-sections chain
map directly and proves its chain-map equation from this naturality and `j.comm`. It rewrites the
concrete abutment formula using the comparison theorem and the original hypothesis `hP`.
It proves compatibility with consecutive filtration-step inclusions by cancelling the
monic target step inclusion and using `Subobject.ofLE_arrow`. It then applies stable-page
compatibility. All existing declaration signatures and definitions are unchanged.

The original module's public imports are unchanged. The second reading removed the unused public
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` import from the filtered child. Its proof imports now contain only
the two new lemmas and `Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`. Updated its
node's proof, proof dependencies and proof origin. New modules retain relevant planned
proof dependencies, so the next worker has the CE, spectral sequence and Ext comparison APIs.

Read the item node, all its dependency statements and signatures, its unit record
`sk-prop-h2` (no realized nodes here), and the CE/filtered/global-section comparison code.
Mathlib searches were run through msearch: LeanFinder returned homology-sequence naturality;
Loogle returned spectral-sequence morphism definitions; grep returned no matching
hypercohomology pullback theorem. LeanSearch returned HTTP Internal Server Error and is
recorded as unavailable. The referenced Stacks .tex files are absent on this clone;
read the official Stacks pages 015J, 015K, 0EZM, 070G and 01F8 instead.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_pullback_maps`
(node `lem-weil-pbc-hypercohomology-pullback-maps`). Its complete proof compiles.

Added exactly two holes, each a public theorem with a complete proof in words and its node:

- `AlgebraicGeometry.Etale.exists_etaleHypercohomology_filtered_resolution_maps`
  (`lem-weil-pbc-filtered-resolution-pullback`), in
  `Sheaf.Paper.EtaleHypercohomologyFilteredResolutionMaps`.
- `AlgebraicGeometry.Etale.etaleKInjective_pullback_abutment`
  (`lem-weil-pbc-kinjective-pullback-abutment`), in
  `Sheaf.Paper.EtaleKInjectivePullbackAbutment`.

This is a decomposition: one upper hole closed, two lower holes added, net -1. No claim
of a sorry-free proof of the mathematical result is made. No hole remains in the parent,
no definition is added, and no data is chosen from an unproved mere-existence statement.

Edge checks: the comparison lemma allows unbounded K-injective representatives, requires
no quasi-isomorphism hypothesis on j or v, and works for every integer n. For v=0 and for
the zero complex its map is zero after passage to cohomology; for identity lifts it is the
canonical resolution comparison. In the filtered construction, negative row degree is
already zero in the presentation; stabilization is per bidegree, so arbitrary negative
complex lower bounds are allowed. The bound must simultaneously govern all maps between
presentations; the proof sketch uses the canonical stationary cycles/boundaries quotient,
not individually selected stable-page isomorphisms. Quantifying over any proof hc is safe
by proof irrelevance; hc itself is proved in the parent from ht and monicity.

## No longer needed

Removed the following direct proof imports from the parent:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`

The CE lift, inverse-image exactness, bounded filtered spectral-sequence and cohomology
pullback facts remain needed in the filtered-construction child; they are not globally
pruned. `HypercohomologyFirstPage`, `LowerShriek` and `UpperLowerStar.Defs` are already
available through the public statement imports. `KInjectiveResolutions` is not required
as a separate direct import: the statements use the existing generic resolution choice.
The module-sheaf existence theorem `etale_kinjective_resolutions_exist`
(node `prop-weil-pbc-kinjective-resolutions-exist`) is not used on this route: the parent
uses the generic K-injective comparison principle and the presentations already carry
resolution choices. Its separate module import is also omitted in the construction child.
No claim that these modules are outside every other target's closure is made.

The old direct `proof_deps` omitted from the parent are:
`lem-weil-pbc-cartesian-eilenberg-functorial`, `thm-sp-spectral-object-yields`,
`thm-sp-if-e1`, `prop-weil-pbc-inverse-image-exact`,
`def-weil-pbc-cohomology-pullback`, `def-weil-pbc-etale-cohomology`,
`prop-weil-pbc-kinjective-resolutions-exist`, `def-weil-pbc-kinjective-resolutions`,
`lem-weil-pbc-cohomology-pullback-functorial`, and
`def-weil-pbc-termwise-hypercohomology-presentation`. Except for the unused
module-sheaf resolution existence theorem, these remain relevant through the child proof
plans or the public statement imports. `def-weil-pbc-inverse-image` remains a direct dependency.
The filtered child also drops its unused public `Derived.UpperLowerStar` import.

## Where the brief, the DAG or earlier work was wrong

The listed `cohomologyPullbackFunctorial` declaration proves naturality/composition in the
Ext encoding; its signature does not provide the row-resolution computation asserted in
the original step 2. Likewise `boundedFilteredComplex_spectralSequence` is a general
filtered-complex API, not a packaged étale CE presentation or the derived unit comparison.
The new filtered construction states this missing glue explicitly; its natural-language
proof includes the constant-integer/global-sections comparison needed for the first page.

The existing `derivedCohomologyPullback_eq_derivedUnit` is on D+ and uses the bounded-below
derived functor, whereas this item's hP uses the unbounded derived adjunction and its Leray
comparison. The new comparison lemma states precisely the unbounded computation, including
canonical resolution isomorphisms, instead of silently treating these APIs as definitionally
equal. The construction of bounded-below CE resolutions additionally requires shifting the
degree-zero existence theorem before shifting back; the child node records this step.

## New nodes

`lem-weil-pbc-filtered-resolution-pullback` records the CE/filtered construction, with E1
comparison and stable-page quotient maps, ending at the concrete global-sections resolution
map. It explicitly accepts any lift j over v and any chain map w with the prescribed components;
it does not identify its abutment with a derived unit. Its source is 015J/015K and the spectral-sequence use in 0EZM.

`lem-weil-pbc-kinjective-pullback-abutment` records the resolution-level computation of the
unbounded unit--Leray map. It has no spectral sequence or filtration in its conclusion.
Its source is the K-injective comparison/preservation lemmas 070I/08BJ and the functorial
RΓ recipe 01F8/01F9/01FA/08J6. The parent's route is their combination plus the proved
lifting, global-sections naturality and monicity arguments. No change record is needed: no existing interface changed.

## Second reading by B2

1. I compared the delivered parent module with the repository baseline. Existing declaration
signatures and definitions are unchanged; only proof imports, a private naturality lemma, and
proof terms changed. The two added theorem declarations are new nodes with matching Lean
statements.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile without
errors or warnings. The parent hole is closed. The only remaining holes are the two named
public split theorems, each with a source, proof docstring, and matching DAG node. No
axiom, unsafe, opaque, extern, implemented_by, or hollow definition was added.

3. The split statements are strictly smaller than the parent: the filtered-resolution theorem
constructs presentations and a concrete resolution-level comparison, while the K-injective
theorem identifies that comparison with the derived unit--Leray map. Neither restates the
parent theorem. Their edge cases and quantifiers are recorded in the report above, and the
searches found no existing declarations duplicating them.

4. The proof follows the unit route through the filtered construction, K-injective comparison,
and abutment identification. The parent no longer directly imports the nine modules listed in
`## No longer needed`; the child retains the imports required by its statements and proof.
No unit `realized` field is altered.

5. The DAG proof, proof dependencies, origins, and Lean declarations agree with the proof
and imports. The new nodes carry the required source, blueprint, and creation metadata.

I removed the unused public `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`
import from the filtered child and recompiled it successfully. I completed the old dependency
node pruning list above. No Lean statement or proof term was altered during review.

Second-reader searches used different queries: LeanFinder on right-derived naturality for
K-injective resolutions returned ordinary injective-resolution naturality results;
Loogle on `CategoryTheory.Functor.rightDerived` returned ordinary degreewise derived-functor
APIs; grep on derived-resolution comparison and filtered spectral naturality found no exact
match. Repository searches confirmed the existing derived-unit computation is on D+, not
this unbounded resolution-level equation. I checked the cited Stacks
[015J](https://stacks.math.columbia.edu/tag/015J),
[015K](https://stacks.math.columbia.edu/tag/015K), and
[08BJ](https://stacks.math.columbia.edu/tag/08BJ) against the mathematical reductions.
