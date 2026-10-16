## What changed

The original module proves `CategoryTheory.cartanEilenberg_canonical_truncation_comparison`
with its existing signature unchanged. Its proof factors the comparison through a concrete
mapping-cone spectral object of the decalage tower, then combines the normalized sequence
comparison and the CE spectral-object comparison. The composition and its page-two
naturality square are complete Lean proofs. A private proved helper transports spectral-object
isomorphisms to sequence isomorphisms using `exists_pageTwo_functor` and proves the required
normalization. The original public imports and statement are unchanged; its theorem proof docstring
now describes the implemented route.

Four new modules supply proved constructions and compatibility results:

- `FilteredComplexDecalageTower` constructs the actual tower, its functor on filtered maps,
  and its mapping-cone spectral object. The finite tower index q is Dec(F)^(1-q), with zero
  and the full complex at the infinite endpoints. It proves the shifted-image universal
  property of decalage, the cone-to-cokernel quasi-isomorphism on every interval, and
  naturality of interval cohomology with the specified quotient maps.
- `DoubleComplexTruncationDecalage` proves that the total of a horizontal smart truncation
  is isomorphic to the corresponding decalage step of the second filtration. This includes
  a real inverse: diagonal projections lift to the boundary cycles and sum to the inverse.
  The comparison commutes with the total inclusion and every specified filtered lift of a
  bicomplex map. Negative cutoffs and negative total degrees are included.
- `DerivedInjectiveResolutionNaturality` proves naturality of the inverse derived-functor
  unit on bounded-below injective complexes, constructs the comparison for a specified
  quasi-isomorphism into such a complex, and proves its augmentation-square
  naturality at the level of whole derived objects and on cohomology. It proves
  the cone quasi-isomorphism theorem by localizing a triangle map and applying
  the triangulated five lemma, constructs bounded-below cones and their functor
  on arrows, and proves injectivity of their terms. Natural isomorphisms for
  whole diagrams of specified resolutions and of interval cone resolutions
  are constructed as well.
- `DerivedUpperTruncationComparison` proves the unique normalized isomorphism from the
  localization of a cochain upper truncation to the canonical derived upper truncation.
  It constructs the isomorphism from that proved unique characterization and proves
  naturality in complex maps and in maps between cutoffs commuting with the inclusions.
  The same existence, uniqueness, normalization and naturality are proved in the
  bounded-below categories used by the derived functor. Actual cutoff maps and
  finite-cutoff towers are constructed, and their whole-tower comparison is proved
  natural also in complex maps.

The CE comparison module additionally proves
`cartanEilenberg_truncatedAugmentation_square` for maps between cutoffs and
`cartanEilenberg_totalAugmentation_square` for normalized total augmentations.
These close the augmentation-square compatibility steps of its plan.

Edge cases of the new interfaces were checked mathematically before stating them:
constant zero or full filtrations give zero finite-page terms on both sides; the
comparison asserts no convergence without boundedness. In the first-quadrant
truncation comparison, negative cutoffs and negative total degrees give zero
objects, and the finite diagonal sums are empty where required. The Lean proofs
quantify over all integer degrees and cutoffs without positivity hypotheses.

Two remaining comparisons have separate modules and nodes, documented below. No existing
module other than the assigned item is changed, and no existing definition or signature is
changed. All new definitions are constructions or choices from proved unique characterizations.

Validation: all seven modules compile through the prescribed wrapper. The dry run
passes compilation and axiom probes; the initial stage-3 preflight required the
independent second-reading section appended below. Nothing was pushed by the first worker.

## Proved and sorry left

Closed: the one original hole in
`CategoryTheory.cartanEilenberg_canonical_truncation_comparison`.

Added, and still open:

- `CategoryTheory.filteredComplex_decalage_comparison`
  (`lem-sp-filtered-complex-decalage-comparison`). Still needs the actual quotient
  cycle/boundary isomorphisms on all pages, compatibility with the differential and
  successor homology isomorphisms, and the normalized page-two square. The interval
  cone-to-quotient quasi-isomorphisms and their naturality are already proved.
- `CategoryTheory.cartanEilenberg_decalage_spectralObject`
  (`lem-sp-ce-decalage-spectral-object`). Still needs assembly of the CE truncated
  augmentation comparisons into interval objects and connecting maps, including
  the full-total endpoint and the
  comparison of Q(F(J)) with RF(X). The total-truncation/decalage isomorphism, its
  naturality, normalized derived injective-resolution naturality, the derived
  comparison for whole diagrams of interval cone resolutions, and normalized
  cochain/derived truncation naturality are already proved. The remaining
  connecting-map step must match the three-cutoff cone triangles with the
  canonical derived truncation triangles, preserving their signs.

These are the only two `sorry`s in the delivered Lean files. Thus the upper comparison is
**decomposed**, not proved without new holes: one hole closed and two added, net minus one.
The four construction/API modules contain no holes. In particular the following are proved:
`decalage_factor_iff`, `decalageTowerConeToQuotient_quasiIso`,
`decalageTowerConeToQuotient_naturality`, `filteredComplexDecalageIntervalIso_naturality`,
`totalTruncLEToDecalage_isIso`, `totalTruncLEToDecalage_naturality`,
`homologyRightDerivedFunctorPlusObjQIsoOfInjective_naturality`,
`homologyRightDerivedFunctorPlusResolutionIso_naturality`,
`rightDerivedFunctorPlusResolutionIso_naturality`,
`rightDerivedFunctorPlusResolutionNatIso`,
`CochainComplex.mappingCone.quasiIso_map_of_quasiIso`,
`CochainComplex.Plus.mappingConeMap_quasiIso`,
`CochainComplex.Plus.mappingCone_injective`,
`rightDerivedFunctorPlusConeResolutionNatIso`,
`exists_unique_truncLE_Q_iso`, `truncLEQIso_naturality`, `truncLEQIso_of_le`,
`exists_unique_cochainTruncLE_Q_iso`, `cochainTruncLEQIso_naturality`, and
`cochainTruncLEQIso_of_le`, `cochainTruncationTowerQIso_naturality`,
`cartanEilenberg_truncatedAugmentation_square`, and
`cartanEilenberg_totalAugmentation_square`.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.Paper.CartanEilenbergLeftExactCohomology`
- `Sheaf.CategoryTheory.CartanEilenbergTruncationResolution`
- `Sheaf.CategoryTheory.LeftExactTruncationIso`
- `Sheaf.CategoryTheory.CartanEilenbergMappedTotal`
- `Sheaf.CategoryTheory.CartanEilenbergDerivedTruncationCohomology`
- `Sheaf.CategoryTheory.FilteredComplexDecalage`

The truncation-resolution, left-exact-truncation, mapped-total and decalage modules
remain used transitively by the new comparisons or constructions;
this is not a claim that their modules can be withdrawn globally.
`lem-sp-cart-eilenberg-left-exact-cohomology`, module
`Sheaf.Paper.CartanEilenbergLeftExactCohomology`, is no longer a dependency of this
route: the normalized comparison uses derived tower intervals, rather than a
separate split horizontal cohomology calculation. Other parents may still need it.
`lem-sp-ce-derived-truncation-cohomology`, module
`Sheaf.CategoryTheory.CartanEilenbergDerivedTruncationCohomology`, is also no longer
needed by this route. It gives unnormalized objectwise cohomology isomorphisms; the
new normalized derived-object comparison supplies the needed computation and maps.
Its proof import was also removed from the new CE comparison module.
The original node's proof and proof dependencies are updated to the implemented
route. No module is withdrawn.

For completeness, the old proof dependencies absent from the new direct proof dependency
list are `lem-sp-ce-truncation-resolution`, `lem-sp-filtered-complex-decalage`,
`lem-sp-filtered-complex-canonical-model`, `lem-sp-left-exact-truncation-iso`,
`lem-sp-cartan-eilenberg-mapped-total`, `lem-sp-ce-derived-truncation-cohomology`, and
`lem-sp-cart-eilenberg-left-exact-cohomology`. The canonical-model module remains a public
statement dependency, and the truncation-resolution, decalage, left-exact-truncation and
mapped-total results remain transitive proof dependencies of the new comparisons.
`lem-sp-spectral-object-page-two-functor` remains a direct proof dependency.

The second reader also removed the redundant public imports
`Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor` and
`Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence` from the new tower module.
Its public `HomotopyCategory.ShortExact` import already exports both, and the definitions
require that import for the concrete cone-to-cokernel map. No proof-only import is public.

## Where the brief, the DAG or earlier work was wrong

The original plan's objectwise derived-cohomology theorem supplies only `Nonempty`
isomorphisms. Those cannot be chosen arbitrarily and then assumed natural. The
new inverse-unit comparison fixes a normalization and proves naturality for specified
augmentation squares. The remaining CE interface asks for a spectral-object
isomorphism, so compatibility with connecting maps remains an explicit obligation.

The concrete tower must use Dec(F)^(1-q) at q. Using Dec(F)^(-q) at q instead shifts
the interval by one: the interval (q,q+1) must be Dec(F)^(-q)/Dec(F)^(1-q), whose
cohomology in degree p+q corresponds to the original filtered E2 term (p,q).
The new construction includes the infinite endpoints explicitly. At tower index
q, the smart cutoff is q-1 and the normalized derived comparison therefore gives
the truncation strictly below q, matching the source library's Grothendieck
spectral object. The untruncated CE augmentation supplies the full endpoint.

The read-only blueprint ancestor script returns None for the assigned node because
its created.item is a stage-3 module name. The new nodes instead preserve its
recorded blueprint ancestry (thm-sp-grothendieck, through the three CE comparison
nodes). Blueprint searches for decalage, truncation and injective resolutions found
no statement identical to the new interfaces.

No existing statement is disputed or weakened. The unit record has no realized
steps bypassed by this route. The two remaining statements isolate different
parts of the argument: a universal filtered-complex comparison independent of CE,
and a CE derived-interval comparison independent of the canonical quotient sequence.

## New nodes

`def-sp-filtered-complex-decalage-tower`: the concrete tower and its spectral object,
with proved restriction, interval quotient and cohomology naturality APIs; module
`Sheaf.CategoryTheory.FilteredComplexDecalageTower`.

`lem-sp-filtered-complex-decalage-comparison`: the remaining universal sequence/page
comparison; module `Sheaf.CategoryTheory.FilteredComplexDecalageComparison`.

`lem-sp-double-complex-truncation-decalage`: the proved totalized smart-truncation
isomorphism and its naturality; module
`Sheaf.CategoryTheory.DoubleComplexTruncationDecalage`.

`lem-sp-derived-injective-resolution-naturality`: the proved specified-resolution
comparison and its naturality; module
`Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`.

`lem-sp-derived-upper-truncation-comparison`: the proved unique cochain/derived
truncation comparison and its complex-map and cutoff naturality; module
`Sheaf.CategoryTheory.DerivedUpperTruncationComparison`.

`lem-sp-ce-decalage-spectral-object`: the remaining coherent CE comparison on all
intervals and connecting maps; module
`Sheaf.CategoryTheory.CartanEilenbergDecalageSpectralObject`.

All six new nodes are in `dag/nodes/sec-abelian-varieties/`. No change record is
needed: no existing statement or definition is changed and no other group's module
is adapted.

## Second reading by G4

1. **Existing interface: pass.** I compared the assigned module with the read-only
   repository using `diff -u`, and separately compared the bytes from its existing theorem
   name through the colon-equals delimiter. The signature of
   `CategoryTheory.cartanEilenberg_canonical_truncation_comparison` is identical, including
   all universe, derived-category, additivity, left-exactness and filtration hypotheses,
   the quantification over every filtered lift, and the page-two square. Its four public
   imports are unchanged. The other six modules are new; no existing definition, target,
   or other group's module changes. The sole existing node changes only `proof`,
   `proof_deps` and `proof_origin`. No change record is needed.

2. **Proof and data: pass, with two declared holes.** I read all seven Lean files and
   compiled them in import order with the prescribed wrapper. The upper proof uses the
   universal quotient/decalage comparison and the CE spectral-object comparison, then
   genuinely composes their naturality squares. Its private helper derives the required
   normalization by conjugating the page-two functor and cancelling its inverse comparison.
   The four construction modules have no `sorry`. The only two holes are exactly the two
   public theorem names listed under `## Proved and sorry left`; neither is in a definition.
   I checked every `choose`: the tower restrictions are fixed by monic inclusions, the
   total-truncation factor is unique, and the truncation isomorphisms and cutoff maps are
   chosen from proved unique characterizations. The diagonal lifts used to construct the
   inverse exist by proved kernel calculations and have their inclusion equations proved.
   No arbitrary data is chosen from an unproved existence assertion. There is no forbidden
   axiom, unsafe/opaque declaration, implementation override, or external implementation.
   The delivery tool's axiom probe checks every delivered declaration; explicit scratch
   `#print axioms` checks additionally cover the upper theorem, both remaining holes and
   the principal constructions, normalization and naturality theorems. These show only
   propext, Classical.choice and Quot.sound for the supporting constructions and proofs;
   the two open comparisons and upper theorem additionally use the expected sorryAx.

3. **Split statements and sources: pass.** I read Stacks
   [015X](https://stacks.math.columbia.edu/tag/015X), second spectral sequence and filtered
   injective resolutions; [012K](https://stacks.math.columbia.edu/tag/012K), the cycle,
   boundary and differential formulas; [015K](https://stacks.math.columbia.edu/tag/015K),
   CE functoriality; [0118](https://stacks.math.columbia.edu/tag/0118), smart truncations;
   and [0156](https://stacks.math.columbia.edu/tag/0156), injective computations. The new
   interfaces are expansions of these constructions, not claims that Stacks directly
   states this Lean normalization. The universal hole has no CE or boundedness hypothesis;
   substitution in its numerator and both denominator terms gives the stated page shift.
   With n=p+q, tower interval (q,q+1) is Dec(F)^(-q)/Dec(F)^(1-q), so its cohomology
   matches E2 at (p,q). Its differential has the required bidegree (r,1-r).
   Zero/full filtrations have zero finite page terms. For a complex concentrated in degree n
   with its only graded piece at filtration p, the tower jumps at q+1=n-p+1;
   interval (q,q+1) therefore has bidegree (p,n-p), checking the one-step offset
   on a nonzero example. For the CE hole the step at q is
   the smart cutoff q-1, matching the source library's truncation strictly below q.
   Negative cutoffs and total degrees vanish in the first quadrant; equal interval
   endpoints have acyclic cones; the infinite endpoints are explicitly zero and the full
   total. No G-acyclicity assumption on F(J) is needed: the object being computed is
   RG(RF(X)), not the derived functor of the composite. The two holes isolate independent
   quotient-page and CE-derived-interval arguments; neither repeats the upper statement.
   I expanded the interval proof documentation to explain uniqueness by t-structure
   orthogonality before RG and how the triangle squares fix connecting-map signs.

   I searched again with the wrapper using the different phrases “Deligne shift of a
   decreasing filtration” and “mapping cones of a Cartan Eilenberg resolution truncation
   tower,” and with the Loogle pattern `CochainComplex.mappingCone.map, QuasiIso`.
   The results give generic shift, cone and truncation APIs, no complete comparison.
   A Mathlib grep for spectral-object/sequence isomorphisms in the homotopy-category
   directory found no replacement. Repository and upstream searches also found no such
   comparison. I read the existing `CartanEilenbergDecalageInjectiveModel` interface:
   it gives specified objectwise injective models at nonnegative cutoffs, but not the
   whole interval and connecting-map comparison. Neither remaining hole can be closed
   by a few-minute application of these APIs. Both have source/proof docstrings and nodes.

4. **Route and pruning: pass after cleanup.** I read the imported canonical model,
   decalage construction, truncation resolution, left-exact truncation and mapped-total
   interfaces, and the page-two functor. The implemented reduction uses their actual
   normalization equations; no arbitrary objectwise cohomology isomorphism is assumed
   natural. The two independent comparisons are needed for this reduction. The report
   accurately counts it as a decomposition: one old hole closed, two new holes added,
   net minus one, and no globally withdrawn module. I made `## No longer needed` name
   every removed old direct proof dependency, including the canonical model retained as
   a statement dependency, and distinguished transitive uses. I removed two redundant
   public imports from the new tower module: `HomotopyCategory.ShortExact` already exports
   `HomologicalFunctor` and `ShiftSequence`. The remaining public imports supply statements
   or constructed definitions; planned proof-only imports are plain imports. I read
   `dag/units/sk-prop-av-pqf-finite.json`: its realized statement and sole realized step
   are empty. This delivery does not edit that unit or bypass a realized step; it retains
   the assigned node's recorded Grothendieck blueprint ancestry.

5. **DAG agreement: pass.** The parent node records exactly the two comparisons and the
   page-two functor assembly in its proof/dependency union. Each new node has its own
   declaration/module, source, ancestry, unit/chapter, creation record and actual search
   history. The tower node records concrete data and the cone/quotient APIs; the other
   four supporting nodes record the proved generic constructions and their naturality.
   The two open comparison nodes match the Lean hypotheses and conclusions and give
   complete mathematical proof plans. I updated the CE node's interval step together
   with its Lean proof docstring, explaining the normalization and sign obligation.
   No node falsely claims that either of these two Lean holes has been filled.

Changes from this reading: removed two redundant tower imports, expanded the CE interval
proof documentation and matching node step, completed the direct-pruning inventory, and
added this independent review. No statement or definition body changed, and no additional
hole was introduced or closed by the second reader.
