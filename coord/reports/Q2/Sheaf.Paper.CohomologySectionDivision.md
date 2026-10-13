## What changed

Proved AlgebraicGeometry.exists_cohomologySection_division without changing its
signature or any definition. Added the proved generic theorem
AlgebraicGeometry.RingedSpace.openModuleCohomology_map_isIso_of_overFunctor in
Sheaf.Topology.OpenModuleCohomologyLocalIso, imported only for the proof.
The helper constructs the restricted injective resolutions explicitly and uses
Mathlib comparison-map naturality to prove local-isomorphism invariance.
The main proof obtains a free generator from nonvanishing_section_trivializes,
uses the proved tensor-section lemmas to obtain a local isomorphism for every
power, and constructs q as inverse additive equivalence after restriction.
Transition compatibility is proved by the sectionwise multiplication identity,
naturality, and injective cancellation. Updated both DAG proof records.

Both modules compile cleanly through lcompile.py --all. No target signatures,
public imports of the original module, or existing definitions were changed.
The helper uses a local 800000-heartbeat allowance for comparison of composed
section and complex functors; its single-file compile is below 60 seconds.

## Proved and sorry left

Closed 1 original hole:
AlgebraicGeometry.exists_cohomologySection_division
(lem-sc-cohomology-section-division).

Added 0 holes. The new theorem
AlgebraicGeometry.RingedSpace.openModuleCohomology_map_isIso_of_overFunctor
(lem-sc-open-module-cohomology-local-iso) is also proved in full.
No sorry remains in either delivered module. This is a proof, not a decomposition.
Existing dependencies are used as provided; this delivery does not claim that
the entire targets' import closure is sorry-free.

## No longer needed

No modules or nodes are pruned. The direct proof import
Sheaf.Topology.RestrictInjectiveResolution in the original module is replaced
by Sheaf.Topology.OpenModuleCohomologyLocalIso; restriction of injective
resolutions remains used by that helper and its node remains transitively needed.
All three original public imports remain necessary for the unchanged statement.
The original nonvanishing-section dependency remains used. No unit statement
or realized step is bypassed (sk-thm-curveestimate realizes thm-sc-proper-cohomology;
this item is below that unit statement).

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The plan's step from restricted injective
resolutions to the specific openModuleCohomology map lacked a named interface.
The new helper proves that bridge, including naturality of the comparison maps;
no unstated cohomology identification is assumed.

Checked the source online because the local Stacks .tex files are absent:
[Tag 01E1](https://stacks.math.columbia.edu/tag/01E1),
[Tag 01CY](https://stacks.math.columbia.edu/tag/01CY), and the canonical map in
[Tag 09MR](https://stacks.math.columbia.edu/tag/09MR).
The local-invariance assertion uses 01E1. The original division statement uses
only local trivialization and does not need the quasi-coherence or qcqs
hypotheses of the global fraction-comparison isomorphism in 09MR.

Searches: LeanFinder returned local bijectivity and sheaf-isomorphism criteria;
Loogle returned AddEquiv.ofBijective and its inverse laws; grep found the proved
free-generator/tensor-section and resolution-naturality infrastructure, but no
existing local-isomorphism lemma for openModuleCohomology. LeanSearch returned
Internal Server Error and is recorded as unavailable, not as a negative result.

## New nodes

lem-sc-open-module-cohomology-local-iso, in
 dag/nodes/sec-curve-estimates/lem-sc-open-module-cohomology-local-iso.json,
records the proved theorem on arbitrary ringed spaces and arbitrary module
morphisms whose over-site restriction is an isomorphism. Its conclusion is only
the cohomology isomorphism, not construction of division maps or their transition
compatibility. Its docstring and node give the full comparison-map argument.
For the empty open it applies to the same restricted resolutions and zero section
groups; p = 0 is included without a special hypothesis. It has no exponents or
invertible-module assumptions. These edge cases impose no exception on the proof.
No change record is needed: there is no existing interface change or adaptation.

## Second reading by Q2

1. Interface check: PASS. Read the complete diff against the repository's original
   CohomologySectionDivision.lean. The existing theorem signature is byte for byte
   unchanged; no definition, hypothesis, conclusion, visibility, or public import
   changes. The only import replacement is a proof-only import. The other delivered
   module is new and has its own new theorem node. No forced adaptations or interface
   change records are needed.
2. Proof check: PASS. Independently compiled both delivered modules in import order
   using lcompile.py --all: clean, 35.4 seconds and 6.5 seconds respectively. Scanned
   both files: no sorry, axiom, unsafe, opaque, implemented_by, extern, or skipped
   kernel checking. A scratch module importing the sandbox outputs printed axioms
   for exists_cohomologySection_division and
   openModuleCohomology_map_isIso_of_overFunctor: each uses exactly propext,
   Classical.choice, Quot.sound; neither uses sorryAx. Read the restricted-resolution
   construction: it constructs the complex and augmentation explicitly, and obtains
   only the injectivity proof from restrict_injectiveResolution. It does not select
   arbitrary data from an unproved existence statement. The division map is explicitly
   the inverse of a proved additive equivalence composed with restriction.
3. New statement check: PASS. No statements were split off with sorry. The fully
   proved helper is strictly the local-invariance step, with no division maps,
   tensor exponents, or transition compatibility hidden in it. Checked U empty,
   p = 0, n = 0, b = 0, W empty, and a zero section: the arguments and signatures
   admit these cases without an extra assumption. Its source and complete comparison
   argument are in its docstring and node. Independently searched LeanFinder for
   derived sections inverting a morphism after open restriction, Loogle for
   CategoryTheory.Functor.rightDerived, and the project and pinned Mathlib sources
   for cohomology/restriction and comparison naturality. The hits provide the existing
   sectionwise-isomorphism and derived-functor infrastructure, not this local-invariance
   statement. An initial unqualified Loogle comparison-map query was not recognized;
   it is not counted as a mathematical negative. Read Stacks
   [01E1](https://stacks.math.columbia.edu/tag/01E1) and
   [01CY](https://stacks.math.columbia.edu/tag/01CY), confirming the locality and
   trivialization arguments used here.
4. Route and pruning check: PASS. Read the proof from the original hole downward:
   local free generator, existing tensor-section bijectivity, restriction of
   injective resolutions and Mathlib comparison naturality, then inverse and
   naturality cancellation. Found no shorter existing theorem replacing the helper.
   All public imports serve the unchanged signatures; all additional imports serve
   proofs and use plain import. Checked the old proof_deps: nonvanishing trivialization
   and open cohomology remain direct dependencies, and restricted injective resolution
   remains a dependency through the new helper. The report's No longer needed section
   accounts for this import replacement; no dependency module is pruned. Read
   dag/units/sk-thm-curveestimate.json: its realized statement is
   thm-sc-proper-cohomology and it has no realized steps. This subordinate change
   does not bypass or change that unit route.
5. Node check: PASS. Compared the existing node's diff and read the complete new
   node. The existing node changes only proof, proof_deps, and proof_origin. Its
   proof describes the actual free-generator, inverse-equivalence, and cancellation
   argument. The new node records the explicit restricted resolutions, both
   comparison naturality identities, and the homology-factorization argument.
   Each proof_deps list is the union of its steps' uses; the referenced nodes and
   their Mathlib or project declarations exist. The new node has the required
   source, searches, origin, created, blueprint, chapter, unit, and verbatim Lean
   signature fields. Neither statement is weakened.

Changes by the second reader: added this independent review and its axiom/search
verification. No Lean proof, signature, import, or node repair was necessary.
The delivery closes the one original hole and adds zero holes; the extra helper
is proved, not split off with sorry.
