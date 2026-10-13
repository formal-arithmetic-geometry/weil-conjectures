## What changed

Replaced the sole sorry in
Sheaf.AlgebraicGeometry.AffineAlgebraCanonicalComparisonIdentification with a
complete proof from two strictly smaller affine assertions. Added proof-only
imports of AffineAlgebraKInjectiveCycleClassEpi and
AffineAlgebraKInjectiveBoundaryExactness. No existing signature, definition,
visibility, or public import changed; no other existing module was adapted.

The proof uses the affine cycle-class epimorphism and exactness of the
boundary/cycle/class short complex. Mathlib's Exact.gIsCokernel combines them
into preservation of the degree-n cokernel. The right adjoint preserves the
outgoing-differential kernel, giving pointwise left-homology preservation.
A proved private helper comparison_of_preserved_left_homology then constructs
Mathlib's canonical mapHomologyIso and identifies its hom with the counit mate.
Its proof uses explicit LeftHomologyMapData with counit components, the
mapHomologyIso_eq formula, the adjunction bijection and inverse cancellation.
This formal calculation is independent of schemes, affine vanishing, or
K-injectivity. In particular the theorem is not one application of a renamed
existential-isomorphism statement.

## Proved and sorry left

Closed AlgebraicGeometry.affine_algebra_kinjective_canonical_comparison_identification
(blueprint: new-affine-algebra-canonical-comparison-identification).
The item's module has no sorry. Its new private helper
AlgebraicGeometry.comparison_of_preserved_left_homology is fully proved.

Added exactly two named public holes, each in its own module:

- AlgebraicGeometry.affine_algebra_kinjective_cycle_class_epi
  (new-affine-algebra-kinjective-cycle-class-epi), in
  Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCycleClassEpi.
- AlgebraicGeometry.affine_algebra_kinjective_boundary_exactness
  (new-affine-algebra-kinjective-boundary-exactness), in
  Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveBoundaryExactness.

This is a decomposition: one upper hole closed, two lower holes added, net -1
before any closure changes from pruning. Neither new statement mentions P,
a, an isomorphism witness, or the canonical counit mate. The first asserts only
surjectivity of pushed cycle classes; the second asserts only exactness at
pushed cycles. Their combination into a canonical homology isomorphism and
its identification with the adjoint mate is proved in Lean here.

The set compiles with lcompile.py. New statements were checked mathematically
on empty schemes/opens, zero complexes, acyclic K-injective complexes (which
are contractible), the identity affine morphism, and complexes supported in
one degree. Empty and zero cases are zero-module assertions; contractible
complexes remain contractible under the additive direct-image functor.
No boundedness or restriction on the integer degree was introduced.

## No longer needed

No existing imports were removed. The original node's two planned dependencies
are not needed in the delivered proof or the new nodes' proposed route:

- lem-pc-affine-morphism-hi:
  WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism.
- lem-sc-qcoh-acyclic-derived-pushforward-cohomology:
  Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology.

The new geometric statements work directly on inverse images of affine opens,
using affine sections vanishing and the unbounded truncation bound. They do
not pass through higher direct images or sheafification of an arbitrary
natural comparison isomorphism. These are dependencies pruned from this
item's proof route; no claim is made that other targets stop reaching them.
AffineAlgebraKInjectiveCohomologyComparison is also not imported or needed:
its existential isomorphism does not specify the cycle-class map.

## Where the brief, the DAG or earlier work was wrong

The existing planned dependency qcoh_acyclic_derived_pushforward_cohomology
asserts only existence of a natural isomorphism. Its signature does not
characterize that isomorphism as the cycle-class comparison, so it does not
supply the canonical identification claimed by the original one-step plan.
An unrelated isomorphism cannot be substituted for the counit mate.
The delivered generic proof supplies the missing formal identification and
leaves the two concrete affine cycle calculations explicit.

The official sources were read at
[Stacks Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW) and
[Stacks Tag 08D4](https://stacks.math.columbia.edu/tag/08D4), since this read-only
checkout does not contain literature/stacks-project/perfect.tex. The new
proof descriptions expand the cycle-map identity: set A = smart upper
truncation at n and B = smart lower truncation of A at n. Both relevant
derived section maps are invertible on Hn; comparison with actual sections
at K-injective I and naturality identify their composite with the raw
projection of cycles to homology. Its surjectivity and kernel calculation
are the two remaining statements, not a choice of data from a holed
existence assertion.

The ancestor script reports None for the item because its earlier created.item
records use Lean module names instead of DAG ids. The new blueprint links
were recovered from the existing
lem-sc-affine-algebra-counit-homology-comparison-isIso ancestry, ending at
lem-sc-finite-duality. The existing item's blueprint fields were not changed.
The item's unit record has no realized statement or step nodes; no unit-level
statement, route, or realization was edited.

## New nodes

new-affine-algebra-kinjective-cycle-class-epi records the pushed cycle-class
projection's epimorphy. Its own module contains exactly one public theorem,
with unchanged geometric assumptions and a full proof in words. The proof
uses the surjective half of the canonical affine section comparison. This
is one part of the cokernel argument, not the upper theorem under another name.

new-affine-algebra-kinjective-boundary-exactness records exactness at pushed
cycles, without asserting surjectivity of the class map. Its own module
contains exactly one public theorem. The proof uses the injective half of
the raw section-cohomology comparison to lift a cycle with zero class to a
boundary. It remains independent of the chosen exact left adjoint.

Both nodes include LeanSearch (recorded unavailable), LeanFinder/Loogle and
source grep searches. Whole-blueprint cycle-class searches found no match.
Generic ShortComplex homology preservation and Exact.gIsCokernel were found
and used, rather than restated. The existing item's proof, proof_deps and
proof_origin were updated to match the delivered Lean. No change record is
needed because no existing interface was changed.

## Second reading by M3

1. Compared the delivered existing module with the repository using diff. Its sole
   existing theorem signature, docstring, visibility and public imports are byte
   for byte unchanged. Only proof-only imports, the proved private helper and the
   theorem proof were added. No definitions or target statements changed. Pass.
2. Compiled all three delivered modules locally with lcompile.py. A scratch copy
   with explicit #print axioms for all four declarations compiled: the private
   formal helper uses only propext, Classical.choice and Quot.sound; the target
   and two split statements additionally use sorryAx. Text inspection finds only
   the two listed whole named theorem holes and no forbidden declaration or
   hollow definition. Pass as a decomposition, not a completed geometric proof.
3. Read both split statements and their full docstring arguments against Stacks
   Tags 0AVW and 08D4. The N=1 bound kills the lower tail in degrees n and n+1;
   the smart truncation maps identify the resulting comparison with the actual
   projection of cycles. Empty opens, zero complexes, acyclic K-injectives,
   identity affine morphisms and single-degree complexes cause no exception.
   The separate epi and middle-exactness assertions are strictly partial and
   are exactly the inputs to Exact.gIsCokernel. Independent LeanFinder search
   for right-adjoint preservation on affine K-injectives and source rg searches
   for quotient surjectivity, exact cycles and homology preservation found no
   existing geometric result giving either assertion. Loogle confirmed the
   existing LeftHomologyMapData.homologyMap_eq used by the formal helper. No
   lower hole could be closed by an available short application. Pass.
4. Read the proof from the target down. The adjunction supplies kernel
   preservation; the two geometric assertions supply the missing cokernel
   preservation, and Mathlib supplies the homology isomorphism. The explicit
   counit naturality calculation proves its canonical mate identity. This is
   a real reduction and chooses no data from a mere unproved existence result.
   Both new imports are proof-only and used; public imports are needed for the
   signatures. The report names both old proof_deps absent from the new route.
   The unit sk-thm-picard-duality has empty realized statement and step lists;
   no unit route or realization was changed. Pass.
5. Compared all node records with the Lean signatures and proof. New nodes have
   their sources, complete proposed proofs, search records, creation/ancestry,
   chapter/unit and verbatim Lean statements. Corrected the parent's citation
   from derived-category bounded-below preservation to the existing Mathlib
   complex-cohomology node, which is what the proof actually uses. Added the
   existing open K-injective restriction node to each new proof route. Pass
   after these metadata repairs.

Second reading changed only the new docstrings and DAG proof metadata: made
explicit that restriction to U preserves K-injectivity by its exact
extension-by-zero left adjoint (Tag 08BS), and corrected the complex-level
homology-comparison citation. No Lean proof or existing signature was rewritten.
Holes closed: affine_algebra_kinjective_canonical_comparison_identification (1).
Holes added: affine_algebra_kinjective_cycle_class_epi and
 affine_algebra_kinjective_boundary_exactness (2). Net hole reduction is -1; no
existing module import was pruned.
