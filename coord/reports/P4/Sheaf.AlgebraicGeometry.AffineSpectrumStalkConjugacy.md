## What changed

Reduced the single sorry in Sheaf.AlgebraicGeometry.AffineSpectrumStalkConjugacy
without changing any existing signature or public import. Added the proof-only
import Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport.

The main module proves normalization of stalkComparison through the exact derived
stalk functor from the chain-map naturality theorem and Coordinates.represents.
It uses the new source-only transport, naturality at the actual coefficient map,
and cancellation of the specified affineSpectrumDerivedPullbackIso to prove the
commuting square. It constructs the target isomorphism from c.e', d.e' and a
natural derived-stalk isomorphism, then uses Arrow.isoMk. Elaboration options are scoped to individual proof declarations, so the original
module interface is unchanged. A small proved private
categorical helper assembles the normalization equations without repeatedly
unfolding the cohomology models during rewriting.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.SingleComplexBaseChange.nonempty_affineSpectrum_stalkComparison_arrow_iso
(lem-pc-affine-spectrum-stalk-conjugacy).
There are no sorries left in the item's module.

Added one hole:
AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_comparisonIntoPullback_transport
(lem-pc-affine-spectrum-comparison-source-transport), in the new module
Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport.

This is a decomposition, not a net reduction in holes. The remaining theorem
concerns only the source comparison into derived pullback. It has no K', phi,
Coordinates, target complex N, chain map t, represents equation, hN, or final
arrow isomorphism. The main proof supplies the omitted coefficient and target
argument in Lean. The remaining theorem is stated for independently supplied
K-flat input representatives and includes a natural transformation, so its
naturality can actually be used in the main proof.

The private helpers spectrum_stalkComparison_normalized and
square_of_normalizations are proved, with no holes.

## No longer needed

No existing import was removed: all three original public imports are needed by
the unchanged signature. No original planned dependency can be declared globally
pruned by this delivery. In particular, the stalk-pullback formula, exactness of
stalks, base-derived cohomology model and pullback composition are still needed
inside the new source-only transport node. Their explicit uses were moved there,
not discarded. The original node now records only the dependencies used by its
actual assembly proof. Specifically, these old direct proof dependencies are no
longer used directly by that proof:

- lem-weil-pbc-module-stalk-pullback;
- def-pc-base-derived-tensor-cohomology-model;
- lem-weil-pbc-module-stalk-exact;
- lem-pc-ringed-spaces-derived-pullback-composition.

All four remain dependencies of the new source-transport node; no module is
pruned from the targets' import closure. hN is not used by the proof, but its
binder is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan describes correct mathematical transports, but the
same-square source-transport and pullback-naturality declarations do not directly
supply transport between the original square and the spectrum square. The new
node isolates that missing cross-square argument before postcomposition by phi.
The target representative equality is stronger than necessary: exact derived
stalks and the target representative isomorphisms suffice for the target transport.

No statement is disputed, weakened, or changed. No definitions, other workers'
modules, or target statements were changed. The unit realized fields are empty;
the affine-reduction route of the original node is retained.

The source pages for Tags 0DJ8, 0098 and 0D5S were read online. This clone contains
only the literature lists, not the cited Stacks or blueprint texts. The detailed
source-only expansion is marked as an agent argument in proof_origin. LeanSearch
returned Internal Server Error; that search is recorded as unavailable. LeanFinder,
Loogle, Mathlib grep, library grep and whole-blueprint node searches found no exact
existing statement of the source-only transport.

## New nodes

lem-pc-affine-spectrum-comparison-source-transport, in
 dag/nodes/sec-picard-framework/lem-pc-affine-spectrum-comparison-source-transport.json,
states the spectrum transport of comparisonIntoPullback before a coefficient
morphism. Its module carries one public theorem with exactly `:= by sorry`, a
source citation and complete proof in words. Source transport respects arbitrary
representative isomorphisms e and e0; no comparison invertibility is assumed.

Edge cases: an empty X' gives no z0. Zero complexes and zero cohomology produce
zero comparison arrows and zero-object isomorphisms; invertibility of a horizontal
comparison is never inferred. Arbitrary unbounded complexes and arbitrary integer
degrees are covered by exact scalar equivalences and derived functoriality, with
no boundedness, base-flatness or quasi-coherence added. The original node copy
updates only proof, proof_deps and proof_origin. No change record is required.

## Second reading by P4

1. Interface: compared the complete main-module diff and extracted the existing
   theorem signature through its `:=`. It is byte-for-byte identical. All three
   original public imports remain. The only added public theorem is in the new
   module; no existing definition, instance, target, or other module is changed.
   Verdict: pass.

2. Proof: compiled both modules through lcompile.py in import order (56.0 s and
   43.4 s, no errors or warnings). Read the normalization proof, the cancellation
   of affineSpectrumDerivedPullbackIso, naturality at phi, and Arrow.isoMk's
   square. Only isomorphisms on the vertical sides are cancelled. The item has
   no sorry; the new module has exactly the reported named theorem with
   `:= by sorry`. No forbidden declaration or hollow definition occurs. The
   existential witnesses T and l are eliminated only inside the proof of
   Nonempty; no data definition chooses an arbitrary unproved witness.
   Scratch #print axioms checks permit only propext, Classical.choice, Quot.sound,
   and sorryAx from the open dependency. Verdict: pass as a decomposition,
   not as an axiom-free proof of the target.

3. Split statement: read the full new signature and its docstring against the
   definitions of comparisonIntoPullback and affineSpectrumDerivedMorphism.
   The source isomorphism is needed before postcomposition by the coefficient
   map. The natural isomorphism T is needed on all morphisms to use naturality
   at phi; an unrelated pointwise target isomorphism would not suffice.
   Arbitrary e and e0 are legitimate: after the canonical exact pullback
   identification, their ratio is a derived automorphism of the input.
   Source transport for this automorphism is linear over A and B, hence over
   their tensor algebra, and extends to C. This accounts for the otherwise
   potentially incompatible representative choices. Empty Xprime has no z0;
   zero representatives have zero sources and targets; negative and positive
   degrees use exact functors without boundedness. No Tor-independence or
   invertibility of comparisonIntoPullback is used. The new theorem is strictly
   the source/counit part: it omits Kprime, phi, target coordinates, their chain
   map and represents equation, and the arrow-category conclusion.
   Independently searched LeanFinder for derived change-of-rings transport,
   Loogle for mapDerivedCategoryFactors, Mathlib grep for scalar equivalences,
   and lean/Sheaf and lean/WeilConjectures for comparisonIntoPullback and spectrum
   transport (queries logged in searches.jsonl). ExactFunctor localization
   factors are building blocks only. The proved coordinate-invariance module
   concerns one fixed square; OpenComparisonIntoPullbackTransport concerns an
   open restriction, not simultaneous spectrum replacement of all four schemes.
   Neither supplies this statement. Its full formalization is substantial and
   cannot be closed by a short application of those declarations.
   Read Stacks Tags [0DJ8](https://stacks.math.columbia.edu/tag/0DJ8),
   [0098](https://stacks.math.columbia.edu/tag/0098), and
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S). The source-only generalization
   is an agent argument from the stalk formula and derived functoriality;
   it does not apply the quasi-coherent affine-global-sections calculation of
   0DJ8 to arbitrary sheaves. Verdict: true, needed, and a proper subargument.

4. Route and pruning: the main proof actually carries out target normalization,
   naturality and coefficient cancellation. Its normalization helper also
   occurs privately in StalkComparisonCoordinateInvariance, so it is not a
   reusable public declaration; importing that module would not replace it.
   No shorter public route was found. The original public imports and the new
   proof-only import are used. In the new module the imports supply the spectrum
   definitions, comparisonIntoPullback, and Arrow in its public signature.
   The four removed direct DAG dependencies are now listed explicitly under
   No longer needed; all remain in the new node, so no closure pruning is claimed.
   Read dag/units/sk-thm-picard-semicon.json: realized.statement and its sole
   realized step are empty, and the existing affine-reduction route is retained.
   Verdict: pass.

5. Nodes: compared existing JSON field by field; only proof, proof_deps, and
   proof_origin differ. Both dependency lists equal the union of the uses in
   their proof steps. The original Lean statement record is unchanged; the new
   node's Lean statement is verbatim in its module. Its source, proof sketch,
   searches, creation record, blueprint ancestry, chapter, unit and Lean record
   are present. It records the missing cross-square transport rather than a
   duplicate of the full arrow-conjugacy theorem. Verdict: pass.

Second-reading changes: completed the pruning report with the four removed direct
proof dependencies and added this independent review. No Lean proof or signature
needed repair. One original hole is closed and one strictly smaller hole is added;
net reduction is zero and no module is pruned.
