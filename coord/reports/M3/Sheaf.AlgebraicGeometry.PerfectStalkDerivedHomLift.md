## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift by a
compiling proof from a smaller derived-descent statement and the existing proved
perfect_affine_map_representative theorem. All existing public signatures and visibility
are unchanged. Added proof-only imports of PerfectOpenStalkDerivedHomDescent and
Modules.RestrictionStalkExtensionIso; no public imports changed. Two proved private helpers construct global/local derived stalk comparisons
and show that functors preserving zero morphisms and finite free objects preserve
strict perfectness; restriction is a specialization. The final equality is proved by
naturality of mapDerivedCategoryFactors and categorical associativity.

Added Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent, containing one public
intermediate theorem. This concerns only two perfect complexes on an affine open and a
derived morphism between their open stalks. It supplies a derived arrow, not a chain map;
it has no global complexes G,H or derived comparisons iG,iH. The original proof constructs
those comparisons and the chain representative separately. Updated the original node's
proof route and dependencies. The unit has no realized nodes here; its route is unchanged.

Repair of the returned duplicate-theorem finding: generalized the private helper in
place to map_strictlyPerfect_of_mapFree. It now accepts an arbitrary functor T between
the two open module categories, a PreservesZeroMorphisms instance, and finite-free
comparison isomorphisms. There is no inclusion V ≤ U hypothesis and T need not be a
restriction functor. The proof explicitly transports the boundedness and retractions;
the main theorem specializes it using mapFreeIso and overMapUnitIso. This is the
return's permitted generalization, with every binder explicit, not a renamed copy.
The existing restrict_strictlyPerfect_for_stalk_spread cannot be imported here: it is
private in PerfectStalkDerivedIsoSpread, which itself imports this item. No changes to
that module or other existing interfaces are necessary. The prior second reading has
been removed because it predates this repair; a new independent reading is required.

## Proved and sorry left

Closed AlgebraicGeometry.Scheme.exists_affine_perfect_stalk_hom_lift
(lem-sc-perfect-stalk-derived-hom-lift): 1 of 1 holes in the assigned module.

Added one hole: AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_derived_hom_descent
(lem-sc-perfect-open-stalk-derived-hom-descent). This is a decomposition, with net hole
change zero, not a claim that the whole stalk-lifting argument is sorry-free.
No sorry remains in the assigned module or its private helpers. No definitions, axioms,
or arbitrary data choices were introduced. All witnesses are confined to theorem proofs.

Both modules compile through lcompile.py. Zero complexes and zero free ranks are allowed;
x in U excludes an empty U, and no separation or Noetherian hypothesis is introduced.
The derived universes v and w remain independent.

## No longer needed

Removed direct imports of Sheaf.AlgebraicGeometry.AffinePerfectHomColimit,
Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations, and
Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence from the assigned module. These are
still needed by the new descent node and imported there, so none is claimed globally pruned.

Removed the unused direct import Sheaf.Algebra.Homology.ModuleStalkExact and its direct
proof dependency lem-weil-pbc-module-stalk-exact. Exactness needed here is supplied by the
proved finite-limit/colimit instances in OpenModuleStalkFunctor. The node may remain
reachable elsewhere; no claim of global pruning is made.

All remaining original proof dependencies are retained either in the main proof or the
new descent node. No unit statement or realized step was pruned.

## Where the brief, the DAG or earlier work was wrong

The original single prose step bundled stalk comparisons, finite-projective affine
transport, localization Hom descent, and chain-map representation. The latter two
interfaces cannot be applied directly to sheaf stalk objects: the affine Hom theorem
requires an explicit ring diagram, module complexes, and natural scalar-extension
identifications. The new node isolates that outstanding affine transport/descent work;
the comparison and chain-representative steps are now actual Lean proofs.

The cited literature tex files are absent on this machine. The cited proof was checked
at https://stacks.math.columbia.edu/tag/09RE and
https://stacks.math.columbia.edu/tag/0BC7. LeanSearch returned Internal Server Error;
that search is recorded as unavailable, not as evidence of no match. LeanFinder and
Loogle returned no theorem giving this derived stalk descent, and source searches
found only the ordinary stalk and restriction comparisons used in the proof.
The nearby exists_chainMap_of_stalk_local theorem requires finite free terms, whereas
IsStrictlyPerfect supplies finite-free retracts. It also uses pullback to the stalk spectrum
instead of the open module stalk functor, so it does not directly discharge the remaining
derived descent statement. Blueprint searches for perfect and stalk returned eight
unrelated etale/coefficient nodes, with no duplicate of the new lemma.

## New nodes

lem-sc-perfect-open-stalk-derived-hom-descent: the strictly smaller derived descent part
of the old proof. Its statement, source, numbered proof, searches and Lean signature
are in dag/nodes/sec-abelian-varieties/lem-sc-perfect-open-stalk-derived-hom-descent.json.
It retains the original affine Hom continuity, principal localization, and affine derived
equivalence route. No change record or forced adaptation is required.

## Second reading by M3

1. Compared the complete assigned module with the repository using diff, and separately
   compared the text from the existing theorem's name through its signature: byte-for-byte
   identical. The only existing-node fields changed are proof, proof_deps and proof_origin.
   No existing definition, visibility, public import, or target statement changes. Pass.
2. Independently compiled both delivered modules in import order with lcompile.py: no
   errors or warnings. The assigned module has no sorry; the new module has exactly its
   reported named theorem hole. A scratch copy with #print axioms confirmed that both
   private helpers use only propext, Classical.choice and Quot.sound. The main theorem
   and the descent theorem additionally use sorryAx, as reported. No forbidden declaration
   or hollow definition occurs. The isomorphism witnesses occur in theorem proofs only;
   neither helper chooses data for a public definition. Pass as a decomposition.
3. Read the new signature, docstring and node against Stacks Tags 09RE (affine proof)
   and 0BC7 (2). Bounded finite-free retracts give finite projective affine section
   complexes; localization at x is a filtered colimit of principal localizations. Hom
   surjectivity gives the stated derived arrow, with restriction-stalk comparisons.
   The conclusion stops before the chain representative, and removes the global models
   and their comparisons: it is strictly a part of the old argument. Empty U is excluded
   by hxU; zero complexes, rank zero, a one-point affine scheme, and independent derived
   universes introduce no exception. The private generalization transports zero objects
   and retract equations and requires no exactness of its arbitrary functor T. Repeated
   searches with LeanFinder (bounded projective maps descending to principal opens),
   Loogle (localization and Hom), and rg through both Lean roots found no duplicate of
   the new derived-descent statement. The existing PerfectOpenStalkChainMapLift accepts
   an actual chain map, not the input derived arrow; using it would still require a
   projectivity and chain-representative argument at the stalk. The previous duplicate
   restriction helper is genuinely generalized here to any zero-preserving functor with
   finite-free comparisons, as the return permitted. Pass.
4. Read the proof downward: local_model_stalk_comparison constructs the global comparison
   from the proved restriction-stalk-extension isomorphism and derived factorization;
   the remaining descent is isolated; map_strictlyPerfect_of_mapFree proves restriction
   preserves the finite-free retract models; perfect_affine_map_representative supplies
   f; naturality supplies precisely the final equation, with correctly oriented inverses.
   The new module retains the imports of its outstanding proof plan. The main module's
   remaining proof imports are used, and its two public imports occur in its statement.
   No longer needed accounts for every removed original dependency: three moved to the
   descent node, and ModuleStalkExact is replaced by the proved OpenModuleStalkFunctor
   instances. Checked sk-prop-av-cube.json: realized.statement and its step are empty;
   this reduction changes no unit route or realization. No global pruning claimed. Pass.
5. Checked both nodes' proof steps and dependency unions against the Lean code and imports.
   The new node has its source, complete proof, search records, creation record, matching
   chapter/unit, blueprint ancestry, and verbatim Lean signature. The old node's route
   describes the arbitrary-functor helper and the actual comparison/naturality argument.
   Every remaining hole is named in Proved and sorry left with its node. Pass.

Second reading changed no Lean proof or signature: the repaired proof is sound subject
only to the explicitly isolated descent hole. Added this independent review and checked
its axioms and alternative chain-map route. Holes closed: one; holes added: one; net zero.
