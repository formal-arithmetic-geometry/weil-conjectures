## What changed

Reduced `AlgebraicGeometry.exists_affineBaseChangeCohomologyModel` to the source-only
comparison `AlgebraicGeometry.exists_affineBaseChangeSourceModel`. The new source theorem
has no K', phi, target representative N, or target chain map: it ends in the canonical
module of cohomology of Lg'^*K. Its natural direct-image presentation allows the original
theorem to postcompose with an arbitrary phi. The proof of that postcomposition is written
in Lean, both globally and at each prime.

Added `Sheaf.AlgebraicGeometry.AffineDerivedCohomologyPresentation` with actual constructions
of global-section cohomology modules, their localization equivalences, and exact
representative/stalk isomorphisms. Proved localization naturality using the localization
universal property, `IsLocalizedModule.map_iso_commute`, naturality of the tilde/Gamma
counit, and the germ formula for tilde maps. Proved representative/stalk naturality using
`module_stalk_exact`, `homologyFunctorFactors` and short-complex homology naturality.

The main module proves its coordinate normalization from c.represents, c.counit_isIso,
and exact-stalk naturality for c.t. It constructs the target module as the actual global
sections of H^i(K'), and its localized target isomorphism uses the supplied c.e'.
No arbitrary witness is selected in a definition. Every existing public signature and
visibility is unchanged; no forced adaptation or change record is required.

Read the source online at https://stacks.math.columbia.edu/tag/0DJ8 (affine proof),
https://stacks.math.columbia.edu/tag/06Z0, and https://stacks.math.columbia.edu/tag/08DV.
The Stacks TeX sources recorded as obtained in literature/LIST.md are absent in this clone.
The unit `sk-thm-picard-semicon` has no node bindings in realized; its statement and route
were not changed. This reduction follows the same affine argument below the unit.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_affineBaseChangeCohomologyModel`
(node `lem-pc-affine-base-change-cohomology-model`); the main module contains no sorry.
Added one hole in `AlgebraicGeometry.exists_affineBaseChangeSourceModel`
(node `lem-pc-affine-base-change-source-model`). This is a decomposition, with net zero
holes, not a claim that the underlying affine comparison has become axiom-free.

The new generic module is fully proved. Its public naturality theorems are
`AlgebraicGeometry.affineDerivedCohomologyStalkIso_naturality` and
`AlgebraicGeometry.affineRepresentativeStalkIso_naturality`; both have explicit proofs.
The private main-module normalization helper is also fully proved.

Edge cases of the remaining statement: the zero ring has no primes, so the local clause
is vacuous; zero complexes have zero cohomology; the identity square gives the ordinary
cohomology comparison; arbitrary integer degree and nonflat base maps are included. The
source action is on cohomology, never on an asserted A'-linear R-K-flat resolution. There
is no Tor-independence or boundedness assumption. The remaining statement has no arbitrary
target morphism, so it is a proper subargument of the original theorem. Naturality of the
new target presentation and localization is the real Lean glue recovering that morphism.

Validation: compiled the sandbox modules in import order with lcompile.py; completed the
localization, global-square and coordinate-normalization proofs with repeated single-file
compiler checks. Final delivery validation is deliver3.py --no-push.

## No longer needed

Removed these direct proof imports from the item:
`Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`,
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`,
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`, and
`Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`.
The first three remain dependencies of the source-only theorem and are not claimed pruned
from the transitive closure. The standalone preservation result
`lem-pc-derived-direct-image-preserves-qcoh` is no longer a dependency of this argument:
the affine calculation gives the explicit cohomology presentation directly.

The original module-local dependencies `lem-weil-pbc-localization-module-exact`,
`lem-weil-pbc-spec-tilde-stalk-localization`, `def-pc-base-derived-tensor-cohomology-model`,
and the affine comparison nodes are now under the source-only node or the proved generic
node. They are retained where needed, not claimed eliminated. No claim is made that another
target ceases to reach any of these modules.

Removed exploratory imports of the generic module that its actual constructions do not
use: SchemeDerivedDirectImage, WeilConjectures' derived exact-functor module,
AffineQCohDerivedEquivalence, DerivedDirectImagePreservesQCoh, and
Mathlib.Topology.Sheaves.Abelian. The generic module imports DerivedCategory and the existing
exact-stalk result directly.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing affine comparison declarations do not by themselves
supply the scheme-derived comparison compatibility or its supplied-coordinate equation;
those are genuine glue, not immediate applications of the raw ring comparison.

The repository contains StalkComparisonSourceTransport and StalkComparisonPullbackNaturality,
but their oleans are absent from the supplied compiled library. I did not copy or restate
their declarations. The delivery instead uses the compiled module_stalk_exact interface
and explicitly proves the target normalization in its own module. This limitation does not
block the delivered reduction.

Mathlib search: LeanFinder found stalk localization and cotangent cohomology formulas, but
no exact derived scheme comparison. Loogle found IsLocalizedModule.iso and map_iso_commute,
which are used; the older ModuleCat.Tilde.stalkIso name is not present in the pinned version.
LeanSearch returned Internal Server Error, recorded as unavailable without a no-match verdict.
Grep and blueprint searches found no duplicate of the source-only comparison or of the
explicit natural global-section localization construction.

## New nodes

`lem-pc-affine-derived-cohomology-presentation` records the fully proved generic module of
canonical global-section localization and exact representative/stalk identifications. Its
primary declaration is affineDerivedCohomologyStalkIso_naturality. These are actual
constructions from existing Mathlib and exact-stalk declarations, not new sorry witnesses.

`lem-pc-affine-base-change-source-model` records the remaining source comparison into
pullback cohomology, before any target morphism. The module contains its actual comparison
normalization definition and exactly one named sorry theorem, with the complete source
argument in its docstring. It is strictly the base-change portion of the original argument;
the general target and coordinate chain map are handled by the proved main module.

## Second reading by X2

1. Compared all three delivered modules with the repository. The two supporting modules
   are new; the existing theorem signature (including every binder and conclusion) is
   byte-for-byte unchanged. The existing public imports and visibility are unchanged.
   No existing definition is altered and no change record is needed. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py, with no errors or
   warnings. Scanned every delivered file: exactly one sorry, in the documented public
   exists_affineBaseChangeSourceModel; no forbidden declarations or hollow definitions.
   A scratch import with #print axioms checked the original theorem, source theorem,
   and every public construction and naturality theorem of the generic module. The
   generic module uses only propext, Classical.choice and Quot.sound. The comparison
   definition and main theorem additionally use sorryAx from still-open upstream
   results and the named source theorem. No arbitrary existence witness supplies data
   to any new definition. Verdict: pass as a decomposition, not an axiom-free proof.
3. Read the source theorem, its proof docstring and node against Stacks Tags 0DJ8 and
   06Z0. Its remaining content is the affine source calculation and localization,
   strictly before arbitrary target postcomposition. It fixes the target to actual
   global sections and its germ equivalence; it does not restate the original theorem.
   Checked zero objects, the zero ring (no primes), identity squares and nonflat maps:
   no base-change invertibility, boundedness or Tor-independence is asserted. Its
   supplied K-flat representative need not be termwise quasi-coherent; comparison is
   transported through the counit and derived representative isomorphism. The natural
   direct-image isomorphism is valid for affine maps and unbounded QCoh cohomology.
   Independent LeanFinder search for affine direct-image cohomology, restriction of
   scalars and natural stalk comparisons found no replacement. Loogle's
   homologyFunctorFactors search confirmed the exact naturality factors already used.
   Read AffineDerivedBaseChangeComparison, AffineQCohDerivedEquivalence and the
   pullback-tensor statements; none states the scheme mate/localization compatibility.
   Repository rg search also checked StalkComparisonSourceTransport and
   StalkComparisonPullbackNaturality: their derived-stalk formulation differs from
   the new exact-stalk presentation and does not supply the source-model theorem.
   Verdict: true, needed, proper reduction; not closable by a short existing lemma.
4. Read the global postcomposition proof and stalk normalization from the top down.
   Both use the existing functoriality/localization lemmas directly. The proof-only
   imports remain plain imports. Public imports in new modules supply their signatures
   or public definition bodies. No shorter compiled interface was found. The unit's
   realized record is unchanged (statement=[], steps=[[]]); this is work below it.
   Every old dependency removed from the main node is accounted for: affine comparison,
   affine tensor-tilde and affine equivalence moved under the source node; localization
   exactness, tilde stalk localization and the base-derived tensor model moved under
   the source/generic nodes; derived-direct-image-preserves-QCoh is no longer used.
   The base-change-map and supplied-coordinate definitions remain direct dependencies.
   No transitive module pruning is claimed. Verdict: pass.
5. Checked node statements, Lean records, proof steps and their dependency unions.
   The original node changes only proof, proof_deps and proof_origin. New nodes have
   source, searches, created, blueprint, chapter/unit and Lean records. Found and
   repaired one omission: restored def-pc-derived-base-change-map to the original
   node's second proof step and proof_deps, since the main theorem uses that map.
   Verdict: pass after metadata repair.

Second reading changed only the original node's proof metadata and this report.
No Lean proof or statement needed repair. One original hole closed, one source hole
added, net zero; the proved naturality and normalization glue is the decomposition.
Axiom-check scratch files live under scratchpad and are not part of the delivery.
