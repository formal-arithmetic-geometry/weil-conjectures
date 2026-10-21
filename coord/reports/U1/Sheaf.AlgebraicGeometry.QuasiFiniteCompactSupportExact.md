## What changed

Repair of returned head `5642e44c844` (reviewer `C-5642e`): retained the reviewed
Lean assembly and compared the packet with the current shared sheaf-dag source.
Refreshed the existing node from that source, preserving only the stage-3 fields
owned by this delivery; the delivery tool creates the rebased commit on the freshly
fetched sheaf-dag. The previous landing failed while resolving the reviewer override
filename, before merging. The change record is included at
`coord/changes/quasifinite-compact-support-identity-indices.md`. The landing tool
maps this path to the reviewer override basename
`quasifinite-compact-support-identity-indices.change.md`, as required by
`tools/batch_land.py` (`fixes`). The returned `.md` override basename is invalid.
No review override is needed merely to include the retained change record.
The record below explicitly records that distinction for the next landing.

Repeated the current downstream audit: five modules depend on this module, and only
the declaring module textually uses `quasifiniteCompactSupportExact`. Updated the
change record to add the newly present closed-chart and sum-right-adjoint consumers
and the current holders D3 and N3. Their imports, statements and proofs need no changes.

Preflight on the refreshed base found ten current DAG citers. Re-audited and added
`lem-pur-etale-closed-chart-exceptional-preservation`,
`lem-pur-etale-horizontal-double-counit`,
`lem-pur-etale-sum-right-adjoint-coherence`, and
`lem-pur-etale-sum-right-adjoint-tensor`; removed the stale
`lem-pur-finite-etale-dualizing-normalization` citer. Each new entry records its
specific mathematical use and why the indexed identity correction preserves it.

The next delivery run was externally terminated with exit code 137 before it reported
a preflight result or a push. The retained packet was not changed by that termination;
retrying through the supported delivery command. All seven modules had already
compiled successfully on the server in the standalone validation.

Replaced the assigned theorem's single unfinished proof with a compiling assembly of the
support sheaf functor, its exactness for every separated quasi-compact locally quasi-finite
map, normalized compactification units, their finite-case invertibility, and the etale
support/sum identification. The exactness proof uses the existing finite Zariski-main
factorization and transfers exactness through the section-preserving sheaf factorization.

Constructed `exactCompactificationUnit` by fully faithful homotopy-localization descent.
Proved finite-case invertibility at the natural-transformation level. Proved
`isIso_etaleCompactificationGraphMap_of_isFinite` by cancelling the invertible factors of
the existing derived graph comparison and detecting isomorphisms through the
degree-zero cochain homology criterion. Its private single-complex and general
localization detection calculations are complete. Also proved the structural-unit
normalization into graph extension, including transport through a supplied normalized
support isomorphism, in the nested-summand module; the graph-composition
calculation remains the sourced obligation.

The comparison families are inverses of these actual units. Refinement compatibility
transfers finite-case invertibility to all compactifications; cancellation proves all
four independence equations. The etale graph map in a finite compactification gives o,
with the required normalization inside direct image. Identity normalization is proved
from composition and refinement: apply composition to two identity morphisms and cancel using the existing compact-support unit law and
exact-derived coherence. The remaining refinement, composition and nested-summand steps
are stated separately, with complete source proofs in their docstrings and DAG nodes.

The finite graph proof uses a proved private abstract comparison criterion, so the
large concrete sheaf functors are substituted once. This reduces kernel conversion cost
without changing any existing graph construction, visibility or public API.

Corrected the three identity-consistency antecedents to equality of the dependent-sum
packages (target scheme, morphism, compactification). Their conclusions are unchanged.
The complete old/new signatures, consumer audit and reason are in
`coord/changes/quasifinite-compact-support-identity-indices.md`. The node's statement_change
records all ten current citers. This is a statement-encoding repair for independent review;
no Claim/Challenge target statement or source-library declaration is changed.

Validation: every sandbox module compiles through lcompile.py in import order. The main
proof contains no sorry, and all added definitions and private helpers are fully proved.
The exact derived unit and finite-case proof compile without unfolding a localization
preimage componentwise. The removed slow evaluation lemma is not part of the delivery.

## Proved and sorry left

This is a decomposition, not a net proof of the original hole. The identity-index repair
means that the literal old HEq-only statement is not claimed proved. The corrected
`AlgebraicGeometry.Etale.quasifiniteCompactSupportExact` has a complete assembly proof;
the delivery replaces its one upper hole by three strictly separate source obligations.
Holes closed by assembly: 1. Holes added: 3. Net holes closed: -2. Fully discharged original
holes: 0 of 1. No sorry is inside a definition or a private declaration.

Complete proof bodies (the axiom audit below distinguishes their dependencies):

- `AlgebraicGeometry.Etale.exactCompactificationUnit_identity`
  (`lem-sfb-exact-compactification-unit-identity`), from composition and refinement
  with no additional hole.
- `AlgebraicGeometry.Etale.isIso_exactCompactificationUnit_of_isFinite`
  (`lem-sfb-exact-compactification-unit-finite`).
- `AlgebraicGeometry.Etale.isIso_etaleCompactificationGraphMap_of_isFinite`
  (`lem-sfb-etale-finite-compactification-sheaf-iso`).
- In the main proof, the normalized sheaf factorization, additivity and exactness,
  construction of all inverse-unit comparisons, their compactification independence,
  the etale sheaf identification, and all three indexed identity-consistency clauses.

Axiom audit through lcompile.py: the finite exact-unit invertibility theorem uses only
propext, Classical.choice and Quot.sound. The identity and finite graph sheaf proofs have
no local hole but still use sorryAx through their declared unfinished dependencies.
No axiom-free completion of those dependency closures is claimed.

Every sorry added and left:

- `AlgebraicGeometry.Etale.exactCompactificationUnit_refinement`
  (`lem-sfb-exact-compactification-unit-refinement`): original steps 4-5, normalized
  proper/open refinement and common refinement. This is a statement about units for
  a supplied exact functor, not existence/exactness of the support functor.
- `AlgebraicGeometry.Etale.exactCompactificationUnit_composition`
  (`lem-sfb-exact-compactification-unit-composition`): original steps 6-7, the equality
  of successive and single derived units through the proper/open tower. Exactness,
  sheaf factorizations and inverse-unit comparisons are supplied to it.
- `AlgebraicGeometry.Etale.etaleSupportNestedSummands`
  (`lem-sfb-etale-support-nested-summands`): the sheaf part of original step 8, equality
  of two nested structural-lift inclusions with the composite-lift inclusion.

Edge checks: exactness and single-complex detection include the zero coefficient ring,
empty schemes/fibres, and the zero sheaf. The refinement statement permits c=d and is
then equality of normalized units. Composition allows identities and empty sources;
all graph-extension zero-complement arguments remain valid. The identity-consistency
proof eliminates the package equality and uses proof irrelevance for class witnesses.
The remaining lemmas quantify over actual normalized maps, not arbitrary witnesses.

## No longer needed

Removed direct proof imports:

- `Mathlib.Algebra.DirectSum.Module`
- `Mathlib.FieldTheory.IsAlgClosed.Basic`
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.EtaleGeometricFibreCompactSections`
- `Sheaf.AlgebraicGeometry.EtaleSumStalks`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.ProperOpenTowerDerivedUnit`
- `Sheaf.Paper.UnboundedProperOpenInterchange`
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`
- `WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `WeilConjectures.Compactification.Refinement`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

The main proof no longer directly invokes the geometric-fibre/stalk proof of the etale
sheaf identification (`lem-sfb-etale-geometric-fibre-compact-sections`,
`lem-cbc-proper-support-geometric-stalk`, `lem-amb-etale-sum-stalks`,
`lem-weil-pbc-geometric-point-pullback-stalk`, `lem-weil-pbc-inverse-image-stalk-germ`,
`sbc-lem-etale-over-normal`, `lemma-weil-pbc-geometric-stalk-conservative`). It uses the
already-stated derived graph comparison and finite exactness instead. Those modules
may remain dependencies of other library proofs, including the graph theorem; none is
withdrawn and no adopted-source declaration is removed. The new normalization obligations
retain the proper/open and K-injective tools that their source proofs actually need.
No global module pruning or positive sorry-ledger progress is claimed.

## Where the brief, the DAG or earlier work was wrong

The statement-review note said the old HEq identity ties merely accounted for indices.
In Lean they do not supply those equalities; the standard no-confusion principle requires
them. This is an indexing/formalization defect, not a counterexample to the paper's
mathematical identity normalization. The change record makes the exact correction explicit.
The ten current DAG citers retain their mathematical use of the theorem.

The sheaf exactness step does not need a separate forgetful-module argument in this
proof: the existing finite direct-image module instances already supply finite limits,
finite colimits and additivity. The etale sheaf step has a shorter existing derived-graph
route. The proper/open refinement and tower normalization results still need additional
formal glue: the existing theorems describe resolution paths and normalized derived
comparisons but do not directly assert the three retained equations with the constructed
exactCompactificationUnit. These are the retained, sourced obligations rather than new
copies of the whole item.

## New nodes

- `def-sfb-exact-compactification-unit`: the actual localization-descent construction,
  in ExactCompactificationUnit. No data or proof hole.
- `lem-sfb-exact-compactification-unit-finite`: finite-case invertibility, proved in
  the same module; its proof uses the fully faithful preimage isomorphism.
- `lem-sfb-etale-finite-compactification-sheaf-iso`: proved finite-compactification sheaf
  graph invertibility, in EtaleFiniteCompactificationSheafIso.
- `lem-sfb-exact-compactification-unit-refinement`: the first retained obligation,
  in ExactCompactificationUnitRefinement.
- `lem-sfb-exact-compactification-unit-composition`: the tower/composition obligation,
  in ExactCompactificationUnitComposition.
- `lem-sfb-exact-compactification-unit-identity`: identity normalization, proved
  in ExactCompactificationUnitIdentity from composition, refinement and the unit law.
- `lem-sfb-etale-support-nested-summands`: normalized sheaf graph composition,
  in EtaleSupportNestedSummands.

Each is attached to sk-lem-geo-affine-local via the assigned node. The existing unit's
statement and realized route are preserved. New-node searches cover LeanSearch, grep, loogle, and
leanfinder; the adopted-source and project APIs were also read directly. The item node's
proof and proof_deps follow the actual assembly. Change record:
`coord/changes/quasifinite-compact-support-identity-indices.md`.

Preflight repair: performed and recorded the missing LeanSearch search and corrected the
recorded definition signature to omit the parser-excluded noncomputable modifier.
The graph proof uses the explicit mapHomotopyCategory_app equation. Its private general
localization criterion detects invertibility using quasi-isomorphisms and degree-zero
cochain homology, removing the heavy DerivedCategory.FullyFaithful import. The private
isIso_of_derived_comparison helper proves the comparison cancellation for abstract exact
functors. The concrete theorem applies it once to the sum, open and finite-pushforward
functors. This version compiles against the unchanged published graph definition
(25.7 seconds), so no graph-definition visibility change is included. No retained
obligation was split to obtain this improvement.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
