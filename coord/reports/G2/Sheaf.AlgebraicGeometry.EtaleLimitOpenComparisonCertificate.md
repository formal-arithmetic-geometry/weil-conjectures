## What changed

Completed `AlgebraicGeometry.Etale.etale_limit_open_comparison_certificate`
without changing its signature. Constructed the directed tail, limiting open cone,
compact and quasi-separated stages, affine transitions, least-stage isomorphism,
final inclusion and preserved sheaf colimit. Applied
`StageCohomologyComparison.system` to the supplied cohomology diagram and cocone.

The new module `Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem` contains
explicit constructions and a lower coefficient coherence theorem. Its four
conjuncts give restricted identities, composition, limit-diagram transitions and
canonical cocone-leg formulas. No object is chosen from unproved existence.
Dependent sheaf categories required explicit types and abbreviation wrappers;
local aliases in the constructor application caused excessive kernel unfolding.
The completed proof uses the exact signature morphisms there.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.etale_limit_open_comparison_certificate`.

Added one lower hole:
`AlgebraicGeometry.Etale.tailOpenRestrictedSystem_coherence`
(`lem-weil-pbc-etale-limit-open-restricted-system`). This is a decomposition,
with one hole closed and one added. Its statement assumes no directedness,
compactness, scheme limit, sheaf colimit or allowed-stage predicate, and does not
assert the original certificate. The target file has no remaining sorry.

## No longer needed

Removed the proof-only import
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and the planned
proof dependency `lem-weil-pbc-etale-inverse-image-restriction`: direct inverse
image suffices. `lem-weil-pbc-inverse-image-composition` is used in the new lower
node, so is no longer a direct proof dependency of the parent but is not globally
pruned. `Mathlib.AlgebraicGeometry.AffineTransitionLimit` remains a proof-only import
of the target module and is not exposed by the new module. The cocone existence theorem is not applied;
its module remains required for the explicit opens and cohomology arrows.
The draft kernel module and node were removed, not delivered. No unit is bypassed.
The second reading also removed the redundant proof-only import
`Mathlib.CategoryTheory.Whiskering`; compilation still succeeds.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt reported an unavailable compiled dependency. It is now
available. The earlier private constructor proof repeatedly timed out while
comparing dependent sheaf types. Explicit scheme-indexed types, abbreviation
wrappers, and use of the exact signature morphisms resolve this; there is no
split certificate theorem or moved target hole. The unfinished lower statement
packages the canonical coefficient coherence and cocone-leg formulas.

## New nodes

`lem-weil-pbc-etale-limit-open-restricted-system`, in
`Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem`, records the explicitly
restricted system and its four coherence formulas. Its docstring gives the
complete natural-language proof and tests empty opens, zero coefficients and
identity diagrams. No change record is needed for an existing interface: the
original signature and public imports remain identical and proof options are
scoped to the declaration.


## Second reading by G2

1. **Interfaces: pass.** Compared the delivered certificate module with the
repository using `diff`, and compared the existing theorem signature as bytes:
it is identical, including hW, hWO, the directed qcqs affine diagram, hc,
coefficient identity/composition, hG, hL, e, allowed, hallowed, hK and hι.
Both existing public imports and the conclusion for the supplied colimit.desc
are unchanged. The only changes to the existing node's JSON values are proof,
proof_deps and proof_origin. There are no forced adaptations or interface
changes requiring a change record.

2. **Proof and constructions: pass as a decomposition.** Compiled both modules
in import order with lcompile.py, without errors or warnings. Then compiled
scratch copies with #print axioms for the certificate and all eight public
restricted-system declarations. The seven constructions use only propext,
Classical.choice and Quot.sound (the inclusion uses only propext). The coherence
theorem and certificate also use sorryAx. The only delivered sorry is the named
tailOpenRestrictedSystem_coherence theorem. No forbidden axiom/unsafe/opaque,
extern, implemented_by, kernel-check bypass, or holed definition occurs. The
functors, cone, sheaves, coefficients and isomorphisms are explicit constructions;
no arbitrary witness is extracted from an unproved existence assertion.

3. **Lower statement: pass.** Read all four conjuncts against the definitions:
identity and composition are for the restricted coefficient maps, the third
is the restricted G transition under the specified tailOpenLimitIso, and the
fourth identifies the canonical leg with geometric cohomology pullback followed
by H.map of that iso's inverse and the restricted cocone leg. Each is consumed
by the parent. These are formal inverse-image coherence equations, not a
restatement of the geometric certificate: no limit, colimit, compactness,
directedness, allowed predicate or certificate is assumed or asserted. On an
empty open or zero sheaves the maps are the unique maps between zero objects;
for a singleton identity diagram the equations reduce to unit coherence and
the same restriction map. The docstring explains the calculation using unit
laws, associativity, naturality, cancellation and functoriality. Independent
LeanFinder, Loogle and grep searches are logged. Upstream
Etale.upperStarComp_id_left, upperStarComp_id_right and upperStarComp_assoc
support that calculation but do not state these restricted-system equations.
No short replacement for the entire remaining hole was found.
The source context was read online because the local Stacks source is absent:
[09YQ](https://stacks.math.columbia.edu/tag/09YQ) and
[01F7](https://stacks.math.columbia.edu/tag/01F7).

4. **Route and pruning: pass.** Followed the actual application of
StageCohomologyComparison.system: limiting opens via the initial over-category
functor, compactness by affine preimage, open quasi-separatedness, affine
restricted maps, the explicit least-stage isomorphism, and preservation of the
sheaf colimit after final tail reindexing. hK and hι supply exactly its arrow
and cocone equations. Read dag/units/sk-thm-p1.json, including realized: none
of its statement/step realizations is bypassed. Both removed old dependencies
are accounted for under No longer needed: inverse-image restriction is removed,
while inverse-image composition is retained below the new node. The cocone
module stays for its actual definitions; its existential theorem is not used.
The new module's public cocone import is needed by its signatures and definitions.
All new proof imports in the certificate are plain imports.

5. **DAG: pass after repair.** Checked the old and new node statements, source,
chapter/unit, proof steps, union of uses against proof_deps, ancestry, creation
and Lean records. The parent's three steps describe the Lean proof and the new
node's four steps describe exactly its remaining equations. Replaced the new
node's flattened lean.statement with the verbatim multiline theorem signature
and added the independent search results. Existing node statements are unchanged.

**Second-reading changes:** removed redundant Mathlib.CategoryTheory.Whiskering,
recorded the exact new theorem signature, added independent search evidence,
and documented this reading. No proof or statement was weakened. One original
hole is closed and one strictly lower hole remains added: net zero holes,
reported as a decomposition rather than an unconditional proof.
