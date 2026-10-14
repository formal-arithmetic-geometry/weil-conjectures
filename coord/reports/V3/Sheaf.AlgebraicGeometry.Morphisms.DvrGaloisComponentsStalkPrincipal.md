## What changed

Proved `AlgebraicGeometry.Scheme.dvr_galois_components_normalization_maximalIdeal_isPrincipal`
with its signature and public imports unchanged. Added two proof-only imports for the new,
fully proved modules `DvrUniformizerRootAlgebra` and `DvrGenericGaloisNormalization`.
The first proves the monic Eisenstein root algebra is a DVR with root-generated maximal ideal.
The second assembles existing finite-open integral-closure and normal-stalk results for the
actual generic-cover base change. The target bounds the stalk dimension using the quasi-finite
stalk map and applies Mathlib's local Dedekind-domain principalness theorem.
Updated the target node's proof, proof_deps and proof_origin to match this argument.

All three files compile without warnings through lcompile.py. Explicit #print axioms checks
for all three public theorems return exactly propext, Classical.choice and Quot.sound.
No definition or existing statement was changed. The unit route remains the trait root-chart
calculation in sk-prop-input-spreading.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.dvr_galois_components_normalization_maximalIdeal_isPrincipal`
(node lem-sbc-dvr-galois-components-stalk-principal).

Also fully proved `AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra`
(node lem-sbc-dvr-uniformizer-root-algebra) and
`AlgebraicGeometry.Scheme.dvr_generic_galois_normalization`
(node lem-sbc-dvr-generic-galois-normalization), including their private helpers.
There are no sorries left in any delivered module and no holes added: one original hole closed,
zero split off. The axiom check also establishes that no sorry remains in their proof dependencies.

## No longer needed

No original imports were removed, and the original node had no proof dependencies to prune.
Second reading removed redundant proof-only `Mathlib.AlgebraicGeometry.Noetherian` imports
from the target and `DvrGenericGaloisNormalization`: QuasiFinite (via Artinian) and
FunctionField already import it publicly. No entire project module was pruned.
The proof does not require a new bespoke tensor-product-factor or normalization-stalk comparison
lemma. Existing finiteEtale_open_integralClosure_finite and relativeNormalization_normal_stalks
suffice. The regular-local-ring/cotangent-space detour is unnecessary: the final criterion is
Mathlib's local Dedekind-domain theorem. This is an implementation choice, not a claim that other
users of those modules can be pruned.

## Where the brief, the DAG or earlier work was wrong

The original node's plan had one non-elementary step and empty proof_deps. The necessary
finiteness and normality machinery was already available in the library; the delivery now
records its use. The original node's blueprint.from.node points to the created root-cotangent
node rather than the blueprint ancestor, so blueprint_refs.py ancestor reports None. Existing
blueprint fields are outside the allowed edits; new nodes use the root-cotangent node's recorded
ancestor sbc-thm-spreading-finite-etale-galois and include the intermediate path.

Mathlib sigmaSpec's finite-isomorphism instance requires the index in the ring universe.
The proof explicitly reindexes Fin r through ULift to apply it without changing any signature.
LeanSearch returned Internal Server Error; Loogle, LeanFinder and source searches were used.
No mathematical statement error was found. Edge cases n=1 and r=0 are covered by the uniform
proof; no tameness or degree-divisibility assumption was introduced.

## New nodes

lem-sbc-dvr-uniformizer-root-algebra: new fully proved algebraic root-DVR theorem, in
lean/Sheaf/AlgebraicGeometry/Morphisms/DvrUniformizerRootAlgebra.lean. It uses the existing closed
local principal maximal ideal criterion and Mathlib's Eisenstein and integral-extension APIs.

lem-sbc-dvr-generic-galois-normalization: new fully proved finite-normal generic-cover theorem,
in lean/Sheaf/AlgebraicGeometry/Morphisms/DvrGenericGaloisNormalization.lean. It uses the existing
finiteEtale_open_integralClosure_finite, relativeNormalization_normal_stalks and Smooth.isNormalRing
as general tools, preserving the trait/root-chart unit route. No change records are needed.

## Second reading by V3

1. **Unchanged interface — pass.** Diffed the target against the repository version:
   the complete existing theorem signature and six public imports are byte-for-byte
   unchanged. Only its proof and proof-only imports change. The two other modules
   are new; no existing definition or other module is adapted, and no change record
   is required. The actual relative-normalization stalk remains the conclusion's ring.

2. **Kernel proof — pass.** Independently compiled all three files with lcompile.py.
   There are no sorries or forbidden declarations, including inside definitions.
   A scratch module with explicit `#print axioms` for each of the three public
   theorems returned exactly `propext`, `Classical.choice`, `Quot.sound`.
   The scratch source was removed. No data is chosen from an unproved existence claim.
   The witnesses to the root ring's domain/DVR properties are proofs about the
   explicitly constructed AdjoinRoot quotient, not arbitrary ring data.

3. **New statements — pass.** There are no split-off holes. Read both new theorem
   signatures and their full proofs. The root theorem proves domainhood by Eisenstein,
   constructs evaluation to B/(pi), proves its kernel is (t), and uses integral
   contraction to make (t) the unique maximal ideal. The nonzero root and finite
   Noetherian extension meet every hypothesis of the existing principal-ideal DVR
   criterion. At n=1 this gives B[T]/(T-pi); in residue characteristic dividing n,
   Eisenstein still applies and no etaleness of the root algebra is assumed.
   The generic-cover theorem supplies only finite normalization and normal stalks,
   rather than rephrasing principalness. Finite Galois extensions give finite etale
   p; pullback pasting gives the finite etale cover of an open of Spec A needed by
   finiteEtale_open_integralClosure_finite. For r=0 the source and normalization are
   empty. A non-dominant q factors through the closed point of Spec B, so its generic
   open pullback is empty as well; neither case falsely requires a source point.
   Independently searched Loogle for `AdjoinRoot, IsDiscreteValuationRing` (no hits),
   LeanFinder for relative normalization over a DVR (general normalization APIs only),
   and both Lean roots for root-DVR and finite-normalization alternatives. Existing
   normal-stalk helpers in other modules are private, and the public root-principal
   theorem has different chart and finiteness inputs, so none replaces these statements.

4. **Shortest route and pruning — pass, two redundant imports removed.** Read
   dag/units/sk-prop-input-spreading.json, especially the trait/root-chart step;
   this calculation stays below that step and does not bypass a realized unit node.
   The unit's realized arrays are empty in the baseline and remain untouched.
   Read the existing finite-open integral-closure and relative-normal-stalk theorems:
   their hypotheses match the normal Noetherian affine base and locally Noetherian
   etale source. Smooth.isNormalRing is used as an algebraic tool on affine charts,
   not as a replacement route for the unit. For the target, the root-prime condition
   makes the base stalk a DVR; quasi-finiteness makes contraction strictly monotone
   on comparable primes, bounding the source stalk's dimension by one. Normality
   and Noetherianness then give exactly Mathlib's local Dedekind principalness
   criterion. No cotangent or regular-local-ring detour is needed. No old proof
   dependency is omitted from the report: the original dependency list was empty.
   Removed the target's and generic-cover helper's redundant Noetherian imports.

5. **Nodes and sources — pass.** Read all three delivered node records and checked
   their Lean signatures against their modules. The target's four proof steps match
   the root-DVR construction, finite normal normalization, base-stalk localization,
   and quasi-finite dimension bound. Its proof_deps are the two used new nodes;
   the helper nodes record the existing finite-integral-closure, smooth-normality,
   relative-normal-stalk and principal-ideal-DVR tools actually applied. New nodes
   have the required creation, source, blueprint, search and Lean records, and no
   hole is hidden in them. Read Stacks Tags
   [09EV](https://stacks.math.columbia.edu/tag/09EV),
   [00PD](https://stacks.math.columbia.edu/tag/00PD),
   [032L](https://stacks.math.columbia.edu/tag/032L),
   [033C](https://stacks.math.columbia.edu/tag/033C), and
   [035L](https://stacks.math.columbia.edu/tag/035L) online because the local literature
   checkout is absent. Their root-DVR, normal finite separable closure, smooth
   ascent and relative-normality hypotheses match their uses here; n=1 is supplied
   by the explicit proof rather than attributed to the n>=2 source statement.

**Changes by the second reader:** removed two redundant proof-only Noetherian imports;
added source and blueprint references to both new module docstrings; appended this
independent review. No mathematical proof or statement needed repair. One original
hole closed, zero holes added, zero split off, and no whole project module pruned.
