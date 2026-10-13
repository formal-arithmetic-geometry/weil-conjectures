## What changed

Replaced the sole hole in `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModelAux`
with a complete Lean proof following its resolution/cone/comparison route.
The original declaration, hypotheses, universes and visibility are unchanged.

The proof obtains a bounded-below K-injective resolution `i : G ⟶ I`, proves
that its cone is bounded below by `min (M - 1) N`, applies the existing finite-free
acyclic-Hom theorem, transfers exactness across the Hom/cone comparison, and
localizes the resulting quasi-isomorphism. It then composes with the existing
`CategoryTheory.derivedInternalHom_obj_iso`. The two new imports are proof imports.

Added `Sheaf.Algebra.Homology.HomComplexMappingCone`, which constructs both
maps of the degreewise product/cone comparison and proves both inverse identities
in Lean. It uses two proved private helpers for additivity and zero postcomposition.
The chain-map calculation is isolated in the new
`Sheaf.Algebra.Homology.HomComplexMappingConeDifferential`.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.derivedInternalHom_of_boundedAbove_finiteFree_aux`
(node `lem-sc-derived-hom-finite-free-model-aux`). No sorry remains in that module.

Also proved the new `CategoryTheory.homComplex_mappingCone_iso`
(node `lem-sc-hom-complex-mapping-cone`) from a strictly smaller differential
compatibility statement. Its degreewise isomorphisms and inverse equations are
constructed and proved, rather than assumed.

Added exactly one hole:
`CategoryTheory.homComplex_mappingCone_differential`
(node `lem-sc-hom-complex-mapping-cone-differential`). Its proof is exactly
`:= by sorry`, with a full componentwise proof in the docstring. It assumes the
specific projection equations for already supplied degreewise isomorphisms and
asserts only compatibility with the differentials. It has no derived-category,
K-injectivity, resolution, acyclicity, boundedness or finite-free conclusion.

This is a decomposition: one original hole closed, one smaller hole added, net
zero holes, rather than an unconditional proof. The existing
`CochainComplex.acyclic_homComplex_of_boundedAbove_finiteFree` remains an imported
open dependency; it is not restated or proved here. The bounded-below resolution
and derived-Hom object comparison are already proved in the repository.

All three modules compile through `lcompile.py --all`. The final dry run checks
compilation and the axiom probe as well. All new choices select the projections
from the already proved `homComplex_projections_exists`; no new definition or
arbitrary existence witness from an unproved theorem is introduced.

## No longer needed

No existing import is removed, and no module is claimed pruned. Every original
proof import is used. The explicit proof-dependency citation
`lem-sc-kinjective-quasi-iso-comparison` is no longer needed directly: the existing
`derivedInternalHom_obj_iso` supplies the full representative comparison. This
is not a claim that its transitive Mathlib comparison machinery is pruned.

The complete original resolution, acyclic-Hom and derived-Hom computation route
is retained. No unit's statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG's step 2 did not name a declaration transferring acyclicity of
`Hom(E,cone(i))` to the mapping cone of the induced Hom map. The delivery supplies
that comparison and leaves only its differential compatibility as a new item.
Step 3 can use the already proved `derivedInternalHom_obj_iso`, rather than
rebuilding the K-injective localization bijection.

The local `literature/stacks-project` files named by the node are absent on this
machine. I read the corresponding official Stacks pages: Section 0A8X gives the
product and differential formula, Section 08J7 gives the K-injective computation
and the termwise split-sequence argument in Lemma 21.35.4. Tag 0GM8 itself is a
stalk comparison that refers to 0GM7; the precise source for the new algebraic
cone statements is Sections 0A8X and 08J7, not a purported explicit cone lemma
in 0GM8. Sources read: https://stacks.math.columbia.edu/tag/0A8X,
https://stacks.math.columbia.edu/tag/08J7,
https://stacks.math.columbia.edu/tag/0GM8,
https://stacks.math.columbia.edu/tag/0GM7.

The new compatibility statement was checked on zero E, zero f, identity f,
zero G or I, and an empty site. Its matrix calculation uses the actual convention
`cone(f)^n = G^(n+1) ⊞ I^n` and differential `(-d_G, 0; f, d_I)`.
The shifted sign in the first Hom component is `(-1)^(n+1) = -(-1)^n`.
Infinite products are handled by their universal property; no exactness of
infinite products and no global projectivity of finite-free sheaves is assumed.

Searches: LeanFinder and Loogle supplied mapping-cone/cochain APIs but no internal
sheaf-Hom cone comparison. Mathlib grep found only an external HomComplex
namespace opening. Repository searches found no such comparison; the existing
bounded-exact-term Hom theorem requires a lower bound on the first complex and
therefore does not apply here. LeanSearch was attempted twice and returned
Internal Server Error; the actual results are recorded in `searches.jsonl`.
The blueprint search `Hom complex cone` returned no matching node.

## New nodes

`lem-sc-hom-complex-mapping-cone`, in
`dag/nodes/sec-picard-framework/lem-sc-hom-complex-mapping-cone.json`, records the
new `HomComplexMappingCone` module. Its Lean proof constructs the degreewise maps
and their inverses, verifies their identities via product/cone projections, and
uses the following differential compatibility to assemble a chain isomorphism.

`lem-sc-hom-complex-mapping-cone-differential`, in
`dag/nodes/sec-picard-framework/lem-sc-hom-complex-mapping-cone-differential.json`,
records the new `HomComplexMappingConeDifferential` module and the one remaining
hole. It is exactly the componentwise chain-map step of the cone comparison,
with supplied degreewise isomorphisms and their precise projection equation.
Both nodes inherit the item's chapter and unit and cite the same blueprint
ancestor. No statement or definition change and no forced adaptation is needed.

## Second reading by U2

1. **No accidental visible changes.** Compared the delivered auxiliary module with the repository version: the theorem signature, hypotheses, universes, and visibility are byte-for-byte unchanged. The two added modules are new declarations recorded by their DAG nodes.

2. **Proof and trust.** Compiled all three sandbox modules with `lcompile.py --all`; no compiler errors or warnings remain. The auxiliary target has no `sorry`; the only remaining `sorry` is the explicitly named differential theorem, whose docstring gives its source and componentwise proof. No prohibited declarations or hollow definitions occur. The delivery probe checks standard axioms only.

3. **Split statements.** Reviewed both new node statements and searched the repository and Mathlib. The mapping-cone isomorphism is a genuine intermediate result, and the differential theorem is a strictly smaller compatibility step, not a restatement of the target. Both are true in the stated generality and carry complete source/proof documentation and matching node records.

4. **Shortest route and pruning.** The target proof uses the existing bounded-below resolution, finite-free acyclic-Hom theorem, cone acyclicity criterion, and derived internal-Hom computation. The Hom/cone comparison is proved from product projections and cone identities. No unused imports were found; the direct K-injective comparison citation is removed from the updated proof dependencies as recorded above.

5. **DAG and unit agreement.** The Lean declarations, proof dependencies, proof origins, and new node records agree with the code. The Serre-duality unit route is retained; no unit statement or step is bypassed.

Changed only the two max-heartbeats comments so the linter records why the local elaboration limits are necessary; no mathematical statement or proof step changed.
