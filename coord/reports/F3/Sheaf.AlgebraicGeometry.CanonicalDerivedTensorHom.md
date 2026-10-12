## What changed

Proved `AlgebraicGeometry.IsCanonicalDerivedTensorHom.unique` in the item's module using
existing K-flat resolutions, K-injectivity of Hom from a K-flat complex, and Mathlib's
K-injective localization Hom bijection. Naturality transports equality from representatives;
tensor-summand extensionality proves equality of the two uncurried chain maps.

Added proof-only imports `Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.Algebra.Homology.KInjectiveHomComplex`, and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
Added the real component construction `AlgebraicGeometry.schemeTensorHomUncurryComponent`
and factored the representative predicate through it to fix the original compile bottleneck.
All existing signatures and mathematical meanings are unchanged. Change record:
`coord/changes/CanonicalDerivedTensorHomComponent.md`.
Updated the existing node's proof route and declaration inventory. No new node or holed
statement was introduced. The complete module compiled locally in 45.9 seconds. A separate scratch equality
check compiled and proved by `rfl` that the named component equals the original
uncurried expression. The required dry run passed compilation, axiom probing and
preflight; nothing was pushed.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.IsCanonicalDerivedTensorHom.unique`
(node `def-pc-canonical-derived-tensor-hom-bijection`).

The sole remaining hole in the delivered module is
`AlgebraicGeometry.exists_canonicalDerivedTensorHom`
(node `def-pc-canonical-derived-tensor-hom-bijection`), unchanged.
Zero holes added, zero statements split off. This is a proof from existing stated
lemmas, not a decomposition; `CochainComplex.isKInjective_homComplex_of_isKFlat`
remains an existing upstream obligation.

## No longer needed

None: every original public import is required by the definitions or representative
condition; every added proof import is used by uniqueness. The original node had empty
proof dependencies, so there is no former proof-dependency module to prune.
The uniqueness proof does not need a tensor-Hom chain-map construction theorem,
a tensor-model invertibility theorem, or a Hom-total-tensor isomorphism: the two
representative clauses supply the chain maps, and uniqueness only compares their
summands. `Sheaf.Algebra.Homology.HomTensorTotal` is not imported directly for this proof;
it still supports the open existence argument and KInjectiveHomComplex below.
No unit route was bypassed: the unit's realized statement and step lists are empty.

## Where the brief, the DAG or earlier work was wrong

The earlier rejected pointwise-uniqueness sorry merely restated uniqueness. It is not
present in this delivery. The earlier substantive scratch proof is retained and completed
as a verified full-module proof after fixing the expensive representative definition.
The uniqueness docstring's phrase “on K-flat inputs” requires a K-flat representative of
the second input before applying K-injectivity of Hom; the Lean proof supplies it.

The repository's literature checkout is absent on this machine. Read the authoritative
Stacks pages for Tags 08DJ and 0A96, which confirm the K-flat second input and K-injective
target argument. The existing named lemma states precisely the K-injectivity used.
Searches through leanfinder, loogle, msearch grep and local rg found the existing
Mathlib tensor-summand extensionality and localization fullness route, with no exact
canonical-family theorem usable without circularity. DerivedInternalHomAdjunction
imports this item and cannot be used to prove its existence theorem.

## Second reading by F3

1. **Visible declarations and statements.** Compared the delivered module with the repository version. All pre-existing declaration signatures are unchanged. The representative predicate has the declared component factored into a real definition; the change record documents this definitional refactor and its direct users.

2. **Compilation and axioms.** Compiled the complete delivered module with `lcompile.py` successfully in 49.1 seconds. The uniqueness proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the only remaining `sorry` is the named existence theorem. The proof uses only the permitted foundational axioms through its imported results.

3. **Split-off statements.** No statement was split off and no new holed theorem or node was added. The component helper is a concrete construction, not an arbitrary witness; its unfolding was checked by a separate `rfl` equality compilation. Searches recorded in `searches.jsonl` found no existing exact canonical-family result.

4. **Shortest route and pruning.** The proof uses the existing K-flat resolution, K-injective Hom-complex, localization fullness, and tensor-summand extensionality results. Every added proof-only import is used, and no original import or proof dependency can be removed. The existence theorem remains open, so its planned dependencies and unit route remain represented in the node.

5. **DAG and unit consistency.** Updated the existing node's declaration inventory and proof route to include the component construction and the uniqueness argument. The target statement and unit's realized route are unchanged; the node remains split solely because the existence theorem is still open.

Changed in this second reading: added this review record only; no Lean proof or statement changes were needed.
