## What changed

Repaired the rejected restatement. Removed the earlier attempt's
`extPullback_homComplex_cocycleComparison`, which repeated the original theorem.
The statement and definition of the original module are unchanged.

Added the proof-only import `Sheaf.CategoryTheory.ExtExactFunctorCocycle`.
The new theorem `CategoryTheory.InjectiveResolution.ext_mapExactFunctor_cocycle`
is an exact-functor formula for individual closed cochains, before the Hom-complex
homology comparison. It is in its own new module and does not import the item.

The original module now contains three proved private helpers. The first proves
left-homology naturality on elements from `ShortComplex.LeftHomologyMapData`.
The second specializes this to the quotient class of a Hom-complex cocycle.
The third chooses cocycle representatives of an arbitrary Ext element, proves
closedness of its image from the chain-map equation, applies the new cocycle-level
Ext theorem, and identifies its Hom-complex homology class. The original theorem
specializes that complete argument to the étale inverse-image functor and the
constant-sheaf comparison.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SheafPullbackResolution.extPullback_homComplex`
(node `lem-weil-pbc-ext-pullback-hom-complex`) by a strict decomposition.
It is proved from a single new cocycle-level Ext formula and proved Mathlib APIs;
it is not yet a proof using only the three permitted axioms.

The three private helpers `homologyMap_apply_of_data`, `homologyMap_mk`, and
`ext_homComplex_naturality` are fully proved, with no direct sorry.

Added one hole:
`CategoryTheory.InjectiveResolution.ext_mapExactFunctor_cocycle`
(node `lem-weil-pbc-ext-exact-functor-cocycle`). This is the only sorry in the
delivered modules. The net hole count is unchanged: one upper hole closed,
one strictly intermediate hole added. No data is chosen from an unproved
existence theorem, and no definition contains sorry.

Edge cases: the new theorem permits arbitrary comparison maps and zero source
objects and does not suppose that the image resolution is injective. Its argument
works for q = 0. Zero cocycles and zero α give zero classes by additivity.
The image-cocycle hypothesis is a closedness assertion explicitly discharged in
the original module, rather than a repackaged hypothesis of the original square.

## No longer needed

No existing public import was removed. All statements and definitions keep their
original public imports. The only added import is used solely in a proof.

`Sheaf.AlgebraicGeometry.EtaleInverseImageExact` and
`prop-weil-pbc-inverse-image-exact` are not needed as proof dependencies of this
module: exactness of the inverse-image functor is supplied by the existing upstream
instances. The standalone wrapper theorem is not imported.

`lem-weil-pbc-kinjective-hom-derived` is no longer a direct proof dependency of the
original theorem. The new cocycle roof formula retains it in its proof plan.
The Ext/resolution equivalence and cohomology pullback definition are retained.
No node realizing a unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's cocycleComparison statement was identical to the target
square, so applying it was not a strict reduction. It has been removed entirely.
The present remaining theorem concerns individual raw cocycles in arbitrary
abelian categories and contains neither homPullbackMap nor Hom-complex homology.
The original module proves the representative-selection, closedness and homology
steps instead of delegating the whole square.

The original plan conflated the roof calculation with quotient descent and
homology naturality. The updated parent proof records those separate steps.

## New nodes

`lem-weil-pbc-ext-exact-functor-cocycle` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-ext-exact-functor-cocycle.json`
records the generic cocycle roof formula in
`lean/Sheaf/CategoryTheory/ExtExactFunctorCocycle.lean`. Its source and complete
proof in words are in both its node and declaration docstring. Searches used the
required msearch wrapper and are recorded in searches.jsonl. No interface changes
or forced adaptations are made, so no change record is needed.

## Second reading by T3

1. **Interfaces: PASS.** Read both delivered modules and diffed the existing module
   against the repository. Independently compared the complete `homPullbackMap`
   definition (including its proof fields) and the complete
   `extPullback_homComplex` signature byte for byte: unchanged. The only existing
   node fields changed are `proof`, `proof_deps`, and `proof_origin`. There is no
   interface change, forced adaptation, or change record to review.

2. **Proof and axioms: PASS as a decomposition.** Compiled both modules in import
   order with `lcompile.py --all`; both pass without warnings. Compiled scratch
   copies under `scratch/second-reading` with explicit `#print axioms` for every
   delivered declaration, including the three private helpers. `homPullbackMap`,
   `homologyMap_apply_of_data`, and `homologyMap_mk` use only `propext`,
   `Classical.choice`, and `Quot.sound`. `ext_homComplex_naturality`,
   `extPullback_homComplex`, and the new cocycle theorem also use `sorryAx`.
   The sole direct hole is the reported named cocycle theorem. No forbidden
   declaration or annotation, hidden hole, hollow definition, or witness chosen
   from an unproved existence statement occurs.

3. **Split statement: PASS.** Checked the orientation of the augmentation
   homotopy, the inverse Ext equivalence, the degree shift, and precomposition
   with alpha against Mathlib's `extEquivCohomologyClass_symm_mk_hom` and
   `mapExactFunctor_hom`. The roof calculation is valid for arbitrary exact L;
   L(R) need not be injective. At q = 0 it gives ordinary morphism transport;
   zero a, zero alpha, and zero source objects give zero classes. For the identity
   functor and identity comparison it recovers the same class. Homotopic
   augmentation-compatible comparisons give the same localized roof. The extra
   closedness hypothesis is precisely the obligation proved by the chain-map
   equation in the parent, with no extra assumption on the original theorem.
   The new statement omits Hom-complex homology, quotient naturality, and the
   sheaf specialization; these are actually proved in the parent. It is a
   genuine cocycle-level component of the argument, not the original square
   renamed. Its docstring contains the roof proof and its node has the required
   source, dependencies, blueprint provenance, searches, creation, and Lean fields.
   Independently searched with leanfinder for “naturality of Ext computed by
   closed morphisms to injective resolutions under exact functors”, loogle for
   `CategoryTheory.Abelian.Ext.mapExactFunctor, CategoryTheory.InjectiveResolution`,
   and grep for derived-functor/cocycle and exact-functor/extMk combinations;
   no direct replacement was found. Also searched both library source roots.
   The available same-category pre/postcomposition results do not handle L(R).
   Verified the source's injective-resolution computation at
   [Stacks 06XR](https://stacks.math.columbia.edu/tag/06XR) and the supporting
   localization/functoriality construction at
   [Stacks 01F8](https://stacks.math.columbia.edu/tag/01F8).
   Closing the remaining theorem requires the derived roof calculation with
   shift and single-complex comparison naturality; it is not a short application
   of the located APIs, so the correctly documented hole is retained.

4. **Route and pruning: PASS.** Read the proof from the original theorem down:
   group-homomorphism extensionality, generic Ext naturality, cocycle
   representatives, closedness, the remaining roof formula, and proved
   left-homology naturality. The new module is imported privately because it
   serves only the proof. Its two public Mathlib imports provide notions used
   in its statement. The parent's public imports provide its original interface
   and the injective-resolution infrastructure. The report names both old
   proof dependencies removed from the parent's direct plan: inverse-image
   exactness and K-injective localization; the latter remains in the new node's
   plan. No project-module import is removed. Read `dag/units/sk-thm-p1.json`:
   neither replaced proof dependency realizes a unit statement or step there,
   and the unit's `realized` record and route are unchanged.

5. **DAG agreement: PASS.** The parent's proof and dependency union match the
   cocycle reduction, Ext/resolution equivalence, and cohomology pullback used
   in Lean. The new node describes the remaining derived roof calculation,
   keeps its source and two supporting Mathlib-leaf dependencies, and records
   its declaration signature verbatim. Existing mathematical statements,
   statement dependencies, source and blueprint data were not changed.

**Second-reader changes:** Added this independent review and scratch axiom
checks; no Lean or DAG repair was necessary. One original hole is closed by
one strictly intermediate hole: decomposition, net zero holes closed, and no
project modules pruned. This delivery is not claimed to be sorry-free.
