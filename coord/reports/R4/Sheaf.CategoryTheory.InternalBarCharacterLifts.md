## What changed

The assigned module now proves `Profinite.CondensedAction.InternalBarCharacter.exists_lifts`
by a genuine decomposition of the recorded calculation. Its signature and the entire
`Lifts` specification are unchanged. The original concrete complex, component and IsLift
definitions move verbatim into `InternalBarCharacterData`, publicly reexported by the item,
so the separate proof modules can share them without a cycle. All old public imports remain.

The data module constructs the ordered shifted composition by `List.reverseRec` and proves
its empty-list and append equations. It constructs the augmentation by extending the
resolution augmentation and proves its degree-zero normalization. It also proves that a
degree-one map vanishes in degree zero and that shifted augmentation has only one possible
nonzero component. The deletion module proves uniqueness from the free-generator equality
test, by cancellation of the component isomorphisms and separate zero-degree and
positive-degree arguments.

The assembled proof chooses the uniquely normalized deletion maps, uses the actual
recursive iterates and augmentation, equips the actual augmented components with their
proved equivariance, proves the action-category equalities by `Subtype.ext`, and obtains
the coordinate comparison by substituting successive ratios into the independent product
cocycle formula at the regular unit and the identity restriction map.

Validation: `lcompile.py --all` accepted all five modules without errors or warnings.
Per-file times were 10.8 s (data), 5.9 s (cocycles), 7.5 s (deletion), 7.5 s
(iteration), and 13.6 s (item). Text checks confirmed all seven moved definition
blocks and the original Lifts specification and theorem signature are unchanged.
The combined dependency closure of the five packet nodes has no cycle or missing node.
`tools/downstream.py` found zero external Lean consumers of the moved definitions.

Change record: `coord/changes/R4-internal-bar-character-data.md`.

## Proved and sorry left

One original hole removed:
`Profinite.CondensedAction.InternalBarCharacter.exists_lifts`
(node `lem-sfb-internal-bar-character-lifts`). The item itself now has zero holes.

Three new holes, each a strictly smaller part of the argument, remain in separate modules:

- `Profinite.CondensedAction.InternalBarCharacter.exists_deletion`
  (`lem-sfb-internal-bar-character-deletion`): existence of a single normalized degree-one
  deletion lift. Uniqueness is proved separately in `deletion_unique` and
  `exists_unique_deletion`; no ordered iterates or inhomogeneous functions are in this hole.
- `Profinite.CondensedAction.InternalBarCharacter.ordered_properties`
  (`lem-sfb-internal-bar-character-iteration`): the homogeneous generator, equivariance and
  augmented-closedness calculations for the actual recursive composite. Its conclusion
  is a proposition about already constructed maps; it chooses no data and contains no
  inhomogeneous diagram or cocycle comparison.
- `Profinite.CondensedAction.InternalBarCharacter.exists_product_cocycle`
  (`lem-sfb-internal-bar-character-cocycles`): the inhomogeneous internal product cocycle,
  independent of every homogeneous resolution and deletion lift.

This is a decomposition, not an axiom-free completion: one upper hole closed and three
lower holes added, net minus two holes before closure effects. No hole is inside a
definition, no arbitrary data is selected into a definition, and no axiom is introduced.
Every remaining theorem has its source, full proof in words, and matching node.

Additional complete proofs: `orderedIterate_nil`, `orderedIterate_snoc`,
`barAugmentation_zero`, `degreeOne_zero`, `augmented_sole`, `deletion_unique`, and
`exists_unique_deletion` (the last uses the named deletion-existence statement).

## No longer needed

The item's private import `Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful`
is removed. It is not used by the assembly; its generator equivariance test remains a
planned dependency of the new degree-one existence lemma. The deletion uniqueness proof
uses `CondensedFreeLinearizationTensor`'s generator test. No old dependency module is
withdrawn or declared globally unnecessary: the original four planned dependencies are
still present in the new nodes' routes or the shared data's statement dependencies.
No unit step or source-library declaration is bypassed. Pruned modules: none.

The broader Mathlib hits (`Rep.barComplex`, ordinary group-cohomology cocycles, generic
chain-map constructors, and Dold--Kan maps) do not provide these internal formulas.
The source-library `groupCohomology.d_cupHom` assumes a commutative group and does not
supply an internal-function map; it does not match the arbitrary profinite group here.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. The DAG's six-step plan was too
large for a single direct implementation here; its three substantive calculations are
now separate named obligations, while the actual constructions, uniqueness, endpoint
vanishing and final coordinate identification are implemented. This retains the unit
route, all hypotheses, all generator formulas and the coefficient universes.

The new statements were checked on the empty list (identity and product 1), degree one
(additivity), degree two (the four-face expression
`a(h)b(k)-a(gh)b(k)+a(g)b(hk)-a(g)b(h)=0`), the trivial group, zero characters,
the zero ring and the empty profinite parameter. Left translation preserves the ratio
without any commutativity assumption on G. The cocycle calculation uses only a
commutative coefficient ring and additive characters, not a commutative G.

## New nodes

`def-sfb-internal-bar-character-data` owns the shared concrete definitions and the actual
ordered-recursion and augmentation constructions. The seven moved definition bodies are
unchanged, and their original importer receives them by public reexport.

`lem-sfb-internal-bar-character-deletion` is proof steps 1--2, with the uniqueness part
implemented in Lean and only degree-one existence left open.

`lem-sfb-internal-bar-character-iteration` is the homogeneous part of steps 2--4 applied
to the actual recursive composites. It does not restate the full existence theorem.

`lem-sfb-internal-bar-character-cocycles` is step 5 proved by the independent telescoping
inhomogeneous face calculation. It has no homogeneous-resolution parameter. The original
item combines its scalar formula with the homogeneous augmented-generator formula to
prove step 6 in Lean.

All new nodes inherit the item's chapter and unit. The original node's proof,
proof dependencies, proof origin and Lean attachment describe the implemented reduction.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
