## What changed

Proved five of the twelve holes in `Sheaf.Paper.ProEtaleTateTwists`, preserving
all public signatures, definitions, attributes and imports.

- `AlgebraicGeometry.ProEtale.spIntegralLevelTransition_existsUnique`: the quotient
  reductions compose, and a tensor of a ring morphism and a root transition is
  linear for the restricted free actions. A proved private helper carries out the
  associator and multiplication calculation; faithfulness gives uniqueness.
- `AlgebraicGeometry.ProEtale.spRationalTwistMap_semilinear`: cancel the tensor of
  the scalar-extension projection, substitute the existing normalization, and use
  multiplicativity of the coefficient inclusion. The private categorical helper
  proves this for arbitrary normalized transitions.
- `AlgebraicGeometry.ProEtale.spFiniteKummer_id` and
  `AlgebraicGeometry.ProEtale.spFiniteKummer_comp`: compare maps on the scalar
  extension's pure tensors, using the existing normalization theorem. The root
  power maps have identity and composition laws by cancellation of their kernel
  inclusions. The unique quotient scalar maps handle the heterogeneous source
  presentations, including the zero coefficient ring.
- `AlgebraicGeometry.ProEtale.spTwists_locallyFree`: use the three trivializations
  of the already stated common-cover theorem and the existing local-unit criterion
  for rank one. Moved this theorem after `spTwists_commonCover` so it can use that
  declaration. Its complete statement and original documentation are preserved.

The semilinearity node now records the categorical proof actually used.
The complete module passed the server compiler in 57.6 seconds with profiling;
development profiler options were then removed for the final delivery checks.
No new statements with holes or new nodes were introduced. Search used the
launcher LeanFinder, Loogle and grep wrappers and direct source searches.

## Proved and sorry left

Closed 5 holes, by the five declaration names above. Added 0 holes; split off 0.
Seven original holes remain in the item:

- `AlgebraicGeometry.ProEtale.spIntegralTwistLevel_comparison`
  (construction node `sk-def-sp-tate-twist`).
- `AlgebraicGeometry.ProEtale.spIntegersMap_existsUnique`
  (`lem-route-sp-integers-map-exists-unique`).
- `AlgebraicGeometry.ProEtale.spEllMap_existsUnique`
  (`lem-route-sp-ell-map-exists-unique`).
- `AlgebraicGeometry.ProEtale.spIntegralTwistMap_existsUnique`
  (`lem-route-sp-integral-twist-map-exists-unique`).
- `AlgebraicGeometry.ProEtale.spRationalTwistMap_existsUnique`
  (`lem-route-sp-rational-twist-map-exists-unique`).
- `AlgebraicGeometry.ProEtale.spQbarTwistAction_existsUnique`
  (`lem-route-sp-qbar-twist-action-exists-unique`).
- `AlgebraicGeometry.ProEtale.spTwists_commonCover`
  (`lem-route-sp-twists-common-cover`).

Each is left as its original named theorem with its existing source and proof
in words. Existing dependency holes are used as permitted by stage 3; these
five closures do not assert that the module's transitive axiom closure is clean.

## No longer needed

No imports or modules are removed. The semilinearity proof no longer uses the
sectionwise tensor-generation and sheafification steps, so its node drops
`def-weil-pbc-sheafification` and `def-weil-pbc-module-tensor-product` from its
proof dependencies. The scalar-extension coequalizer API proves the same identity
categorically. These nodes may still be needed elsewhere; this packet withdraws
none of them. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The semilinearity plan's
sectionwise generation argument is unnecessary: the extension projection's
normalization and coefficient multiplicativity suffice. The local-freeness node
already specifies the common-cover route; the Lean declaration order had to be
changed to use it.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
