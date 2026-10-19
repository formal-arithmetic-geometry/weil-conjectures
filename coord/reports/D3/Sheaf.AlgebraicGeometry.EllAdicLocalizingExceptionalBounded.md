## What changed

Proved `ellAdic_localizing_canonical_rightAdjoint_obj_isBounded` in
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded`. Both existing public
signatures and the supplied-adjoint theorem are unchanged. Added proof-only imports and
proved private helpers for coefficient normalization, transport of constructibility,
universe lifting, the embedded/spectral integral coefficient comparison, and equality
of the two localizing hulls. All coefficient isomorphisms are constructed explicitly.

The proof applies `exceptionalInverseImage_exists`, identifies its proper compactification
functor with the actual derived pushforward, and transports the adjunction through the
fully faithful inclusions. Uniqueness of right adjoints transfers the existing Dctf
preservation theorem. Canonical t-structure bounds give the requested homology vanishing.
The source's rational/integral restriction route is retained through that existence theorem.
Updated the canonical node's proof, proof dependencies and proof origin accordingly.

Validation: the complete module compiles without warnings (about 10 seconds). The unchanged consumer
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` also compiles against
the delivered module. The field comparison allows arbitrary finite normed extensions; the integral comparison allows
arbitrary specified embeddings and retains torsion. Neither comparison replaces the
finite-subextension-valued algebraic closure by the all-continuous-map coefficient ring.
Empty schemes, zero objects, and rank-zero local models require no extra hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_canonical_rightAdjoint_obj_isBounded`
(node `lem-sfb-adic-localizing-exceptional-bounded-canonical`).

The already proved `ellAdic_localizing_rightAdjoint_obj_isBounded` is retained.
There are zero holes left in the delivered module, zero holes added, and zero split-off
statements. All private helpers are proved. The proof uses existing named statements
that remain project obligations, including `exceptionalInverseImage_exists`,
`localizingClosure_ctf_equals_bc`, the field/Qbar local triviality statements, and
`integralLfpConstantModelComparison`; none is restated or replaced here.

## No longer needed

Removed the canonical node's circular proof dependency on
`lem-sfb-adic-localizing-exceptional-bounded`. The supplied-adjoint theorem still uses
the canonical theorem in the intended direction, so its module and node stay.

No original import is removed: proper localizing pushforward and Brown representability
are both used. No module is withdrawn. Direct separate rational/integral restriction
imports and `ProperExceptionalRestriction` are unnecessary: the existing existence
statement provides right-adjoint preservation, and the proper comparison is proved here.
The finite-affine-cover boundedness argument need not be duplicated in this module.

The `import all` modules supply proved local helpers: sectionwise continuous-coefficient
isomorphisms, presentation/stratification transport, and small-support comparison of
coproduct universes. Their larger global theorem statements are not used as assumptions.
Removed experimental direct imports of `Mathlib.FieldTheory.IsAlgClosed.Basic` and
`Sheaf.Paper.ConstantModelTorAmplitude`, since the retained imports already expose the APIs.

## Where the brief, the DAG or earlier work was wrong

The canonical node depended on the supplied-adjoint boundedness node, whose proof in
turn depended on the canonical node. That cycle supplied no geometric boundedness input.
The revised proof uses the already stated `sk-thm-existence` input instead. The two
constructibility predicates and the coproduct indexing universes are not definitionally
equal; the delivery proves their comparisons. The integral comparison additionally needs
an explicit change from embedded coefficients to the spectral valuation topology on a
universe lift; it is not an instance cast.

No existing statement or definition was changed. Preflight requested a change record
for the added namespace/open/local-attribute commands:
`coord/changes/ell-adic-exceptional-bounded-local-helpers.md`. It documents their local
scope and the unchanged consumer interfaces. No forced adaptations or new nodes.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
