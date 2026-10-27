## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.adicLisse_relative_restrict` in
`Sheaf.Paper.AdicLisseRelativeRestriction`; its signature and existing docstring are unchanged.
All new helpers are private and proved. No other existing Lean module is changed.

The proof uses the concrete generic coefficient-encoding helpers already proved in
`Sheaf.Paper.PbcFinitePullbackConstructibility`, and the constant-module
sheafification comparison in `Sheaf.Paper.ProEtaleConstantModuleConstructibility`.
These helpers work for arbitrary coefficient rings and arbitrary scheme morphisms;
the finiteness and Noetherian assumptions in those modules' final theorems are not used.
Private proof imports expose the required existing helpers, including the coefficient
scalar equivalence from `Sheaf.AlgebraicGeometry.ProEtaleOperations`. Naturality of
`proEtaleConstantInverseImageMap` comes from `ProfiniteCoefficientInverseImage`.

First prove naturality of the constant-module encoding by module sheafification's
unit. Combine it with the concrete inverse-image encoding and uniqueness of the
constant-sheaf/global-sections adjunction, then cancel the fully faithful encoding.
Apply the resulting natural module comparison to the actual quotient diagrams.
Forget to abelian sheaves and compare their limits, recording the projection equation.
A general local-model transport lemma proves the scalar law by applying the injective
component comparisons. The given coefficient equation and naturality supply its two
commuting scalar squares. The original covering, modules, completeness and finite
generation are retained verbatim.

The item's DAG proof and proof dependencies now describe this argument. No public
imports, definitions, statements, attributes or instances are changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicLisse_relative_restrict`
(node `lem-weil-pbc-adic-lisse-relative-restriction`).

Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
No statement is split off and no existing hole is relocated.

Validation: `lcompile.py` compiled the final module cleanly in 33.6 seconds with
exit code 0 and no warnings. A text comparison confirms that the original theorem
signature is unchanged. Every Lean line is at most 100 characters. The revised
DAG dependencies equal the union of proof-step uses, and none has a return path
to this node. Delivery performs the required declaration/axiom probe.

## No longer needed

No original import was removed: `Sheaf.Paper.AdicLisseModule` is needed by the statement.
The original plan's abstract lift dependencies
`lem-pe-constant-left-module-inverse-image`
(`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`) and
`lem-sfb-geometric-inverse-image-constant-module`
(`Sheaf.SixFunctors.GeometricInverseImageConstantModule`) are not used by this proof.
Their chosen generic lift need not be related to the concrete pullback: the existing
concrete coefficient encoding gives the comparison directly. They are removed from
this node's proof dependencies; no declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no false assertion was found. The original plan left
implicit the comparison from the generic geometric lift to the concrete small-model
module inverse image used by `IsRelativelyAdicLisseModule`. Existing concrete encoding
helpers avoid that additional comparison. They also remove the need to transport
between site models in this proof. Only the module-to-abelian forgetful functors are
asked to preserve countable limits, never the geometric inverse image.

The proof requires no finite quotient-ring hypothesis, no invertibility of the completed
coefficient map, and no chosen scalar lifts. Thus the zero module, zero ring, empty
scheme or covering member, and the ideals zero and top are included by the same proof.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
