## What changed

Replaced the body of
`AlgebraicGeometry.Scheme.lisse_tower_constant_algebraic_reduction_diagram`
with an adjunction argument from two distinct intermediate statements. Its signature,
its existing public imports, and every existing definition are unchanged.
A local irreducibility attribute keeps the existing realization from unfolding in
the proof. The unused-variable linter is disabled only for the original theorem
to retain its published compatibility binder name. Neither changes an exported
interface. The only existing module changed is the assigned item. Added a private proof import
of `Sheaf.Paper.LisseTowerConstantStalkModels`.

`ConstantAdicQuotientScalarComparison` supplies concrete quotient-module functors:
the quotient map is constructed by `Ideal.Quotient.lift`, constants by the existing
module sheafification, and all derived functors by exact localization. Its one open
theorem supplies the unique ordinary comparison carrying each constant generator to
itself and invertibility of its scalar mate. The chosen comparison is determined
uniquely by those section equations; no arbitrary existence witness supplies data.

`LisseTowerConstantStalkModels` states the geometric step: compatible constant stalk
models, with compatibility after restriction to the common constant completion ring.
It has no effective cone E, no left adjoints L, and no reduction comparison for E.
The scalar comparison has no M, tower, lissity, immersion, or bound on E.
Thus neither new statement repeats the assigned obligation.

The item constructs each e_n by composing the scalar mate with the image of e0_n
and the local model isomorphism b_n. A proved categorical lemma computes its
adjunction unit. Another proved lemma derives the quotient-linear square from its
unit square, using naturality of the actual restriction composition isomorphism
and injectivity of the Hom equivalence. The assumed compatibility of the algebraic
units and the local stalk-model square then give every required square. Finally,
map e_n through homology and scalar restriction to transport finite lissity.

## Proved and sorry left

One original hole is closed by decomposition:
`AlgebraicGeometry.Scheme.lisse_tower_constant_algebraic_reduction_diagram`.
There is no remaining sorry in the assigned module. Its four private helpers
`relativelyFiniteLisse_of_iso`, `comparison_unit`, `paste_unit_square`, and
`reduction_square_of_units`
are fully proved. The unit-square pasting calculation is abstracted over arbitrary
categories so that applying it does not unfold the large coefficient functors.

Two holes are added, each exactly a named theorem body `:= by sorry`:

- `AlgebraicGeometry.Scheme.constantAdicQuotientScalarComparison`, node
  `lem-weil-pbc-constant-adic-quotient-scalar-comparison`.
- `AlgebraicGeometry.Scheme.lisse_tower_constant_stalk_models`, node
  `lem-weil-pbc-lisse-tower-constant-stalk-models`.

This is a decomposition, not a completed proof of the geometric and scalar steps:
1 hole closed, 2 added, net -1. All definitions have actual constructions and no
sorry bodies. The only data chosen from an open theorem is its unique,
section-normalized natural isomorphism.

Validation before delivery: the assigned theorem compiled in 12.0 seconds.
The new scalar-comparison and local-model modules compiled in 13.3 and 13.1 seconds,
respectively. The delivery command recompiles the final files and runs preflight.

## No longer needed

No module or mathematical dependency is pruned. The original geometric dependencies
remain needed under `LisseTowerConstantStalkModels`. The assigned module now uses
those geometric results through that intermediate, rather than directly. Its direct
proof dependencies are the two new nodes. All original public imports remain because
they form the published signature interface. No declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was established. The original two proof steps combined local
stalk construction with the separate unbounded scalar comparison and adjunction
calculation. They did not provide a declaration with the canonical right-restriction
square needed to apply the given unit compatibility. This delivery states that
interface explicitly and proves the categorical combination in Lean.

Edge cases checked in formulating the intermediates: the quotient construction
also handles the zero ring and unit ideal; no nonzero-ring or nonempty-scheme binder
is introduced. Empty schemes admit the empty covering sieve. Bounds remain separate
at every level, and vanishing transfer remains degree-by-degree. The square proof
uses an arbitrary supplied restriction composition isomorphism, so it includes equal
indices without assuming that its chosen representative is definitionally identity.
No faithfulness of derived scalar restriction is assumed: cancellation takes place
in the adjunction Hom equivalence instead. All coefficient actions remain those of
the original inverse-image rings.

## New nodes

`lem-weil-pbc-constant-adic-quotient-scalar-comparison` records the canonical
identity-on-sections scalar square for one completion quotient and its invertible
unbounded derived mate. It retains the existing general constant scalar extension
and ringed tensor-pullback results as proof dependencies.

`lem-weil-pbc-lisse-tower-constant-stalk-models` records the geometric construction
before effectivity, retaining finite origins, exact stalks, finite-ring derived local
constancy and compatible finite derived trivializations. The original unit route
is unchanged. No change record is required: no existing definition, statement,
attribute, instance, or public import is changed.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
