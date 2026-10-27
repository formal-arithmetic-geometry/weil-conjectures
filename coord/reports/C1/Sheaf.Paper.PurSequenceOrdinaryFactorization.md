## What changed

Constructed the ordinary data in `Sheaf.Paper.PurSequenceOrdinaryFactorization`:
the completed-ring cone, constant/limit ringed projection, additive simultaneous
scalar extension, its adjunction, and the comparisons with the recorded finite
adjunctions. Uniqueness of left adjoints preserves units; local unit-tensor
extensionality then identifies the actual quotient transitions. The projection
comparison uses equality transport, and a generic adjunction calculation gives
the required transpose formula. The existing public statement is unchanged.

Added the proved module `Sheaf.Paper.PurSequenceConstantRingFactorization`. Its
first ringed morphism is explicitly identity on sheaves and restriction along
the quotient structural map on modules. Its second morphism is explicitly the
constant/limit morphism with identity structural map. The constant-ring tower
equivalence retains actual sections and horizontal maps. Uniqueness of the
recorded restriction tower, the supplied ordinary limit comparison, and
uniqueness of right adjoints provide all three composition comparisons. The
existing scalar-restriction exactness theorem supplies both exactness fields.
All new definitions contain actual constructions. The constructions also cover
identity transitions, zero modules, and an empty underlying site: the proofs use
only functoriality, adjunction equations, and sectionwise identities, and impose
no nonemptiness, surjectivity, or flatness assumption.

The ordinary theorem uses the new factorization theorem and private proof helpers
through proof imports. The scalar-transition calculation first works with abstract
normalized scalar models. The unique component characterization identifies the
recorded quotient with the canonical mate as a natural transformation, before
its components are evaluated. A typed component API then specializes the square
to the actual coefficient tower without reducing the finite quotient ideals.
The tensor comparison is defined by its canonical transported adjunction formula,
so its identification is reflexivity. The proved module
`Sheaf.Paper.SystemScalarTransitionComparison` isolates the unit-tensor and
quotient-mate calculation over abstract ring sheaves. Local irreducibility keeps
the remaining coefficient constructions behind their APIs. No existing shared
definition, signature, public import, target, or downstream module was changed.
Validation: all three modules compile without warnings through `lcompile.py --all`;
the final assigned module compiled in 50.9 seconds. Delivery preflight follows.

## Proved and sorry left

Closed the original hole in `WeilConjectures.purSequenceOrdinaryFactorization`
(node `lem-pur-sequence-ordinary-factorization`). Its ordinary witness is built
explicitly and combined with the proved
`WeilConjectures.purSequenceConstantRingFactorization`
(node `lem-pur-sequence-constant-ring-factorization`).

Original holes: 1. Holes closed: 1. Holes added: 0. Sorries left in the delivery:
none. No obligation is split off with `sorry`. Existing imported declarations
retain their original proof status.

## No longer needed

No original import is removed and no existing module is withdrawn. The item's
direct planned dependency `def-coef-constant-sequence-equivalence` is now used
inside the proved factorization node. Its direct planned dependency
`def-pc-sheaf-restrict-scalars` is replaced there by the already proved exactness
API of `lem-pur-system-scalar-model`. These are changes to the direct proof
route, not claims that either existing module is globally unused.

The ordinary construction uses the explicit ordinary part of
`SequenceSiteCompletionProjection`; its derived existence theorem and a proof
that the completed cone is limiting are not needed here. That source module
remains needed, and its existing declarations and imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The proof plan was usable.
The imported blueprint has no separate node for constant completed-ring
factorization (whole-blueprint search: zero matches). The item's recorded
`blueprint.from` points at a created node, and its `created.item` is a module
name; the ancestor utility consequently returns `None` for this item. The new
node records the actual blueprint ancestor of its parent,
`thm-pur-rational-and-qbar-purity`, with the complete intermediate route.

## New nodes

`lem-pur-sequence-constant-ring-factorization` records the original plan's
constant-ring factorization and exactness steps. It has a complete Lean proof,
three recorded Mathlib searches, and no new hole. Its universal statement takes
already constructed ordinary adjoints as input and constructs the geometric
factorization, so the original theorem still has to construct all ordinary
adjoint data. No change record is required: only the assigned module, two new
modules, their node records, and this report are delivered.

`lem-pur-system-scalar-transition-comparison` records the fully proved generic
unit-tensor comparison used to identify the horizontal transition square. It
works for arbitrary normalized scalar models and arbitrary comparison
isomorphisms, and uses the canonical quotient mate. Its proof is complete, its
three Mathlib searches are recorded, and it adds no hole.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
