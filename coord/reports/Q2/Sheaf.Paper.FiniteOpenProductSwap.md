## What changed

Decomposed finiteOpenProductSwap while preserving its full original statement.
Proved factorwise invertibility of gamma, sigma, rho, the two one-factor
comparisons, the two product comparisons, and restrictionSource using the
existing isomorphism API. Proved a generic adjunction lemma: restriction detects
maps from any source isomorphic to a left-adjoint object. This avoids the much
larger supported-transport theorem for uniqueness. Cancellation of restrictionSource
and this Hom-bijection argument prove both ambient equalities from unit equations.

Moved the original concrete operations to the new FiniteOpenProductOperations
module and publicly reexported them from the original module. The original names,
signatures, geometric choices, maps and public-import interface persist.
proetSigma now names the native K-flat braiding instead of writing its lift by hand;
see coord/changes/Q2-finite-open-product-operations.md. This is a presentation and
performance repair, not a replacement symmetry. No adopted source file is edited.
The extraction separates definitions from proof imports; it is not a division of a
slow proof to evade a timeout. The native braiding API fixes the slow synthesis.

Added two calculation modules, each with one theorem: FiniteOpenProductRestriction
and FiniteOpenProductSwapRestriction. Their public signatures contain only the
restriction equations, no isomorphism assertions and no ambient equality. The
assembly is substantive Lean (factorwise inversion, adjunction injectivity and
cancellation), not a conjunction repackaging.

Validation: lcompile result c92463b10f6a92a97b511af6 compiled all four modules;
timings 56.7, 49.8, 51.5 and 52.8 seconds respectively. Temporary test modules and
profiler options are excluded. Final delivery recompiles the documented versions.

## Proved and sorry left

Closed the original named hole
WeilConjectures.FiniteOpenProduct.finiteOpenProductSwap (1 original hole).
The main module and Operations contain zero sorry. Its two invertibility clauses
are fully proved from existing isomorphisms; its equality clauses are derived by
the proved supported-source adjunction argument from the three unit equations.

Added two holes, both public named theorems with source, complete proof in words,
and dedicated DAG nodes:

- WeilConjectures.FiniteOpenProduct.finiteOpenProductRestriction:
  lem-pur-finite-open-product-restriction (the two factorization restriction calculations).
- WeilConjectures.FiniteOpenProduct.finiteOpenProductSwapRestriction:
  lem-pur-finite-open-product-swap-restriction (the signed transported restriction calculation).

This is a decomposition, not a claim of a sorry-free proof: 1 hole closed, 2 added,
net -1 before the ledger computes the actual target import closure. There are no
other holes in the delivery and no data chosen from an unproved existence theorem.

## No longer needed

The assembly does not use lem-pur-supported-tensor-isomorphism-transport or its
module Sheaf.Paper.SupportedTensorIsomorphismTransport: its injectivity clause is
replaced by a short general adjunction Hom-equivalence proof. The assembly also
does not use lem-pur-two-open-tensor-chain-normalization or its module
Sheaf.Paper.TwoOpenTensorChainNormalization: its product substitutions are isolated
as the smaller explicit restriction calculations, while invertibility is proved
factor by factor. These modules remain intact, with their original declarations,
imports and attachments. They may still be needed elsewhere; no withdrawal or
whole-library pruning is claimed. Their import of the original item would prevent
using them in its proof without adapting those independently held modules.

The assembly has no direct proof need for lem-pur-derived-pullback-tensor-iso,
def-pc-fibre-product, def-weil-open-immersion or
lem-weil-pbc-open-immersion-base-change: geometry is already proved in the moved
operations; tensor/pullback coherence remains needed by the new calculation nodes.
Only the first two large generic nodes are pruned from this argument.
The temporary proof import Mathlib.CategoryTheory.Adjunction.FullyFaithful was
removed; the basic Hom-equivalence API is already available. Public
imports of the original file are retained through Operations; proof imports are
private. No original Lean module is withdrawn. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned normalization and supported-transport modules both publicly import
the item for its concrete operations. Importing them from the original theorem
would create a Lean cycle. They are independently held (S5 and R6), and the
original consumers still compile with the extraction, so editing their imports
would not meet the forced-adaptation exception. This delivery leaves them alone.

The generic supported uniqueness argument needs no full-faithfulness theorem:
for E isomorphic to L(K), precompose with the inverse, then use the adjunction
Hom equivalence. This is stronger than the particular supported-source uniqueness
step, and is proved directly without new axioms or holes.

Edge cases for the remaining equations were checked mathematically: identity
opens retain the actual unitors and composition maps; an empty open or zero tensor
object gives the unique zero arrows; a nontrivial scalar isomorphism is retained
in both naturality calculations; in odd degrees the two Koszul signs multiply
to one, also in characteristic two. No statement is disputed. The unit route is
unchanged; the item's unit has no binding realized substeps to bypass. The latest
blueprint symmetry clause was read; the calculations are explicitly marked
agent-formulated refinements, not literal assertions of Stacks 0GL1.

## New nodes

lem-pur-finite-open-product-restriction records only the normalized restrictions
of the two explicit chains, a strict part of old Steps 2--6. It introduces its own
objects, has three recorded search kinds, and cites the concrete operation node
rather than the theorem it helps prove.

lem-pur-finite-open-product-swap-restriction records the restriction of the signed
transported reversed map, a strict part of old Steps 8--9. The first new node
handles the reversed comparison's unit equation; the remaining work is normalized
base change and signed tensor/pullback compatibility. Neither new node asserts
ambient comparison equality or invertibility. Existing node Lean attachments are
updated to their actual owning modules, and the main node proof describes the
Lean assembly.

Change record: coord/changes/Q2-finite-open-product-operations.md.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
