## What changed

Replaced `WeilConjectures.ClassicalLocalFrobenius.classicalWeil_blocks` by a Lean
induction using the original positive powers, classical Weil maps, compositors,
and endpoint transports. All existing signatures and definitions are unchanged.
The new proof-only import is `Sheaf.Paper.ClassicalPullbackCompositionCoherence`.

First proved positive isomorphism power addition. The normalized compositor's
associativity and its inverse natural transformation's naturality give a
three-pullback formula with an arbitrary rational arrow. Induction on the second
positive index then proves concatenation of the original classical Weil iterates.
A second induction, expressed as an abstract categorical recurrence, combines
these iterates into the blocked Weil structure. The recurrence treats the power
and index functions as parameters, supplied with their existing equations at
specialization. Explicit zero/successor hom
equations supply that recurrence without unfolding the localization construction
inside the induction. The recurrence is applied directly to the existing public `classicalBlock`.
All substitutions of powers are explicit heterogeneous equality arguments.

The new module states one strictly smaller associativity obligation, with its
source, proof in words and DAG node. It quantifies over normalized compositors
without assuming or asserting any Weil map, iterate or block law. Its normalization
premise is discharged by the existing compositor's chosen specification, rather
than a new choice of comparison. The item node records the actual assembly proof.

## Proved and sorry left

Closed `WeilConjectures.ClassicalLocalFrobenius.classicalWeil_blocks`, one of the
two original holes of `def-zl-classical-local-frobenius-data`, by Lean assembly.
The private helpers `classicalMk_hom`, `positiveIso_add`, `classicalBlockIndex_zero`, `classicalBlockIndex_succ`,
`classicalComposition_map_assoc`, `classicalWeilIterate_add`, the zero/successor
heterogeneous hom equations and `classicalBlockRecurrence`,
together with the generic equality-congruence helpers, are proved completely. The recurrence keeps the block carrier and structure arrow as separate parameters,
with explicit equality and heterogeneous equality witnesses. The witnesses are
definitional projections of the original block. The zero/successor hom equations
then apply directly without rewriting an inverse or changing their source types.

The original hole remaining in the item is:

- `WeilConjectures.ClassicalLocalFrobenius.classicalComposition_existsUnique`
  (`def-zl-classical-local-frobenius-data`), untouched.

The new hole is:

- `WeilConjectures.ClassicalLocalFrobenius.normalizedClassicalComposition_assoc`
  (`lem-zl-classical-pullback-composition-assoc`).

This is a decomposition: 1 original hole closed, 1 smaller hole added, net 0.
There is one direct sorry in each of the two delivered modules. No definition
contains a sorry, and no arbitrary witness is chosen from a mere existence theorem.
The original uniquely specified compositor remains the same definition.

Edge cases: the addition base b=0 is exactly the successor recursion; a=b=0
means two copies of the original structure. The block base n=0 means one block,
and m=0 means the unchanged generator. Product positivity justifies the subtraction
by one in every induction step. Associativity needs no connectedness: all geometric
points are quantified, with clopen connected components used only for detection.
Identity automorphisms, zero sheaves and the empty scheme require no extra assumptions.
No integral invariant lattice for a rational Weil map is used.

## No longer needed

None. No existing import, node, module or declaration was removed. The original
sf and transport addition dependencies are still needed by the earlier proved
block laws. The original public imports remain necessary for the definitions and
signatures. The new private import supplies the associativity used in the proof.
The unit's existing route and realized steps are retained.

## Where the brief, the DAG or earlier work was wrong

The previous node explicitly left both classical obligations unresolved. Its
block-law docstring referred to germ-normalized compositor associativity, but
there was no declaration of that equation. The new node states exactly that
three-pullback step, and the remaining concatenation and block inductions are
now written in Lean. Mathlib's scheme-module pullback associativity has different
objects and does not directly prove the equation for these normalized classical
lisse pullbacks. No existing mathematical statement was changed or disputed.

## New nodes

`lem-zl-classical-pullback-composition-assoc`, in
`Sheaf.Paper.ClassicalPullbackCompositionCoherence`, states associativity of the
inverse compositors for three arbitrary scheme automorphisms, assuming their
actual geometric-fibre normalization. The proof in words compares finite germs,
passes through inverse limits and scalar extensions, and detects equality by
geometric fibres. Only the finite-coefficient part of
`cor-galois-lisse-representations` is used for detection on connected components.
Detection then passes to integral systems via the surjective finite projections
of their free limit fibres, to rational arrows by clearing denominators, and to
algebraic arrows by a common finite coefficient model and faithful field
extension. This respects the current blueprint's finite-only correspondence;
no pro-etale representation theorem or regularity assumption is used. The local
Frobenius data of this unit does not itself state faithfulness of classical fibres.
The requested searches and an additional leansearch were run through msearch.py
and recorded in searches.jsonl.
No change record is needed: no existing public interface, definition, statement,
instance or public import changes, and there are no consumer adaptations.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
