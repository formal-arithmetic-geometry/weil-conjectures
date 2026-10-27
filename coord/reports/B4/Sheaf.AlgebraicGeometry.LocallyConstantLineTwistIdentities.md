## What changed

Filled `AlgebraicGeometry.Scheme.Modules.locallyConstantLineTwist_identities`
without changing its statement, definitions, original public import or docstring.
Its proof restricts the concrete product to degree opens, assembles the tensor
comparison on pairwise intersections of degree opens, and assembles the arbitrary
pullback comparison on the inverse images of degree opens. The integer-power
pullback comparison is proved privately, including negative powers: cancellation
of tensoring by the pulled-back invertible line identifies its prescribed dual
with the pulled-back dual, and induction handles the tensor powers.

Added two generic support modules, with complete proofs:
`DisjointOpenProductRestriction` and `DisjointOpenIsoGluing`. The former proves
that sectionwise open restriction preserves products, removes the zero factors,
and uses the open restriction/direct-image counit for the remaining factor.
The latter transports local isomorphisms to the existing Over-site module
interface, proves compatibility over empty overlaps, and uses the existing
morphism-gluing and uniqueness theorem for the maps and their inverses.
The assigned module imports both privately, together with
`WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`.

All edits are in the assigned module, the two new modules and their nodes, and
the proof fields of the assigned node. No shared definition, existing statement,
instance, attribute or public interface is changed. Empty schemes, empty degree
strata, negative and zero exponents, and infinitely many strata are included.
Arbitrary pullback is compared locally; only open restriction is used to
preserve an infinite product.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.locallyConstantLineTwist_identities`
(node `lem-sfb-locally-constant-line-twist-identities`).

Added zero holes. No sorry remains in any of the three delivered modules.
The new public theorems
`AlgebraicGeometry.Scheme.Modules.disjointOpenProduct_restrict`
(node `lem-sfb-disjoint-open-product-restriction`) and
`AlgebraicGeometry.Scheme.Modules.disjointOpen_nonempty_iso`
(node `lem-sfb-disjoint-open-iso-gluing`) are proved, as are all private helpers.
No unproved statement is split off.

The final server compile was clean: the assigned module took 3.5 seconds,
product restriction 4.8 seconds, and isomorphism gluing 14.6 seconds.
`#print axioms` for all three public theorems reports exactly `propext`,
`Classical.choice` and `Quot.sound`. The temporary axiom-check module was
removed after this check.

## No longer needed

No original import, module or node is withdrawn. The three original proof steps
are retained. The separate direct proof dependency
`lem-pc-tensor-dual-invertible` is unnecessary: the defined `lineTensorInverse`
already supplies its evaluation isomorphisms, and full faithfulness of tensoring
with the pulled-back line compares inverse objects directly. The underlying
dual definitions and evaluation remain needed through
`def-sfb-locally-constant-line-twist`; this is not a claim of global pruning.

Removed the exploratory private import
`WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal`: the unit comparison
is already available from the retained definition interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The existing dependency declarations
suffice after connecting tensor-formula pullback to sectionwise open restriction
and the Over-site gluing interface. The original local-basis argument for negative
powers can be shortened to cancellation by an invertible tensor factor. This
keeps the unit route and all original hypotheses unchanged.

The unit record's historical source path lies under `sec-six-functors`, whereas
the current blueprint places `sk-thm-sf-ctf-stability` under
`sec-six-functors-basics`; the current unit statement was read there. No unit or
chapter record is changed.

## New nodes

`lem-sfb-disjoint-open-product-restriction`, in
`dag/nodes/sec-six-functors-basics/`, records the proved generic restriction
calculation for a product of direct images over disjoint opens. It requires
neither a covering nor invertibility and isolates the concrete product argument.
Its source is Stacks Tags 00AL, 00AM, 0095 and 0097.

`lem-sfb-disjoint-open-iso-gluing`, in the same chapter, records the proved generic
passage from local isomorphisms on a disjoint cover to a global module
isomorphism. It uses the existing Stacks 04TN module-morphism gluing theorem and
its uniqueness clause. It requires neither a line bundle nor a degree function.

Both nodes inherit the assigned unit and blueprint provenance. LeanSearch,
LeanFinder, Loogle, Mathlib grep and whole-library/DAG searches found the existing
generic APIs used in the proofs and no duplicate of either new statement.
There is no interface change requiring a change record or consumer adaptation.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
