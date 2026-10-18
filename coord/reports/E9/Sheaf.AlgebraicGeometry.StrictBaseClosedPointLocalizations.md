## What changed

Proved `AlgebraicGeometry.Scheme.strictBaseClosedPointLocalizations` with its signature
byte-for-byte unchanged. Seven proved private helpers supply the local evaluation,
closed-point, weak-etaleness and pointed uniqueness arguments. No definition, public
signature or target statement changes.

The shorter route uses `strictHenselization_indEtale_of_affine_chart` to prove every
structural map weakly etale. Base change and `WeaklyEtale.of_comp` give weak etaleness
of the supplied maps b and q. Their pointed equations make the ring maps local, so
`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` makes them isomorphisms.
The closed-point hypothesis gives the first structural isomorphism by the same theorem.
The base isomorphism is explicitly its inverse followed by b. Pointed etale rigidity
and the strict-local limit prove compatibility; `pullback.map` gives the fibre
isomorphisms and both projection equations.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
All new proof imports are private. The original public imports are retained.
The weakly etale local-ring theorem belongs to this same blueprint unit and is already
proved in the source library. The local-structure and evaluation-surjectivity tools
are existing declarations; no unit statement or realized unit step is bypassed.

Validation: the file compiles cleanly through lcompile.py after import pruning
(10.8 seconds). A text check confirms the original theorem signature is identical,
there is no sorry in the delivered Lean file, every line is at most 100 characters,
and the updated proof dependency list equals the union of the step dependencies.
The deliver3.py dry run passed compilation, axiom probing and preflight; review class
is CODEX because the node proof changed.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.strictBaseClosedPointLocalizations`
(node `lem-weil-pbc-strict-base-closed-point-localizations`).

Added 0 holes; split off 0 obligations. There are 0 remaining sorries in the item's
module and no new Lean modules. All seven private helpers are proved.

The proof uses the existing imported theorem
`AlgebraicGeometry.Scheme.strictHenselizationClosedLift_over`, whose proof remains
sorry in its separately held module. This is an existing named dependency, not a
new hole, relocated hole, or claim that the full target axiom closure is finished.

## No longer needed

Removed these original proof imports:

- `Mathlib.RingTheory.Unramified.LocalRing`
- `Sheaf.RingTheory.EtaleHenselianRingLift`
- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`
- `Sheaf.AlgebraicGeometry.IndEtaleAffineStrictLocalBaseChange`

The corresponding nodes are no longer direct proof dependencies:

- `lem-weil-pbc-etale-algebra-residue-field-separable`
- `lem-sc-etale-henselian-ring-lift`
- `lem-weil-pbc-etale-local-ring-triples`
- `lem-weil-pbc-ind-etale-affine-strict-local-base-change`

The explicit henselian section construction, comparison of relative separable closures
under Omega into Xi, and affine strict-local base-change comparison are unnecessary.
The relative-separable-closure definition itself remains used by the proved evaluation
surjectivity interface. Some removed direct dependencies remain transitive dependencies
of the affine-chart and evaluation lemmas; no global pruning count is claimed here.

Deleted the obsolete top-level tool approvals for
`lem-weil-pbc-etale-algebra-residue-field-separable`,
`lem-sc-etale-henselian-ring-lift` and
`lem-weil-pbc-etale-local-ring-triples`, retaining the other approvals in order.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than necessary given the existing proved
weakly etale APIs. Weakly etale cancellation and the strict henselian local-ring
theorem already identify b and q, without comparing affine residue-triple diagrams.
No mathematical statement was disputed or changed.

Edge cases: the scheme morphism is arbitrary; no properness, finite type, or
algebraicity of Xi over Omega is used. The geometric points exclude zero strict-local
rings. The argument for b and q works even away from the closed fibre; hclosed is
used precisely to make the first structural map an isomorphism. Fibres may be empty:
`pullback.map` still supplies the asserted isomorphism and projection identities.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
