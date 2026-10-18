## What changed

Proved `AlgebraicGeometry.Scheme.subsingleton_H_of_affine_closed_isSepClosed`
in `Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic`, with its signature and all
public imports unchanged. Added only private, proved helpers and proof imports.
The DAG proof and dependencies now describe the direct exact-global-sections route.

The underlying affine space is profinite and its stalks are strictly henselian.
An étale neighborhood section over a stalk spreads to an open neighborhood by
finite presentation. Local surjectivity of epimorphisms then yields Zariski local
lifts. A finite disjoint clopen refinement permits gluing these to a global lift.
The constant-sheaf/evaluation adjunction consequently makes the constant integer
sheaf projective, so its positive-degree Ext groups vanish. The restriction
functor is constructed explicitly; the existential inclusion supplied by the
existing core theorem is used only to transfer continuity along an isomorphism,
not to choose the data of a public definition.

Validation: the complete proof compiled in 10 seconds after import pruning.
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
Namespace openings were restricted to private helpers and proof bodies; the
original universe declaration is preserved. The interface checker reports no
changes.

The empty scheme and the empty finite clopen refinement are covered by the same
proof: no nonempty point, cover index or global ring is assumed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.subsingleton_H_of_affine_closed_isSepClosed`
(blueprint `lem-cbc-affine-sepclosed-etale-acyclic`).

Holes closed: 1 of 1. Holes added: 0. Holes remaining in the delivered module: 0.
All private helpers are proved; there are no split-offs or changed statements.

## No longer needed

Removed these proof imports:

- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`
- `Mathlib.AlgebraicGeometry.FunctionField`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Mathlib.RingTheory.Ideal.MinimalPrime.Localization`
- `Sheaf.Paper.StrictHenselianZariskiEtaleComparison`
- `Sheaf.Topology.ProfiniteCohomologyVanishing`

The following former proof dependencies are unnecessary for this theorem:

- `lem-weil-pbc-minimal-prime-over-proper-ideal`: Mathlib directly characterizes
  closed points of Spec as maximal ideals.
- `lem-weil-pbc-spec-domain-stalks-function-field`,
  `def-weil-pbc-localization-at-prime`, and
  `lem-weil-pbc-minimal-prime-localization-radical`: the Mathlib
  stalk-dimension/coheight formula directly gives dimension zero.
- `lem-weil-pbc-gabber-strict-henselian-zariski-comparison`,
  `def-sc-topological-abelian-cohomology`, and
  `lem-cbc-profinite-topological-cohomology-vanishing`: direct preservation of
  epimorphisms by global sections and projectivity replace the comparison and
  cohomological vanishing argument.

These are local dependency removals; no claim is made that other targets do not
need these nodes or modules. The unit record's `realized` list imposes no step
that this shorter argument bypasses. Retained the profinite-spectrum and
strict-henselian dimension-zero nodes and used the already proved strict-local
étale-section and Zariski-to-étale core nodes. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no false statement was found.
The planned comparison theorem and profinite-cohomology theorem have universe
interfaces that do not directly instantiate to the assigned statement: the
former fixes schemes and coefficients at the same successor universe, while
the latter fixes spaces and coefficients at the same universe. A direct argument
avoids any interface repair. All constituent geometric, topological and
homological constructions are written and checked in Lean; no new unproved
intermediate theory is introduced.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
