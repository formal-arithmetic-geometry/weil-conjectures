## What changed

Proved `AlgebraicGeometry.Scheme.strictHenselizationClosedLift_over` in
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`, with its signature and
existing public import unchanged. Cofiltered nonemptiness supplies a representative
pointed affine neighbourhood. Rewrite the structural map as its limit leg followed
by its structure morphism, identify the inverse affine-spectrum isomorphism using
`Scheme.isoSpec_Spec_inv`, and postcompose
`strictHenselizationPointEvaluation_pointed` with the structure morphism. Category
associativity and the neighbourhood's `Over.w` equation finish the proof.

This is the canonical evaluation specialization of the neighbourhood factorization
argument already used in `strictHenselizationResidue`; it needs no residue-field
identification or map-existence theorem. The source read was Stacks Tag 04HX,
`literature/stacks-project/etale-cohomology.tex`,
`lemma-describe-etale-local-ring`, and the following definition Tag 03PS.

Updated step 2, `proof_deps`, and the proof-origin note of the shared node
`lem-weil-pbc-strict-henselization-functoriality` to record this auxiliary proof's
use of `lem-weil-pbc-strict-henselization-point-evaluation-pointed`. The other
steps and dependencies remain because they describe the parent theorem's other
clauses. No new statement, definition, node, or consumer adaptation is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.strictHenselizationClosedLift_over`
(blueprint: `lem-weil-pbc-strict-henselization-functoriality`).

The delivered module has zero remaining holes. Added zero holes and split off
zero statements. This is a proof, not a decomposition. The initial proof compiled
on the server in 2.6 seconds; the pruned file is checked again by the delivery tool.

## No longer needed

Removed these seven plain proof imports:

- `Sheaf.AlgebraicGeometry.StrictHenselization`: its definitions are already
  available through the unchanged public import.
- `WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity`: no comparison of
  competing maps is needed.
- `Sheaf.Paper.StrictHenselizationMapExists`: no functorial map is constructed.
- `Sheaf.Paper.StrictHenselizationPointedMap`: no residue-closure surjection is needed.
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`: no local-ring
  structure or henselian property is used.
- `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`: no transport of
  strict henselianity is needed.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`: provided
  by the retained Sheaf structural-map import, whose leg equation is used directly.

In particular, the nodes `lem-weil-pbc-etale-pointed-map-rigidity`,
`lem-weil-pbc-strict-henselization-map-exists`,
`lem-weil-pbc-strict-henselization-pointed-map`, and
`lem-weil-pbc-strict-henselization-local-structure` are unnecessary for this
auxiliary theorem. Relative separable closures, residue fields, separable
closedness, and local morphisms also play no role in this proof. They remain
needed by other clauses of the shared functoriality node, so this delivery does
not claim their modules are globally unreachable. No unit statement or unit proof
step is bypassed. No whole module is withdrawn.

The retained public import `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`
continues to supply the statement's evaluation and structural-map definitions
and preserves the existing exported interface.

## Where the brief, the DAG or earlier work was wrong

The assigned statement and its docstring's proof plan are correct. The imported
functoriality and henselian infrastructure was unnecessary for this particular
closed-lift equation; the two existing leg equations suffice. The node is shared
with the larger functoriality theorem, so pruning this module's imports does not
justify removing dependencies used by that theorem's other clauses.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
