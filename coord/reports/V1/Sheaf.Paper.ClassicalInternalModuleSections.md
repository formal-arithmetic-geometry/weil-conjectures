## What changed

Proved `AlgebraicGeometry.ProEtale.classical_internal_module_sections` in
`Sheaf.Paper.ClassicalInternalModuleSections`, preserving its complete signature,
public imports and docstring. Added only proof imports and two proved private helpers.
The first transports internal injectives to sectionwise modules and a universe-lifted
site, then proves evaluation acyclicity using Tag 03FD. The second uses the existing
bounded-below derived base-change theorem and bounded-below/unbounded compatibility
to forget module structure on derived sections. The final proof transports along `e`,
applies the existing generic abelian derived comparison unit on `G[0]`, and composes
the comparison-specific Leray isomorphism. Updated the node's proof and proof dependencies.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.classical_internal_module_sections`
(node `lem-sfb-classical-internal-module-sections`).
Holes added: zero. Holes left in the delivered module: zero. No decomposition.
Single-file `lcompile.py` validation passed cleanly in 33.6 seconds.
Both private helpers are complete proofs/constructions. The statement still permits
zero rings and empty schemes and has no torsion or finiteness assumption.

## No longer needed

No original imports removed; all three published imports are retained.
This proof does not need `lem-sfb-ringed-site-unbounded-leray-sections`
(`Sheaf.CategoryTheory.Sites.UnboundedLeraySections`): the source library already
provides `comparisonLowerStarCompRightDerivedGlobalSectionsIso` for the actual
comparison morphism, recorded by `lem-weil-pbc-derived-sections-pushforward`.
It also does not need `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`
(`Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`): the required
whole-derived-object comparison follows directly from its underlying proved
injective-acyclicity input and the generic bounded-below derived square. This avoids
reconstructing an isomorphism of derived objects from cohomology groups alone.
Neither of these dependency modules was imported in the original item; this is DAG
pruning for this proof, not a claim that either module has no other consumers.
The full module-coefficient and affine-continuity package in
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison` is not imported; its generic
source-library abelian comparison unit suffices. The mathematical comparison step
`sk-prop-sf-comparison` remains in the route. No module or declaration withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned interfaces have a universe mismatch to bridge: the pro-etale site's
objects live in `u+1` and its arrows in `u`, whereas the cohomology-to-derived-evaluation
interface expects a small category at the coefficient universe `u+1`. The proof
transports to `ULiftHom.{u+1} X.ProEt`, with the induced topology, and back along
an explicit sheaf equivalence. No change of mathematical site or public interface
is needed. The advertised module/abelian comparison is degreewise; the whole derived
object comparison is instead assembled from acyclicity with the already proved
bounded-below derived-square interface. The general ringed-site Leray theorem is
unnecessary in this specialized comparison setting. No target or unit route changed.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
