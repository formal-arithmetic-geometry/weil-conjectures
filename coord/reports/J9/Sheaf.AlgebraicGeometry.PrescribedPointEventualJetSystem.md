## What changed

Replaced the proof of
`AlgebraicGeometry.exists_eventual_prescribedPoint_jetSystem`, without changing its
signature or public imports. The proof uses the existing Bertini kernel-basis theorem,
compares ordinary and tensor pullbacks, transports that basis to the requested twists,
and proves uniqueness of coefficients by linear independence. It obtains generation
and immersion on the exact complement of S, then lifts finite-neighbourhood sections
and expresses their lifts in that basis to prove simultaneous jet surjectivity.

Added three modules, each with its own node:

- `Sheaf.AlgebraicGeometry.ProjectiveTwistRestrictionSurjective`: proved eventual
  restriction surjectivity from the existing Serre-vanishing theorem, the
  closed-immersion unit-kernel theorem, and the cohomology exact sequence. Its proof
  works for any closed subscheme; the finite-support hypothesis is not used.
- `Sheaf.AlgebraicGeometry.GeneratingSystemOpenTransport`: proved transport of a
  generating system and its classifying immersion through an open immersion and a
  module isomorphism. Private proved helpers establish the actual section-unit
  comparison and naturality of the projective classifying morphism.
- `Sheaf.AlgebraicGeometry.PrescribedPointInfinitesimalModel`: the remaining local
  comparison with a finite square-ideal thickening, stated separately.

Only proof imports were added to the assigned module. No existing definition,
public signature, source-library module, or target was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_eventual_prescribedPoint_jetSystem` by a complete Lean
proof from the existing declarations and the new finite-neighbourhood comparison.

Added and proved:

- `AlgebraicGeometry.exists_eventual_projectiveTwist_restriction_surjective`
  (`lem-zl-projective-twist-restriction-surjective`).
- `AlgebraicGeometry.generatingSystem_open_transport`
  (`lem-zl-generating-system-open-transport`), together with its private helpers.

One new hole remains:
`AlgebraicGeometry.exists_prescribedPoint_infinitesimalModel`
(`lem-zl-prescribed-point-infinitesimal-model`). Its proof is exactly `by sorry`,
with its source and complete proof in words in both the docstring and the node.
There are no holes in the assigned module, no holes in definitions, and no
additional holes in the two proved helper modules.

This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero holes. It is not an axiom-free proof of the original theorem.
The remaining lemma has no eventual degree, basis, linear independence, generation,
immersion, or global lifting conclusion. It only constructs the finite square-ideal
model and interprets its local sections. The separately proved restriction theorem
provides global lifts, and the main theorem supplies the basis and its coefficients.

The comparison includes empty S and empty schemes. No positive dimension or
smoothness assumption is introduced. Transport allows empty index sets and opens.
All original hypotheses of the assigned theorem are preserved.

Validation: all four Lean modules compile through the prescribed remote compiler.
The main theorem compiled in 41.4 seconds, the transport module in 44.9 seconds,
the restriction module in 15.9 seconds, and the finite-model statement in 10.7
seconds in the final debugging passes. Diagnostic options and trace tactics were
removed for delivery; the main theorem's heartbeat allowance has a local comment.
The delivery command performs the final compilation and axiom checks.

## No longer needed

No original import was removed: the assigned file originally imported only
`PrescribedPointSystemData`, which its statement still needs. No module is withdrawn
or claimed globally pruned. The helper module
`ProjectiveTwistRestrictionSurjective` omits redundant direct imports of
`Modules.Dual` and `Cohomology.Serre`, both already publicly exported by the needed
`Modules.HilbertPolynomial` import.

The assigned node's old direct proof dependencies have been replaced by the actual
route. In particular:

- `lem-weil-pbc-projective-ample-invertible` is unnecessary for this proof: the given
  closed projective embedding itself witnesses very ampleness of the ordinary
  pullback of O(1), and tensor power one gives ampleness.
- `lem-pc-coherent-hi` is unnecessary as a separate basis-construction step: the
  existing BertiniSections theorem already returns a finite independent spanning
  family of the required restriction kernel.
- `lem-weil-pbc-coherent-serre-vanishing` is unnecessary for the interpolation step:
  the proved conventional-cohomology Serre theorem directly gives H^1 vanishing,
  avoiding a comparison between the two cohomology interfaces.
- `lem-sc-closed-immersion-ideal-tensor-sections` and
  `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` are not separately imported or
  applied here. The proved restriction lemma uses the existing unit-kernel theorem
  and the existing ideal-sheaf finite-presentation API instead. This does not claim
  that either node is globally unused; BertiniSections retains its own imports.

The old finite-type/noetherian and finite-presentation dependencies are used inside
restriction surjectivity, the ideal and ideal-power dependencies inside the finite
model, permanence inside open transport, and cohomology inside restriction
surjectivity. They have moved to those helper nodes, not been pruned globally.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken tool was found. The old plan described all the
geometric steps but had no declaration identifying sections of the finite
square-ideal neighbourhood with the concrete cotangent-valued jets; this is the
remaining new lemma. The original statement is kept verbatim.

The current blueprint places the source argument at
`literature/blueprint/latest/blueprint/sec-deligne-laumon-general/sk-lem-wgen-bertini-cover/lem-zl-bertini-finite-cover-curve.proof.md`,
paragraph 2. The new nodes cite this current path. The unit's route through the
prescribed-point system is preserved; no unit statement or proof step is bypassed.

## New nodes

`lem-zl-prescribed-point-infinitesimal-model`: constructs the reduced finite
subscheme and its square-ideal thickening, identifies residue vanishing with the
restriction kernel, and realizes arbitrary local jets on that finite thickening.
This is the only new unproved declaration. Its proof separates the local ring
calculation, the tensor/open-stalk comparisons, and finite-support sheaf gluing.

`lem-zl-projective-twist-restriction-surjective`: the proved high-degree global
lifting step. Its proof uses the short exact kernel sequence, Serre vanishing and
the comparison of the two pullback adjunction units.

`lem-zl-generating-system-open-transport`: the proved passage from the existing
Bertini system on an open of Y to the precise tensor-pullback family on its inverse
image in X. Naturality of the projective classifying map is proved, not assumed.

The assigned node's proof, proof dependencies and proof origin were updated to the
actual assembly. Its statement and Lean attachment were preserved. No change
record is needed because no existing public interface or definition changed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
