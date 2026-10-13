## What changed

Replaced the sole `sorry` in `Sheaf.AlgebraicGeometry.GradedSerreVanishing`,
`AlgebraicGeometry.graded_serre_vanishing`, with a complete Lean assembly of the
relative-spectrum proof. Its statement and public imports are unchanged.

The proof constructs the fixed Mathlib pullback of `f` along `Spec(A → B)`, proves its
projection affine and its morphism to `Spec B` proper, proves `B` Noetherian and the
pullback locally Noetherian, and converts quasi-coherence plus finite type to coherence.
It pulls the ample invertible module back by `tensorPullback` and applies the existing
`exists_isZero_moduleCohomology_tensorPow_of_ample` over `B`. An explicit induction
identifies tensor powers through the natural comparison of `tensorPullback` and Mathlib
`pullback`. The proved source projection formula then identifies the pushforward twist
with the original coproduct twist. The existing affine edge-map theorem transports
vanishing of additive cohomology groups; the proof reflects this to modules via
subsingletonness and finally transports through the cohomology of the twist isomorphism.

The unformalized bridge from the homogeneous action and local generators to an algebra
module is split into the new module
`Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChange`. Its sole theorem
`AlgebraicGeometry.exists_finiteType_graded_module_affine_baseChange` supplies a
quasi-coherent finite type module on this fixed affine base change and its pushforward
isomorphism. It has no invertible module, ampleness, twisting, cohomology, vanishing,
properness, Noetherian or finite-type-algebra hypothesis or conclusion. This is strictly
the realization part of original steps 1–2, not the original theorem under a new name.
The detailed docstring explains construction of the underlying algebra action, local
finite generation, the affine equivalence, and finite-type transport.

The original node's proof and dependencies now follow the Lean assembly. The unit
`sk-thm-p1` is unchanged: this node is not one of its `realized` statement/step nodes,
and the relative-spectrum / coherent-Serre-vanishing route is retained.

Validation: both sandbox modules compile without errors or warnings under `lcompile.py`.
The delivery dry run includes the project axiom probe and preflight. No existing
signature, definition, visibility, or target statement changes; no forced adaptations.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.graded_serre_vanishing`, node
`lem-weil-pbc-formal-systems-graded-vanishing`. Its proof body contains no `sorry`.

Added 1 hole: `AlgebraicGeometry.exists_finiteType_graded_module_affine_baseChange`,
node `lem-weil-pbc-graded-module-affine-base-change`, in
`Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChange`, with proof exactly `by sorry`.
This is the only `sorry` in the two delivered modules.

This is a decomposition: one upper hole closed and one strictly simpler lower hole added,
net zero new-versus-closed holes in this delivery. It is not an axiom-free proof of the
upper theorem: its dependencies still include the new realization theorem and existing
holed declarations, including coherent Serre vanishing and affine finite-type transport.

## No longer needed

Removed the following proof-only imports from the original module, moving their
remaining role into the realization lemma rather than claiming global pruning:

- `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`, node
  `lem-weil-pbc-affine-module-correspondence`;
- `Sheaf.AlgebraicGeometry.AffineModuleFiniteType`, node
  `lem-weil-pbc-affine-module-finite-type`;
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`, node
  `lem-weil-pbc-affine-morphism-relative-spec`;
- `def-weil-proper-morphism`, node `def-weil-proper-morphism`;
- `Sheaf.AlgebraicGeometry.AssociatedModule`, node `def-weil-pbc-associated-module`;
- `Sheaf.AlgebraicGeometry.TensorPullback`, node `def-pc-module-pullback` (available
  to the original proof through the public imports of `AmplePullback`).

The realization module retains the first four and the tensor-pullback definition because
its remaining proof plan uses them. It also imports the existing relative Spec base-change
and quasi-coherent coproduct lemmas needed to justify its explicit bridge construction.
The original module additionally imports the proved source
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`, the new bridge, and
`Mathlib.Algebra.Category.Grp.Zero`. The existing source projection formula works for
arbitrary scheme morphisms and invertible factors, so no new projection-formula or
cohomology-comparison lemma is added.

No node or module is claimed pruned from the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The original second step describes `G` as an algebra module, but the Lean hypotheses
only provide homogeneous `O_X`-linear maps `mu` and shifted local generators. The existing
affine correspondence expects an already constructed sheaf of modules over the direct-image
algebra. Consequently one cannot apply its signature directly to `∐ G`; the action must
first be extended through the internal direct-sum grading, localized, and glued. The new
bridge states precisely this realization, using the existing affine correspondence and
finite-type lemma in its plan. The relative Spec base-change theorem and the proved
quasi-coherent coproduct theorem are also made explicit in that plan.

The original projection-formula step is available as a proved, more general source lemma.
Its name mentions closed immersions, but the actual projection-formula signature does
not assume a closed immersion and is applicable to this affine projection. Thus this
part of the plan, including the power comparison, is proved directly without a new hole.

Mathlib/source/blueprint searches found no existing homogeneous-action realization bridge.
LeanSearch returned an internal-server error; no absence verdict was inferred from it.
Loogle, LeanFinder and source grep completed. Stacks Tag 0897 was read at
https://stacks.math.columbia.edu/tag/0897 because the repository's literature checkout
is not populated on this machine.

Edge-case checks for the new statement: empty `X` gives the unique zero module on the
empty base change; `r = 0` in a local generating family forces all homogeneous sections
to vanish locally, and hence the underlying sheaf and its realization vanish there.
For `B = A` concentrated in degree zero, the result is finite generation of the underlying
finite graded module on `X` itself. For the zero ring `B`, the scalar/unit law forces
all `G_m` to be zero, consistently with the empty spectrum. Generators in arbitrary
nonnegative degrees and algebras not generated in degree one remain allowed: the proof
uses their shifted span formula and the internal decomposition, never a standard grading.

## New nodes

`lem-weil-pbc-graded-module-affine-base-change` states the quasi-coherent finite-type
realization and pushforward isomorphism on the fixed affine base change. Its source is
Stacks Tag 0897's relative-spectrum realization and finite-type paragraphs, with Tags
01SB and 01PB. The node contains the full homogeneous-action hypotheses, complete proof
steps with existing dependencies, three kinds of search (with LeanSearch's unavailability
recorded), its Lean signature verbatim, chapter/unit/blueprint provenance, and the new
module's declaration record. No change records are needed because no interface changes.

## Second reading by Q4

1. I compared both delivered modules with the repository versions. The target
`graded_serre_vanishing` signature is byte-for-byte unchanged; the realization
theorem is a separate statement. Verdict: pass.

2. I compiled both modules with `lcompile.py --all`. They compile without errors
or warnings. The target has no `sorry`; the only remaining `sorry` is the named
realization theorem, with its matching node. Verdict: pass as a documented
decomposition.

3. I checked the proof against the imported affine base-change, coherence,
pullback, projection-formula, Serre-vanishing, and affine-cohomology declarations.
The proof follows the relative-spectrum route and the new theorem supplies only
the missing homogeneous-action realization. Verdict: pass.

4. I checked pruning against the constants used by the proof. The original module
does not retain proof-only affine correspondence, affine finite-type,
relative-Spec, associated-module, or tensor-pullback imports; the bridge module
retains the imports needed by its split theorem. Verdict: pass.

5. I checked both DAG records against the Lean declarations, including signatures,
proof dependencies, source, and blueprint. The unit route is retained and no target
statement or definition changed. Verdict: pass.

Changed after reading: added this second-reading record. No Lean proof or statement
required repair.

## Earlier second reading (a previous round; superseded)

1. I compared both delivered Lean modules with the repository versions. The existing
`graded_serre_vanishing` signature is byte-for-byte unchanged; the new realization theorem
is a separate, strictly smaller statement. The changed node fields are limited to `proof`,
`proof_deps`, and `proof_origin`. Verdict: pass.

2. I compiled both modules together with `lcompile.py --all`; they compile without errors or
warnings. The original theorem has no `sorry`, and the only remaining `sorry` is the whole
proof of the named public realization theorem, with its matching node and blueprint reference.
No axiom, unsafe, opaque, extern, implemented_by, or sorryAx occurs. The realization theorem
is true in the zero, empty, and degree-zero edge cases because it only asserts existence of the
corresponding affine realization; it does not add properness, ampleness, or cohomology hypotheses.
Verdict: pass as a documented decomposition (one hole closed and one strictly simpler hole
added).

3. I read the source proof of Stacks Tag 0897 and the statements of the cited affine
correspondence, finite-type, relative-spectrum, coherent, pullback, projection-formula, and
affine-cohomology declarations. The upper proof follows the stated relative-spectrum route:
base change and coherence, ample pullback and Serre vanishing, tensor-power and projection
formula isomorphisms, then affine cohomology transport. The new theorem states only the missing
homogeneous-action realization and finite-type pushforward, rather than restating vanishing.
The searches recorded in the new node include LeanFinder, Loogle, grep, and the unavailable
LeanSearch service. Verdict: pass.

4. I checked pruning against the actual proof. The original module no longer imports the
proof-only affine correspondence, affine finite-type, relative-spec, associated-module, or
TensorPullback modules; the new bridge retains the first four where its split proof needs them,
and the public imports remain unchanged. I added `def-weil-proper-morphism` to this report's
removed proof-dependency list because it was also absent from the new proof. The unit route and
its realized nodes are unchanged. Verdict: pass.

5. I checked the two DAG records against the Lean declarations, including the new theorem's
verbatim signature, module, declaration, proof steps, dependencies, source, and blueprint.
The original node's proof dependencies now match the imports and constants used by the Lean
proof, while the new node records the strictly smaller split. No definition or target statement
changed. Verdict: pass.

Changed after reading: corrected the no-longer-needed dependency list above by explicitly
including `def-weil-proper-morphism`, and added this second-reading record. No Lean proof or
statement required repair.
