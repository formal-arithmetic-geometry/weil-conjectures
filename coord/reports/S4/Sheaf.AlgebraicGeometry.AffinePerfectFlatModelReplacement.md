## What changed

Proved the unchanged `exists_affine_perfect_flat_model_replacement` from two strictly
smaller bridges. Added proof-only imports of their modules and the already proved
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective`.
The proof builds K-projectivity from the ring model's upper bound and projective terms,
lifts its derived isomorphism to a chain map, detects that map as a quasi-isomorphism,
and transports the zero terms through the explicit tilde/restriction functor. It
converts the upper integer bound to a natural number. No existing signature, definition,
public import or visibility changed; no existing module was adapted.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Modules.exists_affine_perfect_flat_model_replacement`
(node `lem-pc-affine-perfect-flat-model-replacement`). The delivered main module has no sorry.

Added two holes, so this delivery is a decomposition, not an unconditional proof:

- `AlgebraicGeometry.Scheme.Modules.exists_affine_perfect_sections_projective_model`
  (`lem-pc-affine-perfect-sections-projective-model`): a bounded finite-projective
  representative with a ring derived isomorphism. It asserts no sheaf replacement,
  flatness or chain map.
- `AlgebraicGeometry.Scheme.Modules.affine_projective_sections_sheafification`
  (`lem-pc-affine-projective-sections-sheafification`): a universal comparison for a
  supplied ring quasi-isomorphism and finite projective terms. It neither assumes
  perfectness nor constructs a bounded projective ring representative or bounds.

All three files compiled together through lcompile.py without errors or non-sorry warnings.
Both new holes have complete source-based proofs in their docstrings and DAG nodes.
The explicit associated sheaf complex is constructed by functors, never by choosing
an arbitrary witness of an unproved existence theorem. Existential elimination stays
inside the proof of a proposition.

## No longer needed

No original import was removed, and no original dependency node is retired.
The old direct dependencies `lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-perfect-affine-bounded-projective`, and
`lem-weil-pbc-affine-tilde-gamma-adjunction` move into the new bridges' proof plans;
they remain needed transitively. The two K-projective dependencies remain direct.
Second reading removed redundant imports from the new modules: `Mathlib.AlgebraicGeometry.AffineScheme`
from AffinePerfectSectionsProjectiveModel and `Mathlib.Algebra.Homology.Embedding.CochainComplex`
from AffineProjectiveSectionsSheafification. Both new modules now import the smaller
`Mathlib.Algebra.Module.Projective` instead of `Mathlib.Algebra.Category.ModuleCat.Projective`. The
three original public imports still supply the existing statement's vocabulary.
The unit `sk-thm-picard-coherence` has empty realized statement/step lists, and this
reduction preserves its bounded perfect replacement route.

## Where the brief, the DAG or earlier work was wrong

The original plan's algebraic-model statement applies to Spec A and to a D_QCoh object;
the assigned theorem uses arbitrary affine Y and an actual quasi-coherent complex D.
Its final tilde/Gamma adjunction dependency supplies the counit but does not directly
state the required finite-presentation and sectionwise IsFlatOver facts or the full
chain comparison. The two bridges make those missing interfaces explicit.

Mathlib K-projectivity and derived-map bijectivity exist, and the source library already
proves `CochainComplex.IsKProjective.exists_Q_map_eq`, which the delivery uses.
LeanSearch returned HTTP 500 (recorded as unavailable). LeanFinder/Loogle found generic
K-projectivity and finite-presentation APIs; grep found no exact bridge. Searches of the
full imported blueprint for affine section models and section sheafification found no
duplicate. Existing finite-term affine presentations deliberately forget projectivity
and bounds, and the strictly-perfect map representative assumes both complexes are
strictly perfect, unlike the present arbitrary target D.

Edge cases checked mathematically: empty Y/zero ring, zero complex, rank-zero terms,
negative upper integer bounds, and a>b (all terms zero). Neither bridge excludes these.
The bound conversion is Lean-proved for arbitrary b, including b<0. Flatness in the
second bridge is the required affine sectionwise predicate, not merely tensor-flatness.
Sources read: Stacks Tags 08EB, 01IB, 0647 and 06Z0 via their official pages because the
literature source files are not present in this read-only clone. No source was changed.

## New nodes

`lem-pc-affine-perfect-sections-projective-model` in
`Sheaf.AlgebraicGeometry.AffinePerfectSectionsProjectiveModel` isolates the ring-model
and ordinary-section identification (Stacks 08EB, 0656, 06Z0, 01IB).

`lem-pc-affine-projective-sections-sheafification` in
`Sheaf.AlgebraicGeometry.AffineProjectiveSectionsSheafification` isolates the exact
sheafification/counit comparison and finite-projective term properties (Stacks 01IB,
08EB, 01I9, 00HT). The main node's proof and proof_deps now match the Lean reduction.
There are no change records or forced adaptations.

## Second reading by S4

1. Compared the existing main module against the repository with diff. Its declaration
   signature and docstring are byte for byte unchanged; only four plain proof imports
   and the proof body differ. The two other modules are new, with no adaptations or
   change records. No target or definition changed. Pass.
2. Compiled all three modules in import order through lcompile.py. Scratch copies with
   `#print axioms` for each public theorem showed only propext, Classical.choice,
   Quot.sound and sorryAx. The main theorem has no direct sorry; the two named bridges
   have their entire proofs postponed. There are no definitions, forbidden trust
   mechanisms, or witness choices in data. Existential elimination occurs only in
   a proposition proof. Pass as a decomposition, not an unconditional proof.
3. Independently checked both bridges against Stacks
   [08EB](https://stacks.math.columbia.edu/tag/08EB),
   [01IB](https://stacks.math.columbia.edu/tag/01IB), and
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0).
   Exact associated sheaves and the natural affine counit identify ordinary sections
   termwise; the derived equivalence then transfers the projective model. Finite
   projectives sheafify to retracts of finite free sheaves, and flatness across affine
   inclusions proves the precise IsFlatOver predicate. Checked empty schemes/zero
   rings, zero and acyclic complexes, rank zero, reversed bounds and negative upper
   bounds. Both bridges are true and strictly parts of the argument: one constructs
   the ring representative without a sheaf comparison; the other sheafifies an
   already supplied map without constructing a perfect representative. Each has
   a source, full proof docstring and matching node. Independent msearch LeanFinder,
   Loogle and grep queries, plus searches of lean/ and Mathlib's Tilde source,
   found useful counit/projective APIs but no duplicate bridge. Neither remaining
   bridge has a short complete proof in the available API. Pass.
4. Read the reduction from its target down. Existing K-projective lifting is used
   directly, and the derived map's invertibility is checked before sheafification.
   Zero terms are transported through the explicit functor, with b <= b.toNat
   justifying the natural upper bound even for b < 0. The unit has empty realized
   lists and its bounded perfect replacement route is retained. No original
   dependency is pruned; the report now distinguishes moved direct dependencies
   from dependencies no longer needed. Narrowed the new modules' imports after
   testing scratch variants. The full import-order compile exposed that the main
   proof had obtained the categorical projective instance through a new bridge's
   public import; added a plain Mathlib.Algebra.Category.ModuleCat.Projective
   import exactly where that instance is used. Pass.
5. Checked the three node records, signatures, dependency unions, source-based proof
   plans, blueprint ancestry and creation records. The main node agrees with the
   Lean reduction; the bridge nodes describe precisely the two remaining holes.
   Corrected the last main proof step's elementary flag to false, because it applies
   the non-elementary sheafification bridge. Pass.

Changes in second reading: removed two redundant new-module imports, narrowed two
projectivity imports, added the required proof-only categorical projectivity import
to the main module, corrected one DAG elementary flag, clarified the dependency
report, and added this review. The main proof body and all signatures are unchanged.
Holes closed: exists_affine_perfect_flat_model_replacement (one original hole).
Holes added: exists_affine_perfect_sections_projective_model and
 affine_projective_sections_sheafification (two holes). Net holes closed: -1;
no claim of positive ledger progress or pruned original modules is made.
