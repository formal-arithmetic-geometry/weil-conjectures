## What changed

The existing declaration `AlgebraicGeometry.localDirectImage_stalk_cohomology`
has exactly its repository signature and original docstring. Its proof obtains
a forward equivalence pinned to a concretely constructed class map, takes its
inverse, and applies the normalization theorem with the pinning hypothesis.

New modules:
- `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassMap`: the actual additive
  cohomology-to-stalk map `AlgebraicGeometry.localDirectImage_stalk_class`.
  It composes `resolutionSectionClass` for Mathlib's injective resolution with
  `isoRightDerivedObj.inv` on top and the top germ. The section-complex
  comparison is `Iso.refl`; no unspecified equivalence supplies this map.
- `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassEquiv`: existence of the
  linear equivalence with precisely that underlying additive map.
- `Sheaf.AlgebraicGeometry.LocalDirectImageStalkNormalization`: normalization
  only for the inverse of an equivalence with that specified underlying map.

The two new imports of the item's module are proof-only `import`s. Its three
original public imports are unchanged. The canonical-map module publicly imports
only what its signature and definition need; the two lemma modules publicly
import what their statements need. The equivalence lemma keeps private imports
of module-stalk exactness and the local-spectrum property for its open proof.
Each new statement has its own module, a source, a full proof in words, and a node.
No existing statement or definition changed; no change record is required.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.localDirectImage_stalk_cohomology` (1 of 1
original holes in the item). This is a decomposition, not a completed axiom-free
proof: the reduction still depends on both new open statements.

Holes added, both with proof exactly `by sorry`:
- `AlgebraicGeometry.localDirectImage_stalk_cohomology_equiv`, node
  `lem-weil-pbc-local-direct-image-stalk-cohomology-equiv`, in
  `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassEquiv`.
- `AlgebraicGeometry.localDirectImage_stalk_cohomology_normalization`, node
  `lem-weil-pbc-local-direct-image-stalk-cohomology-normalization`, in
  `Sheaf.AlgebraicGeometry.LocalDirectImageStalkNormalization`.

There are no other new holes and no sorry in a definition. The concrete map is
fully constructed and `#print axioms` shows only `propext`, `Classical.choice`,
and `Quot.sound`. The two open lemmas and the original theorem additionally
show `sorryAx`, and no other axiom. Thus the delivered decomposition closes one
hole and adds two, a net of -1 before any pruning effects; the maintainer's
pinned-baseline ledger determines the closure totals. It does not count as net
proof progress merely because its upper declaration now has a proof term.

## No longer needed

All eight original direct `proof_deps` of the parent node are replaced by the
new equivalence and normalization nodes. Their disposition is:
- `def-pc-module-stalk-functor`: retained in the signature and map construction.
- `def-weil-pbc-flat-base-change-open-choices`: retained in the signature,
  concrete section-class construction, and normalization proof plan.
- `def-weil-pbc-flat-base-change-resolution-construction`: retained for the
  target-class normalization; its module is still a public signature import.
- `def-weil-pbc-module-cohomology-fmap`: retained in the signature and
  normalization statement/proof plan.
- `lem-weil-pbc-exact-functor-complex-cohomology`: retained below the new
  equivalence lemma; its Mathlib match is the homology comparison.
- `lem-weil-pbc-module-stalk-exact`: retained below the equivalence lemma;
  its module import moves from the item to that lemma's module.
- `lem-weil-pbc-spec-local-ring-canonical-morphism`: retained below the new
  lemma nodes; its private import moves to the equivalence module.
- `lem-weil-pbc-higher-direct-image-presheaf`: no longer needed on this route.
  The concrete `resolutionSectionClass` already gives the relevant comparison;
  `Sheaf.Paper.HigherDirectImagePresheaf` is pruned from this item's import route.

Removed from the item's direct imports: `Sheaf.Algebra.Homology.ModuleStalkExact`,
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`,
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`,
`Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`, and
`Sheaf.Paper.HigherDirectImagePresheaf`. The first and fourth are imported by the
new equivalence module; the second and third remain available through the
unchanged public signature imports. Only the last is pruned from this route;
no claim is made that the whole targets' closure no longer reaches it.

## Where the brief, the DAG or earlier work was wrong

The first worker's normalization statement applied to an arbitrary linear
equivalence. This is false: in degree zero for the identity on Spec(Q) and the
structure sheaf, the canonical class 1 is fixed by the normalized equivalence,
whereas composing it with multiplication by -1 takes it to -1. Thus existence
of an arbitrary equivalence cannot establish normalization. That statement has
been removed and replaced by the normalization of the specified class map.
No false statement remains in the delivery.

The first worker's two node descriptions were placeholders rather than
self-contained mathematical statements, their one-line proofs were incomplete,
and the parent node was not updated to reflect the Lean reduction. These have
been repaired. The initial report called the decomposition a proof and did not
account for its added holes; the accounting above corrects this.

The repository acquired the original proof-dependency imports during this
reading; the final comparison uses that refreshed repository baseline, preserves
its existing signature, and records every removed import above.

The unit `dag/units/sk-thm-p1.json` and its `realized` routes are unchanged.
The decomposition expands the original node's local evaluation and resolution
comparison argument below the unit level; it does not replace a unit step.

## New nodes

`def-weil-pbc-local-direct-image-stalk-class-map` records the actual additive
map, with the resolution, evaluation, derived comparison and germ operations
specified in both its natural-language statement and its Lean definition.

`lem-weil-pbc-local-direct-image-stalk-cohomology-equiv` states linearity and
invertibility of that particular map, without the separate normalization
condition. The pointwise equality uniquely determines its equivalence witness.

`lem-weil-pbc-local-direct-image-stalk-cohomology-normalization` states the
restricted-resolution identity only for an equivalence pinned to the actual
class map. It leaves invertibility/existence to the first lemma and proves the
remaining comparison with arbitrary compatible supplied resolutions.

All three have self-contained statements, source locations, proof steps with
matching proof dependencies, verbatim Lean records, chapter/unit metadata,
and new search records. The parent node's proof, proof dependencies and proof
origin now match the two-step reduction. No unit or other statement was changed.

## Second reading by S3

1. Compared every delivered module with the repository. The existing theorem's
   signature and public imports are byte-for-byte unchanged. Changes to its
   file are the proof and private imports. The other three modules and their
   declarations are new. Verdict: no existing interface changed.
2. Compiled all four modules in import order with `lcompile.py`, without errors
   or warnings, and compiled a scratch axiom probe for every declaration.
   The constructed map has only the permitted three axioms. Exactly the two
   reported named theorem holes remain; their axiom closures and the upper
   theorem also contain `sorryAx`. Scanned for forbidden declarations and
   sorry in definitions: none. Verdict: valid reduction, still incomplete.
3. Rejected the arbitrary-equivalence normalization by the nonzero degree-zero
   example above. For the repaired claims, checked the zero-module and empty
   total-space cases (all classes zero), degree zero (the section-to-germ map),
   V=top, and arbitrary neighborhoods V containing y (inverse image is top).
   The normalization hypothesis forces the equivalence to be the canonical map;
   compatible target augmentation and section components remove resolution
   choices up to homotopy. Repeated searches with different wording using
   LeanFinder, Loogle and Mathlib grep; LeanSearch returned an internal server
   error, recorded as unavailable. Results give generic stalk and resolution
   homotopy lemmas but no existing declaration of either new claim. Also searched
   upstream `WeilConjectures` and `lean/Sheaf`. Verdict: two true, necessary,
   strictly separate components; neither just renames the whole target.
4. The final reduction starts from the upper theorem and uses the concrete
   existing section-class construction rather than introducing an unspecified
   comparison. Imports are classified by signature versus proof use; every old
   dependency and import is accounted for in No longer needed. The unit's
   realized statement and steps are unchanged. Verdict: valid decomposition
   below the unit level; no assertion of net proof progress.
5. Read and corrected all four delivered node records. The new map node matches
   its real construction; the equivalence and normalization nodes have exact
   signatures, complete self-contained statements and proof plans. Their proof
   dependency lists are the unions of their steps' uses. The parent's route
   matches the Lean proof. Verdict: DAG and Lean agree.

Changed in this second reading: removed the false normalization and arbitrary
choice, constructed the actual class map, pinned the equivalence to it, moved
each new statement into its own module, repaired imports and node metadata,
updated the parent route, and corrected hole accounting. The completed map's
standard-only axiom closure also verifies that its data did not come from an
unproved existence theorem. No split-off proof was short enough to close during
this reading.
