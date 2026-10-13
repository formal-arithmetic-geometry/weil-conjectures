## What changed

Proved the combination in AdditiveCohomologyPullbackComparison without changing any
existing signature or public import. Added two proof imports and two intermediate
modules: CanonicalAdditiveCohomologyComparison and CartesianUnitCohomologyTransport.
The first constructs the canonical scalar and adjoint coefficient morphisms.
The original module constructs coordinate isomorphisms, proves scalar conjugation
and the adjunction pullback square, then combines cohomology functoriality with the
two intermediate comparisons.

## Proved and sorry left

Closed AlgebraicGeometry.Scheme.Modules.exists_additive_cohomology_pullback_comparison.
This is a decomposition: one hole closed, two added. No sorry remains in the item.
The two new holes are:

- AlgebraicGeometry.Scheme.Modules.exists_canonical_additive_cohomology_square
  (lem-pbc-canonical-additive-cohomology-square).
- AlgebraicGeometry.Scheme.Modules.exists_cartesian_unit_cohomology_transport
  (lem-pbc-cartesian-unit-cohomology-transport).

Both are public theorems with whole proofs `by sorry`, sources, complete proofs in
words and nodes. No definition chooses data from an unproved theorem. All modules
compile locally; the original proof has no warnings. Edge cases checked: degree
zero, zero rings, identity morphisms, empty schemes and nonflat algebra extensions.
The canonical square asserts no invertibility of the coefficient morphism.
Ordinary transport uses only scheme isomorphism and pullback of the unit.

## No longer needed

No existing import was removed and no global pruning is claimed. The following old
proof_deps are no longer direct dependencies of the item; they remain in the
intermediate nodes' plans:

- lem-sc-etale-tensor-unit-sections-natural, via the canonical additive square;
- lem-sc-etale-qcoherent-source-comparison-natural, via that square;
- lem-pc-affine-cech-inverse-image, via that square;
- lem-weil-pbc-module-pullback-structure-sheaf, via cartesian transport (its
  ordinary Mathlib clause, rather than the tensorPullback declaration).

The public PullbackFree import in the new ordinary-transport module is needed
by unitToPushforwardObjUnit in its signature (verified by removing it in a
compiler experiment and restoring it). No existing library module is claimed
pruned. The unit and chapter routes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The source comparison is natural in endomorphisms of a fixed module; it does not
state compatibility with scheme inverse image. The affine Cech inverse-image
statement concerns ordinary module cohomology, not the cross-site square. Neither
alone closes original step 3. The canonical-square intermediate records this missing
comparison without assuming arbitrary existential equivalences commute. Displayed
cartesian-square transport is a separate ordinary argument. LeanSearch returned
Internal Server Error and is recorded as unavailable. No statement was altered or
disputed, and no forced adaptation was needed.

## New nodes

lem-pbc-canonical-additive-cohomology-square is stated in
lean/Sheaf/AlgebraicGeometry/Curve/CanonicalAdditiveCohomologyComparison.lean.
It compares fixed additive structure sheaves to ordinary unit modules for an
arbitrary map of quasi-compact separated schemes, including global multiplication
and inverse-image naturality. It has no base algebra or cartesian square. The scalar
and coefficient morphisms are concrete constructions.

lem-pbc-cartesian-unit-cohomology-transport is stated in
lean/Sheaf/AlgebraicGeometry/Curve/CartesianUnitCohomologyTransport.lean.
It concerns ordinary cohomology and the displayed/categorical pullback identification;
there are no etale sheaves, coordinates or compactness assumptions. The original
proof requires both results and proves their combination explicitly. No change
record is needed: existing signatures and public imports stay identical.

## Second reading by E1

1. Signatures and visibility: PASS. Diffed the item against the repository;
   its existing theorem signature is byte for byte unchanged. No existing
   definition or public import changed, no target changed, and no other existing
   module is adapted. The only existing node changes are proof, proof_deps and
   proof_origin. The two extra modules and their nodes are new.
2. Proof and data: PASS. All three delivered modules compile locally without
   warnings. The item has no sorry. Exactly the two reported public theorems have
   whole proofs by sorry. There is no forbidden declaration or hollow definition.
   coordinateIso uses the supplied section coordinates; etaleAdditiveSmul is
   sectionwise multiplication; etaleAdditivePullback is the concrete structural
   map transported through an adjunction. Existential comparison witnesses are
   eliminated only inside a theorem proof, never used to define data.
   Scratch copies compiled with #print axioms for every new definition, all
   three private coordinate helpers, the item and both split theorems. The
   definitions and helpers use only propext, Classical.choice and Quot.sound;
   the item and the two split theorems additionally use sorryAx as reported.
3. Split statements: PASS as a decomposition, not a completed axiom-free proof.
   The fixed-sheaf comparison removes all arbitrary coordinates, base rings and
   displayed cartesian transport; the ordinary transport removes the entire
   etale comparison. Both are strictly parts of the argument and neither is a
   renaming of the original theorem. Read their statements, proof docstrings,
   nodes, and the existing source-comparison, unit-coordinate and affine-Cech
   statements. Independent leanfinder, loogle and grep searches (logged in
   searches.jsonl), plus searches of lean/Sheaf and the upstream cohomology API,
   found no complete replacement. The existing fixed-scheme comparison supplies
   endomorphism naturality, not scheme inverse-image naturality. The upstream
   unit pullback isomorphism supplies the object isomorphism, not the required
   Ext transport square. Neither remaining hole closes in a few lines.
   Mathematically, degree zero is the structural section map, identity morphisms
   give identity transport, empty schemes and zero rings give zero unit groups,
   and nonflat base extension requires no tensor comparison isomorphism. On
   affine schemes higher unit cohomology vanishes. General separated cases use
   affine refinements and their acyclic intersections. Sources checked:
   [03P2](https://stacks.math.columbia.edu/tag/03P2),
   [01FD](https://stacks.math.columbia.edu/tag/01FD),
   [01F7](https://stacks.math.columbia.edu/tag/01F7),
   [02KH](https://stacks.math.columbia.edu/tag/02KH).
4. Route and pruning: PASS after documentation repairs. Read
   dag/units/sk-thm-p1.json realized: this item is below the unit level and the
   Artin-Schreier/coherent-cohomology route remains. Listed every removed direct
   old proof_dep above. No global module pruning is claimed. The proof-only new
   comparison imports in the item are plain imports. The public imports of
   the new modules provide declarations appearing in their signatures.
5. Nodes: PASS. The item node records the actual coordinate construction,
   scalar conjugation, adjunction square and two comparisons. proof_deps is the
   union of step uses. New nodes have self-contained statements, sources,
   proof plans, search records, split status, creation and blueprint provenance,
   the item's chapter/unit and matching Lean declarations. The ordinary
   transport plan explicitly uses the ordinary Mathlib clause of the unit-node
   match; it does not confuse tensorPullback with Modules.pullback.

Second-reader changes: corrected an error in the original theorem's proof docstring (inverse images of affine
opens need not be affine, so use a finite affine refinement on C'); made the
No longer needed dependency list explicit; added this independent review.
The hole accounting stays one original hole closed and two lower holes added
(net -1, a decomposition). No extra holes were introduced by the second reader.
