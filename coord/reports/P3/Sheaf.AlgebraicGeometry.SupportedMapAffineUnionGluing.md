## What changed

Reduced `AlgebraicGeometry.Scheme.exists_supported_map_affine_union_gluing` without changing
its signature. The proof first constructs compatible supported perfect data on W and V,
then glues those data on Y=W union V. Two new geometric steps have dedicated modules and
nodes. The main module proves the nested transported restriction composition directly,
then a general categorical helper proves the biproduct/shift restriction equation and
transports it to the arbitrarily supplied comparison c. Neither helper has a hole.
No ambient extension, arbitrary unproved witness used in a definition, or interface change
is introduced.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_supported_map_affine_union_gluing`
(node `lem-sc-supported-map-affine-union-gluing`).

Added two holes, each the whole proof of a named public theorem:
- `AlgebraicGeometry.Scheme.exists_supported_affine_overlap_map`
  (node `lem-sc-supported-affine-overlap-map`, module `SupportedAffineOverlapMap`).
- `AlgebraicGeometry.Scheme.exists_supported_relative_open_gluing`
  (node `lem-sc-supported-relative-open-gluing`, module `SupportedRelativeOpenGluing`).

This is a decomposition of one hole into two strictly distinct geometric steps, not a
sorry-free proof or a positive net hole count. The item's theorem has no remaining sorry.
The affine lemma produces no object on the union; the relative gluing lemma requires
actual compatible local objects and does not construct them. The main proof combines both
and proves the full restriction comparison calculation itself.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.AffinePerfectMapLift`,
`Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension`,
`Sheaf.AlgebraicGeometry.DerivedOpenGluing`, and
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh` from the main module. These remain
needed through the two new modules: no corresponding node or transitive module is pruned.
The original node's proof dependencies now point to the two finer steps and the open
localization theorem; its former affine/gluing dependencies move to those steps.
The full list of old `proof_deps` no longer used directly by the main proof is
`def-pc-perfect-complex`, `lem-pc-derived-open-restriction-qcoh-iff`,
`lem-sc-affine-perfect-support-extension`, `lem-sc-affine-perfect-map-lift`, and
`lem-sc-derived-open-gluing`. The perfect-complex definition remains a statement dependency;
the other four nodes are used by the two new steps. None is globally pruned.
No mathematical dependency is declared globally dispensable.

## Where the brief, the DAG or earlier work was wrong

The plan does not state the transport of the affine construction to relative overlap
functors, or supported perfect gluing through the open-scheme equivalences. Existing
`derived_open_gluing` gives local identifications and maps, but does not itself assert
perfectness or support, and is phrased with opens of the union scheme rather than opens
of the ambient X. These are the two new tasks, with source-derived proofs in their
docstrings and nodes. The original theorem and its plan are mathematically consistent.
Mathlib search found `Modules.overMapCompOverEquiv`, and `overMap` composition is
sufficiently definitional to construct the nested restriction isomorphism without a hole.
LeanSearch returned Internal Server Error; LeanFinder and Loogle supplied only generic
complex lifting lemmas and restriction/biproduct comparisons. Source reading used Stacks
Tags 09IM, 08EK, 08EH and 08DG. The unit's realized fields impose no extra intermediate
node here, and its proof route is unchanged.

## New nodes

`lem-sc-supported-affine-overlap-map` splits the local strictly perfect model transport,
affine support extension, and affine map lifting into a reusable statement that constructs
only the W/V data. Sources: Tag 09IM, using Tags 08EK and 08EH. Empty opens, empty overlap,
and empty T obey the same construction. No U, union object, or arbitrary comparison c
occurs in this conclusion.

`lem-sc-supported-relative-open-gluing` glues supplied supported perfect objects and
compatible maps on arbitrary ambient opens. Sources: Tag 08DG and local perfectness
Tag 08CM. No affine, compactness, closedness of T, or stabilization hypothesis occurs.
The same pointwise proof handles empty cover members and empty union.

Both nodes record all three Mathlib search kinds and complete natural-language proof
steps. No change record is required: all existing signatures and visibility are preserved.

## Second reading by P3

1. **Unchanged interfaces — pass.** Diffed all three delivered modules against the
   repository: only `SupportedMapAffineUnionGluing` already exists. Extracted the text
   from its theorem name through `:= by` and checked byte equality with the repository.
   The signature, universes, all localization assumptions, support hypotheses, and the
   quantifier over arbitrary `c` are unchanged. The added definition is private and is
   an explicit composite of associators, an equivalence unit, and identity isomorphisms;
   it chooses no witness from an unproved existence statement. No change record is needed.

2. **Proof and axioms — pass.** Compiled the two new modules without errors or warnings.
   Compiled a scratch copy of the entire main module, including its proof, with
   `#print axioms AlgebraicGeometry.Scheme.exists_supported_map_affine_union_gluing`:
   the output was exactly `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`.
   The corresponding scratch checks for both split declarations gave the same list.
   There are exactly two `sorry` tokens in the delivered source, each the complete
   proof of the public theorem listed above; none occurs in a definition or helper.
   Checked all sources for forbidden axiom, unsafe, opaque, extern, and implemented_by
   constructs. The restriction-composition definition cancels the intermediate
   over-equivalence; the categorical helper proves the map equation first for `k`,
   then uses naturality of `k.symm ≪≫ c`. Its shift isomorphism affects only the second
   summand, so no unmentioned shift compatibility of `c` is used.

3. **Split statements — pass.** Read [Tag 09IM](https://stacks.math.columbia.edu/tag/09IM),
   [Tag 08EK](https://stacks.math.columbia.edu/tag/08EK),
   [Tag 08EH](https://stacks.math.columbia.edu/tag/08EH),
   [Tag 08DG](https://stacks.math.columbia.edu/tag/08DG), and
   [Definition 08CM](https://stacks.math.columbia.edu/tag/08CM), and the actual upstream
   declarations `exists_perfect_supported_extension`, `exists_perfect_map_lift_of_isAffine`,
   and `derived_open_gluing`. The affine step uses quasi-separatedness only to make
   intersections of quasi-compact opens quasi-compact; it never assumes the intersection
   is affine. Closedness and quasi-compact complement pull back to the affine member.
   The support-preserving augmentation in map lifting supplies exactly the support needed.
   In the gluing step the object and compatible maps are supplied as hypotheses, and
   perfectness and stalk vanishing are local on the two opens. No boundedness of the target,
   quasi-coherence of the two local sources beyond perfectness, or closedness of T is needed.
   Tested empty W, empty V, empty intersection, empty union, T empty, T equal to X, and
   W=V: the local conditions are vacuous where appropriate and the same constructions work.
   The affine step has no union object; the gluing step has no affine construction and
   accepts arbitrary local objects. Neither is a renamed copy of the item.
   Repeated searches with different words: LeanFinder's “Descent of perfect complexes and
   morphisms along a binary open cover” returned generic Mayer–Vietoris and scheme gluing
   results; grep “perfect.*gluing|gluing.*perfect|supported.*overlap” found no exact match.
   Loogle `CategoryTheory.Functor.mapBiprod` returned the comparison already used by the
   helper. Also searched `lean/Sheaf`, `lean/WeilConjectures`, and the slopmaster2 source:
   no existing declaration combines these relative supported interfaces. The two new
   theorem docstrings give the construction and support/perfectness argument in words.
   Formalizing their geometric transport is substantial work, not a few-minute closure.

4. **Shortest route and pruning — pass after report repair.** The main proof genuinely
   combines the affine data and the local gluing result, then proves the nested restriction,
   biproduct, shift, and arbitrary-comparison calculations. The public imports serve existing
   signatures; both new imports are proof-only. The new modules publicly import exactly
   the perfect-complex, restriction-map, and affine definitions their statements use.
   Read `dag/units/sk-thm-picard-duality.json`: its realized statement and step arrays are
   empty, so no realized node is bypassed. The two-open route of 09IM is preserved.
   The original report omitted the explicit list of former `proof_deps`; added all five
   removed direct dependencies and explained why none is globally pruned.

5. **DAG correspondence — pass after citation repair.** Checked each new node's declaration,
   verbatim Lean statement, hypotheses, module, source, creation record, blueprint ancestry,
   searches, proof steps, and union of step uses. The main node's first two steps name exactly
   the affine and gluing declarations applied by the Lean proof and its localization choices.
   Added `def-pc-derived-open-restriction-maps` to the third step and to `proof_deps`, since
   `schemeDerivedOpenRestrictionCompIso` is explicitly used there. The last step is the
   naturality calculation actually proved by `stabilized_map_restriction`.

Changes in this reading: completed the `No longer needed` dependency list, added the
restriction-comparison DAG citation, and formatted the two new nodes' prose mathematical
statements as TeX without changing their content. Trial removal of broad local instance
registrations did not improve compilation reliably and was reverted; delivered Lean code
is unchanged from the first worker. The main proof's scratch axiom check compiled in 55.2 s;
other attempts hit the wrapper's 60 s limit, so delivery compilation is checked again below.
This remains a decomposition: one original hole closed and two lower holes added, net -1.
