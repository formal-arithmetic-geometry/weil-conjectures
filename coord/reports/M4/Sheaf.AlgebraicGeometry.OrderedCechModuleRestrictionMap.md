## What changed

Completed `orderedCech_module_restriction` without changing its signature or public
imports. Added proof-only imports of
`WeilConjectures.Topology.Sheaves.CechComparison` and
`Mathlib.Algebra.Homology.Embedding.CochainComplex`.

A proved private helper `orderedCechModuleCoordinate_d` transports the extended
pushforward differential through `extendXIso`, applies `hd`, expands the usual
Cech differential using `TopCat.Presheaf.cechComplexFunctor_d_π`, and identifies
the face restriction composites using uniqueness of arrows between opens.
The main proof constructs additive presheaf maps with the inverse of `a`, proves
naturality using `hn` and coordinate naturality, and proves local linearity using
`hl` and coordinate scalar compatibility. It applies `ha` and the helper to
establish the chain equation. Negative components are the unique maps into the
zero negative terms of `K`; the negative chain equations follow from the zero
negative terms of the extended source, including the boundary from -1 to 0.
The coordinate formula follows directly from `a.apply_symm_apply`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.orderedCech_module_restriction`
(node `lem-pc-ordered-cech-module-restriction-map`): 1 of 1 original holes.
The private helper `orderedCechModuleCoordinate_d` is also completely proved.
No holes remain in the delivered module; no holes or new modules are added.

## No longer needed

None. The original coordinate module remains necessary; both added proof imports
are used. The DAG's original route and proof dependency on
`def-pc-ordered-cech-module-coordinates` are retained. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous report incorrectly said the coordinate module already supplied a
differential identity. It supplied additive, zero, scalar, and naturality
identities only. The missing differential identity is now proved locally from
the existing source-library Cech face formula, rather than left as a new hole.
No statement or definition changes were necessary.

Searches: LeanFinder returned generic cochain-map constructors, not an ordered
Cech restriction theorem. Loogle did not index the source-library face lemma;
msearch grep returned no hits. Direct rg located the proved
`TopCat.Presheaf.cechComplexFunctor_d_π` in
`WeilConjectures.Topology.Sheaves.CechComparison` and the analogous calculation
in `OrderedCechDegreewiseProjectionDifferential`; the proof uses the face lemma
without importing the signed-projection machinery.

Edge cases: the construction never chooses a tuple, so empty covers and degrees
with no increasing tuples are included. No affineness, separation, or nonempty
intersection assumptions are introduced. Negative source degrees, specifically
-1, are handled using `isZero_of_isStrictlyGE`.

## Second reading by M4

1. **Visible declarations and statements.** Compared the delivered module with the repository version. The theorem signature and all existing declaration interfaces are byte-for-byte unchanged; only proof-only imports and proof bodies were added.

2. **Compilation and axioms.** Compiled the module with `lcompile.py` successfully. The proof contains no `sorry`, hollow definition, axiom, unsafe, opaque, extern, or implemented_by. The helper is private and fully proved; the public theorem is fully proved.

3. **Statement and proof quality.** The theorem still asserts exactly the ordered restriction cochain map and coordinate identity. The local differential calculation is a strictly internal proof helper, with no new public statement or weakened hypothesis. The construction handles empty tuple index sets and the negative degree boundary.

4. **Shortest route and pruning.** The coordinate identities from the dependency module are used directly. The added Cech comparison and cochain embedding imports are proof-only and both are used; no existing import or proof dependency is redundant. The unit route and its realized coordinate dependency are retained.

5. **DAG and source consistency.** The proof follows the DAG route: sectionwise inverse coordinates, naturality and linearity, differential compatibility, then zero negative components. No split-off holes or new nodes were introduced, and the target statement remains unchanged.

Changed only the report by adding this second-reading record; no Lean declarations or DAG statements were altered.
