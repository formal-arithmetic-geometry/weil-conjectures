## What changed

Proved the body of AlgebraicGeometry.koszul_basicOpen_exact without changing its
signature or any existing declaration. The proof follows the original route:
extend the generator homotopy, sheafify and restrict it, and compare the zero
homology map with an invertible scalar map.

Added Sheaf.RingTheory.KoszulGeneratorHomotopy. Its public theorem
ExteriorAlgebra.koszul_generator_homotopy is proved by an explicit construction:
left exterior multiplication by Finsupp.single i 1. Private, proved helpers
construct that linear map and prove the contraction identities in degree zero
and successor degrees. This does not use any new unproved algebraic statement.

Added Sheaf.AlgebraicGeometry.BasicOpenTildeScalarIso, with the one remaining
localization interface theorem. It applies to every complex and every scalar;
it makes no reference to the Koszul sequence or exactness. Its source and full
proof in words are in its docstring and node. The basic-open invertibility is
also supported by Mathlib's
Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen. Identifying tilde.map of
a scalar identity with sectionwise scalar action is the unfinished bridge.

The item's new imports are proof-only. Its four original public imports stay,
since its unchanged signature requires them. The existing node now records the
proved assembly and its two intermediate declarations.

## Proved and sorry left

Closed the sole original hole: AlgebraicGeometry.koszul_basicOpen_exact
(node lem-r4-koszul-basic-open-exact). No sorry remains in the item's module.

Also proved ExteriorAlgebra.koszul_generator_homotopy
(node lem-k3-koszul-generator-homotopy), with no local holes. Its three private
helpers generatorWedge, generatorWedge_identity, and generatorWedge_zero_identity
are complete, and generatorWedge contains no postponed proof or arbitrary choice.

Added exactly one hole: AlgebraicGeometry.basicOpen_tilde_scalar_isIso
(node lem-k3-basic-open-tilde-scalar-iso), whose complete body is `by sorry`.
It is the only sorry in the delivered files. This is a decomposition with one
hole closed and one added, not a claim of a net decrease in reachable holes.

All three modules compile together through lcompile.py in import order. Edge
cases checked in the mathematical argument: r=0 has no index i; a=0 and
nilpotent a give an empty basic open, where module sheaves are zero; the zero
ring and zero complex are allowed. The degree-zero homotopy identity is proved
separately in Lean, rather than assuming a differential into degree -1.

## No longer needed

None. No original import, node, or module is pruned. All three original DAG
proof dependencies supply notions used by the unchanged statement and the proof.
The parent still follows exterior multiplication and inversion on the basic open;
no blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node's two steps cited definitions only: no stated theorem supplied
either the generator homotopy or the scalar isomorphism on a basic open. The
first gap is now proved; the second is isolated as a general localization theorem.

The local checkout has the literature indexes but not the referenced Stacks TeX
files. The source was read directly at the official Stacks pages for Tags 0626,
0663, 01HR, and 09IR. Tag 0626 is the contraction homotopy identity; Tag 0663 is
its generator specialization. No unsupported source was substituted.

An exploratory proof of the localization theorem found the sectionwise unit
lemma in Mathlib, but unfolding the bundled fully faithful tilde construction to
identify its scalar action was expensive and did not complete. That exploratory
proof is not delivered; the remaining theorem has exactly `by sorry`.

## New nodes

lem-k3-koszul-generator-homotopy: a proved chain-level statement for the explicit
Koszul complex, independent of any sheafification or open restriction. Its node
records the exterior multiplication construction and its two degree cases.
Module: Sheaf.RingTheory.KoszulGeneratorHomotopy.

lem-k3-basic-open-tilde-scalar-iso: the general scalar isomorphism after tilde and
restriction to D(a). It is a strict part of the argument: it assumes no Koszul
complex and concludes no exactness. It is true even for arbitrary unbounded
complexes, since scalar inversion is degreewise and commutes with linear maps.
Module: Sheaf.AlgebraicGeometry.BasicOpenTildeScalarIso.

No definition or statement changes and no forced adaptations; no change record.

## Second reading by K3

1. I compared the delivered item module with the repository version. The theorem signature of
`AlgebraicGeometry.koszul_basicOpen_exact` is byte-for-byte unchanged; only proof-only imports and
its proof body were added. The two added modules are new declarations, and their DAG statements
match their Lean signatures.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile without errors.
The item has no remaining `sorry`. The only remaining `sorry` is the named theorem
`AlgebraicGeometry.basicOpen_tilde_scalar_isIso`, which is documented and has node
`lem-k3-basic-open-tilde-scalar-iso`. No forbidden declarations or hollow definitions occur.

3. The split theorem is strictly weaker than the item and is true for arbitrary integer-indexed
complexes: it asserts only invertibility of scalar multiplication after restriction to `D(a)`,
with no Koszul or exactness conclusion. The homotopy theorem is a direct exterior multiplication
construction, and its degree-zero and successor identities are proved separately. Searches and
edge cases are recorded in `searches.jsonl` and the report.

4. The proof follows the planned route: the generator homotopy, extension to cochain degrees,
additive tilde and open restriction, then scalar invertibility and vanishing of the homology map.
The unit route is retained; no original imports or proof dependencies were pruned.

5. The DAG proof dependencies and proof steps agree with the imports and declarations used in the
Lean proof. No statement or definition change, forced adaptation, or change record is needed.

I changed only this second-reading report section; the proof files and node statements were left
unchanged after compilation.

Additional verification: a scratch copy compiled through `lcompile.py` with explicit
`#print axioms` for all three public theorems. `ExteriorAlgebra.koszul_generator_homotopy`
uses only `propext`, `Classical.choice`, and `Quot.sound`. The scalar lemma and the
assembled exactness theorem use these plus `sorryAx`, exactly as expected from the
one reported localization hole. Independently searched for invertible elements acting
bijectively on associated module sheaves, `tilde.*smul|smul.*tilde|map_smul|isIso_of_components`,
and localized-map scalar identities; no existing complete replacement was found.
The rank-one case has homotopy from exterior degree zero to one and the proved zero-degree
identity. Zero or nilpotent scalars have empty `D(a)`, where sheaf section modules are zero;
unit scalars are invertible on the entire affine scheme. These checks support the exact
strength of the remaining statement. The unit record has empty `realized.statement` and
`realized.steps` arrays; this delivery changes neither its statement nor its route.
