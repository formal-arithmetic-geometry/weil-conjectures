## What changed

Proved `AlgebraicGeometry.exists_tangentMap_linear` in
`lean/Sheaf/AlgebraicGeometry/TangentMapLinear.lean`, preserving its signature, visibility,
docstring, and both public imports. Added one private, fully constructed ring homomorphism
`tangentPairMap`, which changes coefficients in the two-direction square-zero algebra.

The proof follows all three steps of `lem-sc-tangent-map-linear`. Residue-field naturality
and the inverse residue-field isomorphism identify the base points. Compatibility with
reduction and inclusion of constants proves that the composite is a tangent vector over `k`.
Coefficientwise ring calculations prove compatibility with scaling, the two coordinate
projections, and the sum map. The selected module structures have the operation formulas
supplied by `exists_tangentVectors_vectorSpace`. Transporting a gluing of two source tangent
vectors through the coefficient-change map and postcomposing with `f` gives a gluing of their
images; applying the two addition formulas proves additivity. These identities bundle the
explicit composite into the required linear map.

Local compilation with the required `lcompile.py` wrapper passed without warnings. The
coefficient-change helper is constructed directly, with all ring laws proved; no new data
is selected from an existence statement. The gluing morphism is used only in the proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_tangentMap_linear` (node `lem-sc-tangent-map-linear`).
No `sorry` remains in the item, and no new holes were added. This is a proof from existing
statements, not a decomposition. Its existing dependency
`AlgebraicGeometry.exists_tangentVectors_vectorSpace` remains an upstream proof obligation
(node `lem-sc-tangent-space-vector-space`); it is not changed by this delivery.

## No longer needed

None. Both original public imports are required by the unchanged statement. Both planned
proof dependencies remain used: `lem-weil-pbc-residue-field-point-naturality` is the existing
Mathlib theorem `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`, available through
the original imports, and `lem-sc-tangent-space-vector-space` supplies gluing and the
operation formulas. No planned node or module is bypassed, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The DAG's three-step route works with the
existing signatures. Searches with LeanFinder, Loogle, the search wrapper's grep, and local
`rg` found cotangent maps and manifold tangent maps, but no shorter scheme dual-number
linearity theorem. No node update is required: the proof follows the existing route and
uses exactly its two proof dependencies.

## Second reading by U2

1. PASS: Compared the sole delivered module with the repository by `diff -u` and
   checked the existing declaration's docstring and signature byte for byte. The
   existing public imports and visibility are unchanged. Only the theorem proof and
   a private coefficient-change ring homomorphism were added; no change record is needed.
2. PASS: Independently compiled the delivered file using `lcompile.py`, without errors
   or warnings (12.1 seconds). Compiled a scratch copy with `#print axioms` for both
   declarations. `tangentPairMap` uses only `propext` and `Quot.sound`; the theorem uses
   `propext`, `Classical.choice`, `Quot.sound`, and the expected upstream `sorryAx` from
   `exists_tangentVectors_vectorSpace`. There is no local `sorry`, forbidden declaration,
   hollow definition, or arbitrary witness used as new data. The linear map's function is
   explicitly constructed; gluing is eliminated only inside its additivity proof.
   The existing choices of vector-space structures have their operations determined by
   the upstream zero, addition, and scaling formulas and unique gluing.
3. PASS: No statements were split off and no new nodes or holes were added. Read the
   coefficient-change construction and all local compatibility identities. They remain
   valid for zero scalars, zero vectors, and equal vectors, and specialize to identity
   coefficient change. The base-point and structure-map checks use the inverse residue
   isomorphism in the correct direction, with `hf` ensuring the map remains over `k`.
4. PASS: Read the proof from the conclusion downward: it constructs the prescribed
   composite, proves scalar compatibility coefficientwise, and proves addition by
   transporting the unique two-vector gluing and using both operation formulas.
   Independently searched LeanFinder for naturality of infinitesimal points preserving
   addition and scaling, Loogle for `TrivSqZeroExt, RingHom`, and local sources for
   tangent linearity and coefficient-change maps. The results give no shorter theorem
   for arbitrary scheme dual-number tangent vectors. Both public imports occur in the
   unchanged signature, so neither is proof-only or removable. Both old proof dependencies
   are used, and the report's empty pruning list is complete. Read
   `dag/units/sk-thm-picard-rr.json`: the unit's route and `realized` fields are unchanged.
5. PASS: Read `lem-sc-tangent-map-linear` and its upstream vector-space statement. The
   Lean proof implements its three steps and uses exactly its two `proof_deps`:
   residue-field point naturality and the tangent-vector vector-space construction.
   The addition formula already incorporates uniqueness, so applying it directly to
   the transported gluing realizes the planned uniqueness argument. The recorded proof
   and proof origin remain accurate; no node update is necessary.

Changes by the second reader: appended this independent review and its axiom-check
results. No Lean proof, signature, import, definition, or DAG edit was needed.
