## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_cupCech_total_cochain_map` in
`Sheaf.Paper.CupCechTotalCochainMapExists`, with its existing signature unchanged.
The map is constructed directly, without choosing a witness of an unproved existence theorem.
Private helpers establish global-section bilinearity, extend the signed row formula over
both total-degree coproducts and the tensor product, prove the Cech and resolution
Leibniz identities, and check the total signs and cochain identity on generators.
The alternating-face calculation is proved directly from the Cech differential formula,
finite-sum cancellation, and the restriction-compatible pairing `D.pair`. The existing DAG route is retained.
The elaboration options are scoped to individual declarations.
No other existing modules or interfaces were changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_cupCech_total_cochain_map`
(node `new-cup-cech-total-cochain-map`).
There are no remaining holes in the delivered module, and no holes were added.
All private constructions and helpers are proved; this is a proof, not a decomposition.
The complete file compiles within the 60-second limit. The delivery axiom probe accepts
every declaration, and the dry run passes all checks except the second reading, which
the next worker supplies. Nothing was pushed.

## No longer needed

All existing imports and the three existing proof-dependency nodes are used.
The temporary import `Mathlib.Algebra.BigOperators.Fin` was removed: the required
finite-sum lemmas are already available through the existing imports.
No new dependency modules are needed. The temporary development modules are excluded
from the delivery; their proved helpers are private in the item's module.

## Where the brief, the DAG or earlier work was wrong

No statement or proof-plan correction was necessary. The data supplied by
`CupResolutionPairing`, together with Mathlib's total-coproduct and tensor APIs, suffice.
The proof treats arbitrary Cech index types and arbitrary nonnegative degrees; it introduces
no inhabitedness, covering, positivity, or augmentation assumptions.


## Second reading by H4

1. **Unchanged interface: pass.** Read the whole delivered module and its diff against
   `lean/Sheaf/Paper/CupCechTotalCochainMapExists.lean`. The signature of
   `AlgebraicGeometry.Scheme.Modules.exists_cupCech_total_cochain_map` is byte-identical,
   as are the imports. All added constructions and lemmas are private. The existential
   cochain map, every natural degree, both degree equations, and the signed tensor-row
   normalization remain exactly as stated. No definition used by another module changes.

2. **Proof and axioms: pass.** Compiled the delivered file with `lcompile.py`: no errors
   or warnings, 31.5 seconds. Compiled a full scratch copy ending with `#print axioms
   AlgebraicGeometry.Scheme.Modules.exists_cupCech_total_cochain_map`: only `propext`,
   `Classical.choice`, and `Quot.sound` (33.6 seconds), with no `sorryAx`. Checked the source
   for `sorry`, forbidden declarations/attributes, and lines over 100 characters: none.
   `cupCechPairLinear`, `cupCechSignedRow`, `totalDescBilinear`, `cupCechTotalLinear`, and
   `cupCechTotalComponent` explicitly construct their data; the final witness is
   `CochainComplex.ofHom` of those components and their proved commutation law.

3. **Split statements and edge cases: pass.** There are no split-off statements or new
   nodes. Read the bilinearity, omitted-face cancellation, resolution Leibniz, and total
   Leibniz proofs. `aw_sum` cancels the last left term against the first right term and
   also works when either face degree is zero. The front/back maps share exactly one
   vertex. Empty index types require no tuple choices; all row evaluations are vacuous.
   Zero cochains and characteristic two cause no exception: only additive identities
   and integer scalar actions are used. No cover, inhabitedness, or positivity premise
   has entered the proof.

4. **Shortest route, imports, and pruning: pass.** Repeated searches using LeanFinder
   for a natural bilinear resolution pairing on total Cech complexes, Loogle for
   `mapBifunctorDesc`, and grep for `Alexander.?Whitney|cupCochain|cup.*leibniz|leibniz.*cup`.
   Loogle's coproduct constructor and its normalization are already used. No direct
   Mathlib replacement was found. Searched the upstream Cech files and `lean/Sheaf`;
   `moduleCup_awSummand_leibniz` instead concerns integer-indexed complexes of
   cosimplicial sheaves and a sheaf morphism, so using it here would require additional
   constructions and transports. The direct tuplewise calculation is appropriate.
   All three imports occur in the public target signature. Each old proof dependency
   is still used, so `## No longer needed` has no omitted node or module.

5. **DAG agreement and unit route: pass.** Read `new-cup-cech-total-cochain-map` and all
   three dependency records against their Lean declarations. Its first step is realized
   by global-section bilinearity, the two total coproduct extensions, and tensor lift;
   its second by `D.restriction`, `D.leibniz`, omitted-face cancellation, and generator
   extensionality. Thus `proof`, `proof_deps`, and `proof_origin` still describe the code.
   Read Stacks 07MB (`cohomology-equation-needs-signs`) and the associated discussion in
   Section 20.25, and checked the resolution-first convention using `total_d_ι`.
   The four exponents are `i*s`, `i*s+r`, `i*s+r+s`, and `i*s+r+s+i`; the right resolution
   exponent differs from the tensor expression by `2*i`, as proved in `hsign`.
   The existing cube unit route and its `realized` record are untouched; this delivery
   supplies its existing lower-level signed-map step and bypasses no unit.

**Changes after reading:** clarified the report's description of the direct alternating-face
proof and added this independent review with compilation, axiom, search, and route evidence.
No Lean proof, signature, import, definition, or DAG edit was necessary. The delivery closes
one original hole and adds zero holes: proved 1 of 1, split off 0, pruned none.
