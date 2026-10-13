## What changed

Proved `AlgebraicGeometry.Etale.restrictedOverSingle_composition` in
`Sheaf.AlgebraicGeometry.RestrictedOverSingleComposition`, preserving its signature and
public import. Added six proved private helpers: `comp_hom_assoc`, `square_triangle`,
`square_coefficient`, `single_map_zero`, `inverse_eq_of_triangle`, and
`restricted_single_iso_hom`. The geometric helpers adapt the proved calculations in
`RestrictedAffineSingleConeNaturality`, without importing its preorder-specific module.
The proof specializes square naturality to the fixed coefficient sheaf and the identity
on its pullback to C, cancels the first coefficient isomorphism, and checks the complex
identity in degree zero and in the remaining zero components. The hom-formula helper
uses the existing defining equation `restrictedOverSingleIso.eq_1` and `asIso_hom`.
Local transparency settings keep inverse-image constructions from expanding during
geometric elaboration and allow the degree-zero component formulas to apply.
Updated the existing node's proof and proof origin to describe this calculation.
No definitions, existing signatures, public imports or other modules were changed.
The preflight conservatively requests a change record for the local attribute commands:
`coord/changes/restricted-over-single-composition-local-attributes.md` explains their
local scope and the absence of downstream effects.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.restrictedOverSingle_composition`
(node `lem-sbc-restricted-over-single-composition`). Added zero holes; none remain in
the delivered module. All six private helpers have complete proofs. No unproved
intermediate theorem is used. The full module compiled through `lcompile.py` without
warnings in 39.3 seconds against the published build.

## No longer needed

None. The existing data import and inverse-image composition node remain needed.
No new proof-dependency import was added. The preorder-specific transition composition
module is not needed, but it was neither an import nor a dependency of this item, so this
is not claimed as pruning from the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The unit realization record has no statement or
step realized by this node, and the prescribed restriction/associativity route is kept.
The initial published build lacked `RestrictedOverSingleData`; compilation resumed after
its publication. Kernel profiling identified expensive direct unfolding of the transition
isomorphism; its existing defining equation supplies the hom formula more directly.
The final calculation retains the exact objects and comparisons from the original
statement. Identity arrows, zero sheaves and empty schemes require no extra hypothesis.

## Second reading by X3

1. The module was compared with the repository version. The public import and the target
   theorem signature are unchanged byte for byte; only proof-local helpers and proof text
   were added.
2. The delivered file compiles with `lcompile.py` without errors or warnings, and contains
   no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The proof uses
   only the existing inverse-image composition result and elementary categorical identities.
3. The target statement is unchanged and the private helper calculations are true and
   strictly intermediate; no split-off statement or new node was added.
4. The proof follows the prescribed restriction and associativity route. No unit statement
   or realized unit step is bypassed, and no import can be removed from this module.
5. The DAG proof steps and proof origin now describe the actual coefficient-square and
   degree-zero/zero-component calculation. The original statement fields were restored
   verbatim; no definition or interface change was found.

Changed during second reading: restored the existing node's statement serialization from
the repository and added this review record. No mathematical or Lean proof change was
needed.
