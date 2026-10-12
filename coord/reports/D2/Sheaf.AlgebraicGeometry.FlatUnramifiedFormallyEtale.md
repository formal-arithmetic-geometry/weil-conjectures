## What changed

`AlgebraicGeometry.flat_unramified_formally_etale` now reduces unique lifting to the
universal first order thickening, the zero conormal calculation, and the zero-kernel
criterion for closed immersions. Its existing signature and public imports are unchanged.
Two new modules state strict substeps: `FlatOpenDiagonalConormalZero` and
`FirstOrderThickeningConormalZero`. The latter is proved using the existing
`Scheme.Modules.affine_conormal_sections` theorem, rather than left as a new hole.
All imports used only for proofs are plain imports.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.flat_unramified_formally_etale`.
New hole added: `AlgebraicGeometry.flat_openDiagonal_conormal_isZero`, node
`lem-weil-pbc-flat-open-diagonal-conormal-zero`. This is the only sorry in the delivery.
New auxiliary theorem proved without a local hole:
`AlgebraicGeometry.firstOrderThickening_isIso_of_conormal_isZero`, node
`lem-weil-pbc-first-order-thickening-conormal-zero`. The second reading closed the
first worker's hole in this auxiliary theorem.

This is a decomposition: one original hole closed and one new hole added, net zero.
The target still depends on open upstream statements, including universal-thickening
existence and affine conormal sections. No claim of an axiom-free target proof is made.

## No longer needed

Removed direct imports from the item (all with prefix `Sheaf.AlgebraicGeometry.`):
`FormallyUnramifiedConormal`, `TensorPullback`, `Thickening`,
`UniversalFirstOrderThickening`, `UniversalThickeningFlatBaseChange`, and
`UniversalThickeningOpenRestriction`. The first four remain available from imports
needed by the signatures or the intermediate lemmas; the last two remain proof-plan
imports of the open conormal lemma. Removed the redundant proof import `TensorPullback`
from `FlatOpenDiagonalConormalZero`. No module is claimed pruned from the target closure.

Every removed direct proof dependency of the item's old node is listed here:
`def-weil-pbc-conormal-sheaf-formally-unramified`, `def-pc-fibre-product`,
`def-weil-unramified-morphism`, `def-weil-open-immersion`,
`lem-weil-pbc-formally-unramified-base-change`, `lem-weil-pbc-flat-morphism-base-change`,
`lem-weil-pbc-universal-thickening-flat-base-change`, `def-pc-module-pullback`,
`lem-weil-pbc-universal-thickening-open-restriction`,
`def-sbc-closed-immersion-ideal-sheaf`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`, and
`def-weil-closed-immersion`. Their conormal/ideal roles move into the intermediate nodes;
the finite-type unramified definition is no longer needed for that conormal calculation,
since an open diagonal already gives formal unramifiedness. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's new nodes had empty dependency lists and single-sentence proof
summaries, rather than recording the argument and the existing statements used.
Their statements were raw Lean signatures, their blueprint ancestor was incorrect,
and their searches recorded unavailable services as no matches. The existing item's
node had not been updated to the implemented reduction. These records are repaired.
The square-zero ideal step can be proved from the existing affine conormal theorem
and Mathlib's `Ideal.cotangent_subsingleton_iff`, without adding another sorry.

## New nodes

`lem-weil-pbc-flat-open-diagonal-conormal-zero`: the conormal-vanishing part of the
04FF argument (old steps 2–5), without the universal lifting conclusion. Its statement
requires flatness and an open diagonal, and an explicit universal thickening. Finite
type is unnecessary in these steps. The four proof steps retain the original flat
base-change, open restriction, identity thickening and diagonal pullback calculation.

`lem-weil-pbc-first-order-thickening-conormal-zero`: the ideal-theoretic part of old
step 6. It assumes only a square-zero closed immersion with zero pulled-back ideal;
it neither assumes flatness of f nor asserts any lifting property. It is proved by
identifying affine sections with I/I², deducing I²=I=0, and using the closed-immersion
zero-kernel criterion. Both nodes cite the nearest blueprint ancestor
`thm-weil-pbc-finite-etale-lifting`, through the item's existing ancestry. No change
record is needed because no existing statement or definition changes.

## Second reading by D2

1. Compared the delivered item with the repository using `diff -u`: the entire
   existing declaration signature, docstring, visibility and four public imports
   are byte for byte unchanged. Only plain proof imports and the proof body differ.
   Both other modules are new; there are no forced adaptations or changed definitions.
   Verdict: pass.
2. Compiled all three modules in import order with `lcompile.py --all`; no errors or
   warnings. Scanned every Lean source: one sorry, exactly in the named conormal
   theorem; no forbidden declaration or hollow definition. Scratch `#print axioms`
   checks show only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` for the
   target, square-zero auxiliary and remaining hole. These
   sorries are the reported lower hole and existing upstream theorem holes.
   Existential elimination of X′ occurs only inside the proof of a proposition;
   no definition chooses arbitrary data from an unproved existence theorem.
   Verdict: pass as a decomposition, not an axiom-free completed proof.
3. Read [04FF](https://stacks.math.columbia.edu/tag/04FF),
   [04FE](https://stacks.math.columbia.edu/tag/04FE), and
   [01R3 (2)](https://stacks.math.columbia.edu/tag/01R3), and the imported universal
   thickening, base-change, open-restriction and affine-conormal declarations.
   The vanishing statement captures exactly the calculation before the lifting
   conclusion: open diagonal gives formal unramifiedness without finite type,
   flat base change identifies the conormals, restriction to the diagonal reduces
   to an isomorphism, and Δ followed by either projection is the identity.
   Tested the identity and empty-scheme cases (zero ideals), open immersions
   (identity universal thickening), and square-zero affine quotients: I/I²=I
   prevents a nonzero square-zero ideal from satisfying the zero-conormal hypothesis.
   No finiteness hypothesis is hidden. The square-zero auxiliary needs no universal
   property and is now proved. Neither intermediate restates the item's lifting
   statement. Re-searched with LeanFinder, Loogle and rg in Mathlib, the upstream
   sources and lean/Sheaf: related results give the closed-immersion criterion and
   cotangent lemma, but no existing scheme conormal-vanishing theorem. LeanSearch
   returned HTTP 500 and is recorded as unavailable. Blueprint search for conormal
   found only normal-bundle and curve-differential definitions, neither a duplicate.
   Verdict: true strict substeps; one lower hole remains.
4. Read from the target downward: the universal property's c is transported by
   inv j; the two commutative triangles use H.2.1 and hc, and uniqueness uses
   Mathlib `FormallyUnramified.hom_ext` with exponent 2 from the test thickening.
   A direct Mathlib Etale route needs local finite presentation, which the existing
   signature does not supply directly; the actual conormal route is retained.
   Inspected `dag/units/sk-thm-p1.json`: this item is not itself a realized unit step;
   the realized projective-line/curve/henselian route is untouched. The original
   conormal argument is retained under its new intermediate node, and the complete
   removed-direct-dependency list is above. Verdict: pass; no closure module pruned.
5. Updated the target's proof/proof_deps/proof_origin to the actual reduction.
   Repaired both new nodes' self-contained statements, stmt_deps, complete proof
   steps and their union of uses, source places, exact multiline Lean signatures,
   recorded searches, and blueprint ancestry. The proved auxiliary's dependency
   is the existing affine conormal theorem; the remaining hole retains precisely
   the base-change/open-restriction statements of the original conormal route.
   Existing node fields outside the stage-3 allowance are unchanged. Verdict: pass.

Changed in this second reading: proved the square-zero auxiliary, removed one redundant
proof import, repaired all three DAG proof records and the report, and corrected the
hole accounting to one closed original hole and one new lower hole.
