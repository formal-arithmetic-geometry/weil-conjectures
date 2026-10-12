## What changed

Proved the unchanged `AlgebraicGeometry.Etale.epi_higher_image_colimit_comparison`
from affine raw-class descent and the already proved canonical module-coefficient
presheaf comparison. The Lean proof precomposes with colimit coprojections, uses
hB and the specified isomorphisms, detects raw-comparison equality on the dense
affine etale site, and then uses local surjectivity and sheaf separatedness.
It makes no claim of global lifting of arbitrary affine higher-image sections.
No statement or definition was changed. The target's existing docstring is retained.

Added `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep`, with the
strictly smaller affine raw-class step stated as a named theorem. Its statement
contains neither K, B, eK, eB, nor any sheaf-colimit conclusion. It only treats
sections in the image of raw cohomology on affine objects. Added a DAG attachment
for the exact already proved module-valued local-comparison declaration, so the
proof does not cite an abstract abelian comparison for canonical module naturality.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.epi_higher_image_colimit_comparison`
(node `sbc-lem-higher-image-colimit-comparison-epi`), with a complete cancellation
proof from the new affine raw-class theorem and the existing source comparison.
There are no sorries left in the item's module.

Added and left: `AlgebraicGeometry.Etale.exists_higher_image_raw_affine_image_rep`
(node `sbc-lem-higher-image-raw-affine-image-rep`). This is one named public theorem
whose entire proof is `by sorry`, with its source and natural-language proof.
This delivery is a decomposition: one upper hole closed and one lower hole added,
not a claim of a fully sorry-free continuity theorem. No other Lean declaration
or hole was added. The local-comparison attachment records an existing theorem.

## No longer needed

Removed direct proof imports from the item's module:

- `Mathlib.CategoryTheory.Sites.Abelian`.
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`.
- `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`.
- `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The last module is available through the statement import; no redundant direct
import is needed. The direct proof dependencies on
`lem-weil-pbc-filtered-category-exists-directed-final`,
`lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-injective-module-abelian-acyclic`, and
`lem-weil-pbc-etale-cohomology-limit-complex-systems` move into the raw-class
step's plan. They are not claimed globally unnecessary.

`sbc-lem-higher-direct-image-presheaf` and its abstract abelian-isomorphism module
are not used by the implemented proof. The stronger, already proved canonical
module-valued comparison from the source library supplies local surjectivity.
`lem-weil-pbc-sheaves-colimit-sheafification` is unnecessary for this route:
colimit.ι_desc and cancellation prove epimorphy directly. No finite-cover gluing,
eventual-zero representative, or injectivity argument is needed.

## Where the brief, the DAG or earlier work was wrong

The original listed presheaf theorem gives an abstract abelian-sheaf isomorphism;
it does not itself state the natural canonical module comparison needed here.
The source library already proves precisely the latter in
`isLocallyBijective_higherDirectImagePresheafToSheaf`, and the added attachment
records that exact declaration without adding a Lean theorem.

The existing abelian raw affine representative and affine limit-class theorem
use a directed poset, variable abelian coefficients, and a colimit coefficient
sheaf. They do not directly give the present module-valued statement with an
arbitrary cofiltered index and fixed pulled-back coefficients. No cyclic parent
continuity theorem is imported.

hK is not mathematically needed for the cancellation argument once B is a cocone
and hB specifies its legs. Its binder is preserved, and referenced explicitly to
avoid an unused-variable warning. No unit statement or realized unit step changes.
The new raw theorem retains the continuity route of the original plan.

Edge cases checked for the new statement: a singleton index gives the identity
transition; zero coefficients give only zero classes; in negative degrees raw
cohomology vanishes, and cofilteredness supplies a stage for the zero class.
The affine-object restriction is essential: no global representative for a
non-quasi-compact etale object is asserted. No flatness of Λ is assumed.

## New nodes

`sbc-lem-higher-image-raw-affine-image-rep`: affine raw module classes have a stage
representative after the canonical comparison. New module:
`lean/Sheaf/AlgebraicGeometry/HigherDirectImageRawAffineImageRep.lean`.
It isolates the cohomology-continuity and map-identification step, leaving
sheaf local generation, affine density, and the colimit proof to the parent.

`sbc-lem-module-higher-image-raw-comparison-locally-bijective`: an attachment to
the already proved source declaration
`AlgebraicGeometry.Etale.isLocallyBijective_higherDirectImagePresheafToSheaf`.
It has no new Lean file and no new sorry. Searches found the exact theorem in
the source module and no DAG record carrying that exact statement.

## Second reading by V2

1. The delivered target module was diffed against the repository. Its theorem
signature and all existing declarations are unchanged; only the proof and imports
changed. Verdict: pass.
2. Both delivered Lean modules compile through `lcompile.py`; the target has no
remaining `sorry`, and the sole lower hole is the named theorem
`exists_higher_image_raw_affine_image_rep`. No forbidden declarations or hollow
definitions were found. Verdict: pass.
3. The lower statement is a strict affine raw-class reduction, with a source,
natural-language proof, and matching DAG node. Searches found no existing exact
declaration. Its edge cases and fixed coefficient interpretation were checked.
Verdict: pass.
4. The proof uses the canonical source comparison, affine density, local
surjectivity, and sheaf separatedness. Removed imports and obsolete dependencies
are recorded above; the unit route is retained. Verdict: pass.
5. The target and new node proof, dependencies, origin, and Lean records agree
with the implementation. Verdict: pass.

Changed only this report for the second reading; no Lean statement or definition
was changed.
