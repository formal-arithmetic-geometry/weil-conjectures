## What changed

Replaced the proof of `CategoryTheory.Mod.sheaf_localizedBasisCoefficients` without changing
its statement or the predicate `LocalizedBasisCoefficients`. Constructed the map Q explicitly
by regular-module lifts on each biproduct summand. Proved its summand formulas and canonical
square, constructed an inverse using module localization, and proved both inverse equations
and the required uniqueness. The private helpers prove the finite-biproduct and regular-module
identities for arbitrary index universes, including the empty index type.

Added `Sheaf.CategoryTheory.LocalizationLinearDescent`, stating the independent module
localization universal property of Stacks Tag 0EMD, expressed in the existing internal module
interface. The new result concerns every A-module and every R-linear map from T; it contains
no basis or finiteness assumption. The upper proof uses it for two different modules.
Updated the item's DAG proof to agree with this argument and added the lower node.

The only preflight objection was two file-level elaboration options; both now scope
only their individual proofs. No persistent option command is added.

Validation: both modules compiled together with `lcompile.py --all`, with no errors or
warnings (2.6 seconds and 7.3 seconds in the final checked run). No source-library module,
public existing signature, definition or target was changed.

## Proved and sorry left

Closed the original hole in `CategoryTheory.Mod.sheaf_localizedBasisCoefficients`
(node `lem-sfb-localized-basis-coefficients`). There are zero sorries in the assigned module.

Added one hole: `CategoryTheory.Mod.sheaf_localization_linearDescent`
(node `lem-sfb-localization-linear-descent`). Its proof is exactly `by sorry`, and its
module and node contain the source and full fraction-and-gluing proof in words.
This is a decomposition: one upper hole closed, one independent lower hole added, net zero.
No other holes are introduced. Every private helper is proved; no definition contains sorry.

## No longer needed

Removed the original proof-only imports
`Mathlib.CategoryTheory.Sites.PreservesSheafification` and
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` from the assigned module.
Its proof no longer directly uses `lem-sfb-ring-localization-sheafification`,
`lem-pc-sites-sheafification-underlying-sets`, or
`lem-weil-pbc-site-sheafification-sections-local`: these are dependencies of the remaining
module localization result instead. They are not claimed as pruned from the targets.
The direct finite-coordinate denominator-clearing, local-surjectivity and local-injectivity
steps of the old upper proof are replaced by the module universal property and two explicit
inverse equations. No existing module or DAG node is withdrawn; no unit step is bypassed.
All existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is sound. Its ring localization model does not itself state
the module universal property of Tag 0EMD. This is the genuine separate result retained here.
The available sectionwise/internal equivalence and `sfbRingLocalizationSheafification` have
size constraints requiring passage to a small equivalent site before applying them at the
item's full independent universes. The new node records that transport rather than assuming
that section rings of a sheafified localization are objectwise localizations.

Searched Mathlib with LeanSearch, LeanFinder/Loogle and source rg; ordinary module localization
is present (`IsLocalizedModule.is_universal`, `LocalizedModule.lift`, and
`LinearMap.extendScalarsOfIsLocalization`). Read the internal/sectionwise module equivalence,
the ring localization model, the scalar localization telescope results, and
`localization_restrictScalars_fullyFaithful`. None directly states the required internal
linear descent for arbitrary universal ring localizations on an essentially small site.
The last theorem proves full faithfulness for the particular sectionwise ring localization,
not extension of maps from an unlocalized algebra.

Checked the new statement mathematically at t=1, t=0, nilpotent t, zero rings/modules, and
sites without points. At t=1 it is ordinary restriction along isomorphisms. If t is nilpotent,
A and B and every unital A-module are zero, so the unique-map assertion holds. The proof uses
killing powers followed by invertible action, never cancellation or a nonzero-divisor
assumption. Finite-index arguments in the upper proof include the empty index type.

## New nodes

`lem-sfb-localization-linear-descent` in
`dag/nodes/sec-proetale-coefficients/lem-sfb-localization-linear-descent.json` realizes the
Tag 0EMD universal property for the R-module underlying T and an arbitrary A-module N.
It is strictly independent of the specified finite basis, and the upper proof combines
its two applications with an explicit biproduct construction. Its source, proof steps,
Mathlib searches, blueprint ancestry and exact Lean statement are recorded. No change
record is required because no existing statement or definition changes.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
