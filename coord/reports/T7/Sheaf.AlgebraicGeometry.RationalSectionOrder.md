## What changed

Filled `AlgebraicGeometry.Scheme.Modules.rational_section_order` in
`Sheaf.AlgebraicGeometry.RationalSectionOrder`, preserving its entire statement verbatim.
Added two proved private helpers: `coefficient_order_nonneg` obtains a local scalar from
the generic-stalk image formula; `span_germ_of_freeGenerator` proves that the germ of a
local free generator spans the stalk. Generator independence follows by applying valuation
nonnegativity to both coefficient ratios.

For finiteness, represent the rational section by an actual section near the generic point,
write it in a local free generator, and take the basic open of its coefficient. The coefficient
is a unit at each point of this open, so the section germ generates there. Independence then
makes every order on this open zero. The existing proved finite-complement theorem finishes.
Only proof imports changed: added `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator`.
The DAG proof and dependencies now describe this argument. No definitions, public imports,
public signatures, target statements, or consumer modules changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.rational_section_order`
(node `lem-sc-rational-section-order`). Both clauses have complete Lean proofs.
Added zero holes; split off zero statements. No `sorry` remains in the delivered module.
The proof uses the existing named dependency
`AlgebraicGeometry.Scheme.Modules.invertible_module_generic_stalk`, which still has its
previous hole in the shared library; this delivery does not change it.

## No longer needed

Removed redundant private imports `WeilConjectures.AlgebraicGeometry.Curve` and
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`; their statement support is already
provided by the unchanged public imports.

The route no longer uses `lem-sc-integral-function-field-affine-fraction`: a rational
section is itself a germ, so a representative section and its local coefficient give the
generating basic open directly. It also no longer applies `lem-sc-dim0-finite` separately:
the existing proved `lem-sc-nonempty-open-complement-finite-dim-le-one` supplies exactly the
finite complement needed. No module is withdrawn: the fraction-field statement is Mathlib,
and the dimension-zero theorem and replacement finite-complement theorem share
`WeilConjectures.Mathlib.Topology.KrullDimension`, which remains imported.
The unit's statement and realized proof step are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The old plan unnecessarily constructs an affine fraction
for a generic germ and reproves a finite-complement fact already available in the adopted
source library. The replacement follows the same Stacks 02SG argument and keeps its
nonempty generating open and finite-support steps. The finite-complement lemma is an
existing proved general topological tool from another unit; its statement is used directly.
The local free-generator definition also already exists in the adopted source library.
No new nodes or change records are needed.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
