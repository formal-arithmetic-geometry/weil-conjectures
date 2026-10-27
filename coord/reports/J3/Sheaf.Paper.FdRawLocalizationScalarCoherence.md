## What changed

Completed `WeilConjectures.FdRawLocalization.rawLocalizationScalarCoherence` from the
strictly smaller localization theorem `rawLocalizationScalarDescent`. The remaining theorem
is exactly original plan steps 1–3: raw localization with exact shifts, the actual integral
component, identity normalization, the three-field equation and both unit substitutions.
It contains neither four-field contraction nor their equality.

The proof in the item supplies original steps 4–6 in Lean. For the left contraction it maps
the h,k cocycle through P_m, uses naturality of j_m at the framework associator, and applies
the h.trans k,m cocycle. For the right contraction it uses naturality of the PBC associator
at j_h, applies the k,m cocycle at S_h K, and then the h,k.trans m cocycle. Functor map_comp
and category associativity combine the results. The published framework associator pentagon
then equates the two framework contractions, including repeated fields.

Moved the 18 existing presentation declarations verbatim into
`Sheaf.Paper.FdRawLocalizationScalarData`, publicly re-exported by the original module.
This prevents the descent theorem from importing the theorem that uses it. The move is
needed by the argument dependency order; it is not a compile-time split. The original
signature and all 18 moved declaration signatures and bodies were checked for exact
textual equality by the project's declaration parser. No consumer module exists in the
current Lean import graph; the DAG parent still needs the original theorem, which remains.

The original private semilinear localization import is now private in the descent module.
Updated the item node to the actual descent/naturality/pentagon argument and recorded the
new theorem and shared presentation in two nodes. Change record:
`coord/changes/J3-fd-raw-localization-scalar-data.md`.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.FdRawLocalization.rawLocalizationScalarCoherence`
(node `lem-fd-raw-localization-scalar-coherence`). The theorem is proved from the descent
statement and the existing framework pentagon, with both four-field calculations explicit.

Added one hole:
`WeilConjectures.FdRawLocalization.rawLocalizationScalarDescent`
(node `lem-fd-raw-localization-scalar-descent`). It is a public theorem in its own module,
with the whole proof `by sorry`, its source and full proof in words. There are zero holes
in the data module and zero in the delivered item module. This is a decomposition, not a
net proof gain: holes closed 1, holes added 1, net 0. No data is defined using an arbitrary
witness of this theorem. The family and comparison are bound inside the theorem proof;
the prescribed HEq functors, shifts and integral components fix them.

Edge cases: inclusions are always non-strict; all naturality and cocycle calculations
apply unchanged to identities, repeated adjacent or fully equal fields, zero objects and
empty schemes. Localization is used only in the forward direction, never as faithful.

## No longer needed

No mathematical dependency or module is pruned from the target closure. The original
module no longer directly imports `Sheaf.CategoryTheory.SemilinearScalarLocalization`;
that proof import belongs to the descent module and remains needed there. The original
three public imports are preserved transitively through the data module.

The item node now uses the descent node and `def-weil-algebraically-closed-coefficients`
(the published associator_cocycle). Its direct proof edges to
`def-weil-rationalization-karoubi`, `def-weil-pbc-rational-category`,
`def-weil-linear-scalar-localization`, `prop-weil-pbc-scalar-extension`, and
`lem-pur-semilinear-scalar-localization` are moved to the descent argument, not globally
removed. The item's old top-level approved tool-use entries are removed because these
uses now occur in the descent node. All unit statements and proof steps are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction or target change was necessary. The generic semilinear
localization result does not by itself discharge identification of the specified raw
coefficient functors and shifts; this specialization is the remaining descent theorem.
The four-field steps are genuine elementary naturality/cocycle calculations, as planned.

The newest blueprint trace-function file is now under `sk-cor-plancherel` and contains
the trace definition; the existing item's older source records the coefficient-comparison
auxiliary extraction. The delivery preserves that already-reviewed auxiliary statement
and its full route. `coord/delivery-errors.md` has no section I despite the standing
brief's reference; its existing sections and the current stage-3 rules were consulted.

## New nodes

`def-fd-raw-localization-scalar-data` owns the 18 existing comparison presentations moved
without any body or signature change. It includes U,C,I,J, the specified scalar and
integral associators/units, RationalFamily, RawComparison and the three diagram maps.
Its public module is `Sheaf.Paper.FdRawLocalizationScalarData`.

`lem-fd-raw-localization-scalar-descent` records exactly original plan steps 1–3, with
no four-field conclusion. Its theorem is in
`Sheaf.Paper.FdRawLocalizationScalarDescent`. Generic scalar localization is reused;
there is no duplicate of the existing general semilinear theorem. Searches included
LeanSearch, LeanFinder/Loogle, Mathlib grep, project grep, and blueprint_refs searches.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
