## What changed

Proved `AlgebraicGeometry.WeilSheaf.frobeniusPowStr_constantFieldRestriction`
with its original signature, carrier construction, attributes, and public imports.
The item was initially copied from its quarantine archive; the shared source has
since been restored centrally with the same interface.

The proof works with underlying sheaf maps. It transfers ordered addition of
Frobenius pullbacks to inverse-pushforward maps, handles the zero summand by the
unit law, and proves transport of iterates by induction using the existing
pushforward exchange coherence. A private explicit sheaf-map wrapper prevents
expensive conversions through adic module actions. A proved private restatement of the existing `transportCommIso_eq` identity
identifies the transport comparison explicitly before projecting to underlying
maps, avoiding definitional unfolding of the adic comparison. Importing its
broader source module timed out during imports, so the private identity uses
the same direct reflexivity proof with the smaller coherence import.

Added two proved coherence modules, one public statement per module:
`ConstantFieldTransportComparisonFactors` proves the factorisation-form comparison
using the existing composition identity twice and a factor triangle checked on
sections. `ConstantFieldTransportComparison` uses the existing full-square factorisation
and cancels the first upper-star factor to give the compositor square.
The compositor cancellation is proved at the natural-transformation level before
taking its component, avoiding expensive kernel conversion through chosen adjoints.
They provide a small proof API for the transport module; no adopted source-library file is changed. The item proof imports
`WeilConjectures.WeilSheaf.BaseChangeField.Coherence` and
`Sheaf.DeligneLaumon.ConstantFieldTransportComparison` privately.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.WeilSheaf.frobeniusPowStr_constantFieldRestriction`
(node `lem-zl-source-constant-field-transport-structure`).

The two added public helper statements are proved:
`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv_exchange_factor`
(node `lem-zl-source-constant-field-comparison-factors`) and
`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv_exchange`
(node `lem-zl-source-constant-field-comparison-square`).

No new proof hole is added, and no sorry remains in any delivered module.
The cases m=0 and r=0 are included. No definition takes data from a sorry.

Validation: all three delivery modules passed the compiler in import order.
`#print axioms` for the original theorem and both added public helpers reports
exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The temporary audit module was removed before delivery.

## No longer needed

Both original public imports and both original declared dependencies remain
needed. The planned separate r=0 argument and pullback-associativity calculation
are unnecessary: inverse-pushforward addition and exchange give one induction.
No source-library declaration, node, or module is withdrawn. No module is pruned.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined rather than withdrawn. Its rework row identified the
archive used initially; its current restored shared source has the same public
interface. No mathematical statement or existing definition was changed.

The original plan separated r=0. Ordered addition with a zero second summand
allows one induction for every r. Direct conversions at explicit composite
isomorphisms caused expensive unfolding of canonical adjoint comparisons; the
proved coherence API keeps the composite abstract through cancellation.

`blueprint_refs.py ancestor` returns None for this module-based created.item
chain. The new nodes therefore copy the existing item's explicit blueprint
ancestor, `thm-zl-real-mixed-by-curves`, and prepend the item node to its recorded
via chain. Blueprint and local DAG searches found no duplicate generic square.

## New nodes

`lem-zl-source-constant-field-comparison-factors`, in
`Sheaf.DeligneLaumon.ConstantFieldTransportComparisonFactors`, is the generic
factorisation-form square. Its proof combines the two canonical comparison
composition identities using a lower-star triangle proved on sections. It is
proved, with no new hole, and changes no existing interface.

`lem-zl-source-constant-field-comparison-square`, in
`Sheaf.DeligneLaumon.ConstantFieldTransportComparison`, is the compositor form
needed by the original theorem. Its proof uses the existing factorisation of `upperStarCompIso`, cancels the first
upper-star factor, and cancels the inverse first compositor after precomposition,
while keeping the common composite abstract. The public API supplies the composite after cancellation and is then
stated as an equality of natural transformations. The transport application
specializes the inverse isomorphism at that level and then takes the component,
retaining the original hom and inverse expressions. It is proved, with no new hole. No change record
is required because all added interfaces belong to new modules.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
