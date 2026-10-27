# StandardBifunctorHomModel

## Reason

Construct the standard-sign model required by the native specialization without choosing
new product objects. The native row-sign complex, with its product projections rescaled by
(-1)^(n*p), satisfies the standard differential. All structure fields are proved; no data
are supplied by an unproved existence statement. The two separate representative-existence
lemmas specify universal derived extensions, uniquely up to the natural isomorphism preserving
their representative maps. Their objects are used only through those specified maps.

## Old

The new modules and their declarations were absent. The item contained one remaining hole,
AlgebraicGeometry.ProEtaleWeilSheaf.native_two_injective_hom_model.

## New

Three new modules provide nativeHomComplex and standardHomModel, the source representative
extension theorem, and the underlying representative extension theorem (with its two proved
additivity instances). Their full statements and constructions are in the delivered modules
and their Lean records. The item's existing public imports, signatures, options and the
already proved general comparison are unchanged. Its added imports are private proof imports.
The sign normalization is the identity on the underlying complex, with its required
(-1)^(n*p) components measured by the rescaled standard projections. No existing definition,
instance, simp attribute, visibility or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom | B4 | Constructs the standard models, combines both representative extensions, proves coefficient and sign fields, and applies the existing chain comparison and localization descent. |
| Sheaf.Algebra.Homology.NativeStandardHomRepresentatives | B4, new module | Uses the explicit source standard model in its statement. |
| Sheaf.Algebra.Homology.UnderlyingStandardHomRepresentatives | B4, new module | Uses the explicit target standard model in its statement; proves additivity. |

The two original direct importers, Sheaf.Algebra.Homology.RingedForgetTensorTransposition
and Sheaf.Paper.NativeWeilRowHomComparison, see the identical public interface. No source-tree
file or other existing module is adapted.

## Status

landed 20261026T235832-L-1459339 2026-10-26 (merge of deliver/B4/Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom)
