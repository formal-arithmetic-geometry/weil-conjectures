# Pullback composition mate proof scope

## Reason

The static interface check classifies added local attribute commands as an interface
change. This record documents the proof elaboration settings needed to avoid repeatedly
unfolding composite module direct images and scalar restrictions. No existing statement,
definition body, universe, binder, visibility or public import changes.

## Old

`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit` had the original public
import of `GlobalHomAdjunctionIso`, the global derived-category instance parameter,
and one theorem with a sorry. It had no local irreducibility commands or private
formal mate helpers. The maximum heartbeat budget was 800000.

## New

The original public import, instance parameter and theorem signature are identical.
Two non-public proof imports supply the two counit subcalculations. Private, fully
proved helpers give the mate transpose identity and its forward Hom-equivalence form.

The added `[local irreducible]` attributes name `derivedPullback`,
`Scheme.Modules.tensorPullback`, `schemeHomPullbackAdjunction`,
`CategoryTheory.Functor.rightDerivedFunctor`,
`CategoryTheory.Functor.rightDerivedFunctorUnit`, `CategoryTheory.Adjunction.comp`
and `DerivedCategory.Qh`. They apply only within the item module.
The lazy projection and weak-head unfolding options are disabled during elaboration.
Linting is disabled only for the large theorem declaration, following the existing
composition-unit proof. Elaboration and kernel checking remain enabled; the original
800000 heartbeat budget and the compiler's 60-second limit are unchanged.

Three new modules carry the two strictly smaller counit calculations and a concrete
common counit expression. The latter has a proved construction equation and introduces
no new choice. One counit calculation remains a named sorry; the other is proved.
These additions change no existing mathematical interface. All four delivered modules
compile without warnings, in respectively 17.4, 33.6, 16.2 and 19.6 seconds.

## Users

| module | holder | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit | F4 | proof elaboration only |
| Sheaf.AlgebraicGeometry.DerivedDirectImageSquareMate | unclaimed in this checkout | no effect; the used theorem signature and public imports are identical |

`Sheaf.AlgebraicGeometry.DerivedDirectImageSquareMate` is the direct existing importer
and user of `AlgebraicGeometry.derivedPullbackComposition_mate_unit`. It needs no edit.
The local attributes and options are not exported. No downstream adaptation is forced,
and none is delivered. Target meanings and statements are unchanged, so no target
statement review is reopened by this proof-scope change.

## Status

landed 20261014T040539-L-999793 2026-10-14 (merge of deliver/F4/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit)
