## What changed

Completed `WeilConjectures.IntegralSystemRealization.Recursion.integralRealizationRecursion`
in its existing module. All existing signatures, definitions and public imports stay
unchanged. Added proved private helpers only. The proof uses actual normalized
reconstruction, explicit triangle and naturality calculations for proper/open
comparisons, and two inductions on the expression tree: one for the equations and
one for uniqueness. It retains the stipulated full child domains and both tensor slots.

Replaced the proof import of `Sheaf.Paper.NormalizedDVREffectivity` by
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` and
`Sheaf.Paper.SfDerivedCompleteLegacyComparison`; added private Mathlib imports
for the auxiliary finite-field datum (ZMod and its algebraic closure). Updated the item's node to this proof route.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.IntegralSystemRealization.Recursion.integralRealizationRecursion`
(node `lem-pur-integral-realization-recursion`). Added zero holes. No `sorry`
remains in the delivered Lean module; no statements were split off.

Validation: the final module compiled cleanly through lcompile.py in 16.7 seconds
(exit 0, no warnings). Existing definitions and the theorem signature were also
compared textually against the shared source and are verbatim unchanged.

## No longer needed

Removed the direct proof import `Sheaf.Paper.NormalizedDVREffectivity`; actual
reconstruction supplies the needed invertibility directly. Effectivity is still
used transitively by that reconstruction theorem.

The proof no longer needs the old direct proof dependencies
`lem-pur-unary-counit-transpose` (`Sheaf.CategoryTheory.UnaryCounitTranspose`),
`lem-pur-binary-counit-transpose` (`Sheaf.CategoryTheory.BinaryCounitTranspose`),
`lem-sf-integral-expression-recursion` (`Sheaf.SixFunctors.IntegralExpressionRecursion`),
or the existence theorem `lem-sf-integral-compactification-system-realization`.
Its Realizations data are already given, with the precise primitive recursion
fields. The generator-reduction theorem itself is not applied; its published
pullD, tensorD and inverseOrZero definitions are used unchanged.
These are removals of proof-dependency edges, not claims that the whole library
has stopped importing those modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier DAG proof predates the current Realizations recursion interface and
plans a second coefficient-transposition argument. Its conclusion follows more
directly from the current fields, after checking the proper/open comparisons
against the definitions in this item. No mathematical statement was weakened.
The current blueprint source is under sk-thm-sf-compatibility, whereas the old
snapshot source path used sk-thm-sf-package.

The existing intrinsic/legacy completeness comparison is needed to connect
sfIntegralConstructible to the actual reconstruction theorem; this is the
same input-completeness bridge used by IntegralComparisonRecursionLaws. Its
auxiliary finite-field datum is in universe zero, independently of the given D.
No geometric restriction or new input hypothesis is added.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
