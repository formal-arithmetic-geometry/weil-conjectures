## What changed

Proved `CategoryTheory.TwistedActionRingedSite.restrictionHomComparison_isIso`
without changing its statement or the canonical map definition. The independent,
fully proved translation-comparison and conjugate-action arguments are in the
new modules `Sheaf.CategoryTheory.TwistedActionTranslationHomComparison`,
`Sheaf.CategoryTheory.TwistedActionHomPairCurrying`, and
`Sheaf.CategoryTheory.TwistedActionTensorHomNaturality`, imported privately along
the proof dependency chain. No other existing Lean module or public import
changes. Updated the item's proof plan to the fixed-pair argument actually used.

Translation's Hom comparison follows from its equivalence, natural tensor
comparison and Yoneda. The conjugate Hom action then defines a genuine fixed
pair. Currying identifies equivariant Hom maps with equivariant tensor maps.
Full faithfulness of `P.modules` supplies the inverse bijection on Hom sets;
essential surjectivity and Yoneda identify the canonical comparison as an
isomorphism. The proof uses only existing definitions and the data supplied by P
and T, and introduces no chosen witness of a sorried existence theorem.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.TwistedActionRingedSite.restrictionHomComparison_isIso`
(node `lem-sf-twisted-action-restriction-hom-comparison-iso`).
Added 0 holes; split off 0 unfinished statements. The new helper theorem
`CategoryTheory.TwistedActionRingedSite.homPair_currying` is fully proved
(node `lem-sf-twisted-action-hom-pair-currying`). No sorry remains in any of the four modules. The additional proved theorem
`CategoryTheory.TwistedActionRingedSite.isIso_translationHomComparison` has node
`lem-sf-twisted-action-translation-hom-comparison`; it adds zero holes. The general naturality calculation
`CategoryTheory.TwistedActionRingedSite.tensorHomComparison_precomp` is also proved
(node `lem-sf-tensor-hom-comparison-precomposition`), adding zero holes.

## No longer needed

No existing import was removed; the sole public import is still needed by the
statement. This proof does not require `lem-sf-integer-action-slice-equivalence`
(`Sheaf.CategoryTheory.IntegerActionSliceEquivalence`) or the separate
`def-weil-presheaf-modules-sheafification` proof dependency. Removed these edges
from this item's proof plan. The former module remains available to its other
consumers; no module is withdrawn.

The comparison follows from tensor naturality and the diagonal-action equation;
`T.tensor_pure`, ring transport on slices, and a sectionwise sheafification
calculation are unnecessary here. The generic sheaf tensor and tensor-Hom
adjunction remain necessary. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan calls for transporting a concrete integer-action slice
normalization to the abstract Site record in P. This is avoidable: P already
supplies the fixed-pair equivalence, and T supplies natural tensor comparisons
and their diagonal actions. These imply the claimed canonical Hom comparison by
an entirely categorical argument. No mathematical statement was corrected.

Searches: launcher LeanFinder found groupoid-functor internal Hom constructions
and monoidal reflection, neither a direct specialization to these fixed pairs;
Loogle had no declaration for the source-library Hom API. Local rg searches
located the private translation-comparison proof in the parent module and the
source tensor-Hom adjunction. The parent cannot be imported because it depends
on this item; its proved translation argument is adapted as private helpers.
The slice-Hom helpers of NativeRingedRestrictionHom and ElementRestrictionHom
are not needed. The empty site, zero ring and zero modules satisfy the same
adjunction argument without additional nonemptiness assumptions.

## New nodes

`lem-sf-twisted-action-hom-pair-currying` records the fully proved invertibility
of the conjugate Hom action and its equivariant currying criterion, in
`Sheaf.CategoryTheory.TwistedActionHomPairCurrying`. It concerns base-site fixed
pairs only and is strictly one part of the restriction comparison argument.
No hole has been moved to it. Its sole public theorem states both properties of
the same explicit action; all construction helpers are private.

The initial combined file typechecked completely but took 83 seconds. A private
irreducible translation comparison and a named theorem supplying the proof of
the fixed-pair construction were added; the combined file still exceeded the
60-second limit. The self-contained proved helper was then extracted. No
transparency check or time limit was disabled. No change record is needed:
existing public statements, definitions and attributes remain unchanged.

`lem-sf-twisted-action-translation-hom-comparison` records the fully proved
invertibility of the canonical Hom comparison for the translation equivalence,
in `Sheaf.CategoryTheory.TwistedActionTranslationHomComparison`. The currying
helper imports this theorem privately. This further extraction follows the
helper's clean 60.8-second typecheck, and isolates the independent equivalence
argument from conjugate-action currying. It introduces no unfinished proof.

Performance improvements also replace repeated local functor records in the
restriction proof with a named private composite functor, and use the action
morphism directly in the currying helper instead of repeatedly reducing a
fixed-pair record. These are private implementation changes only.

`lem-sf-tensor-hom-comparison-precomposition` records the general, fully proved
naturality calculation for the transpose of a supplied tensor comparison, in
`Sheaf.CategoryTheory.TwistedActionTensorHomNaturality`. It assumes neither
faithfulness nor an action-site presentation and does not assert invertibility
of any Hom comparison. It isolates the last independent calculation when the
main module remained slightly over the compile limit. No hole was introduced.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
