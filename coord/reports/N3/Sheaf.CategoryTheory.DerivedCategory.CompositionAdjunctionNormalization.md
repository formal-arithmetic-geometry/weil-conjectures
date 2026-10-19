## What changed

Proved `CategoryTheory.Adjunction.derivedCompositionAdjunctionNormalization` from the
concrete derived-functor API. Retained and checked the earlier sandbox proof against the
current sources. Its private `compIso_hom_eq_conjugate` helper generalizes the source
`rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv` argument to independent Hom universes.
The witness is the specified conjugate; the derived composition comparison proves its
representative equation, and the conjugation identities prove both normalization equations.
The existing public theorem signature and `derivedCompositionLeftIso` definition are unchanged.

Updated `lem-sfb-derived-composition-adjunction-normalization` to record this proof route,
including its Mathlib derived unit/counit factorization leaf. No unit statement or realized
step is bypassed. The unit's concrete K-injective convention is implemented by the existing
Grothendieck resolution instance and the right-derived functors already in the statement.

Change record: `coord/changes/N3-composition-adjunction-normalization-proof-context.md`.
It documents the private helper's section variables and local composition instances and the
removal of the unused public import. No existing mathematical interface or target meaning
changes. No consumer adaptation is required.

Validation: the retained pruned item compiles again against current sources (6.5 seconds), and compiling the item followed by
its unchanged direct consumer `Sheaf.SixFunctors.DetSfCompCompositionBaseChange`
succeeds (5.5 and 10.6 seconds). The initial delivery probe accepted all declaration axioms.
The downstream scan lists 62 transitive consumers and 10 direct importers; all ten
direct importers compile unchanged against the pruned module (2.4 to 27.0 seconds each).

## Proved and sorry left

Closed 1 of 1 sorries:
`CategoryTheory.Adjunction.derivedCompositionAdjunctionNormalization`
(node `lem-sfb-derived-composition-adjunction-normalization`).
Added 0 sorries; split off 0 statements. No sorry remains in the item or is added elsewhere.
The private helper is completely proved.

## No longer needed

Removed these imports from the original module:

- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors` (formerly public): the concrete
  `mapDerivedCategoryRightDerivedAdjunction` already in the statement supplies the specified
  adjunction; the general essential-constancy existence theorem is unnecessary.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`: the canonical derived unit/counit
  factorization equations give the needed comparison without constructing Hom colimits.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: Grothendieck resolutions
  support the concrete upstream `rightDerivedFunctor` already fixed in the statement.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: no direct K-injective Hom-bijection
  calculation is used; the remaining upstream imports already supply K-injective notions.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` and
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`: their composition and
  termwise-adjunction APIs remain used, but the public `RightDerivedFunctor.Adjunction`
  import already supplies them, so these direct imports are redundant.

Also removed the earlier sandbox's provisional proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate`:
its comparison lemma has a common Hom universe and is not applied. The private proof uses
the smaller existing `RightDerivedFunctor.Adjunction` API directly.

Removed proof dependencies `def-sfb-right-derived-functor`,
`lem-pc-pre-derived-adjoint-functors-general`, `lem-weil-pbc-kinjective-hom-derived`,
and `lem-pc-derived-adjoint-functors`. The generic derived-adjunction Mathlib leaf
`lem-sc-derived-adjunction-from-underived` supplies the factorization equations instead.
Removed the obsolete top-level tool approvals for
`lem-pc-pre-derived-adjoint-functors-general` and `lem-pc-derived-adjoint-functors`;
the termwise-adjunction approval is retained.

These modules and nodes are unnecessary for this proof; other users may still need them.
The statement dependencies, including the derived-category conventions, remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The source `CompConjugate` theorem requires a common Hom universe, whereas this theorem
permits independent Hom universes. Its proof generalizes verbatim in a private helper;
no hypotheses or universes of the public theorem are restricted.
The previous report incorrectly described unused imports as needed and omitted the
proof-route update. Those omissions are repaired here. The initial dry run also required
a change record for the helper's section commands; that record is included.

Earlier delivery attempts stalled on shared worktree capacity. No launcher script or
capacity setting was changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
