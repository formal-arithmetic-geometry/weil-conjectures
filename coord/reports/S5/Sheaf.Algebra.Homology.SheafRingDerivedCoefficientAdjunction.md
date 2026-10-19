## What changed

Proved `SheafOfModules.sheafRingDerivedCoefficientAdjunction` without changing its
statement or public imports. Two new modules isolate and prove the ordinary coefficient
adjunction and the derived Hom comparison. No definitions or existing statements changed. The resumed check confirms that the main theorem's
signature is textually identical to the current shared source. Both new modules now carry
module-level source and blueprint references as well as their theorem docstrings.

The ordinary proof reuses the private sectionwise construction in
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`: extension/restriction Hom
maps followed by sheafification give the adjunction, transported to the prescribed E.
Its Hom formula reduces by cancellation of equality transports. Exactness follows by
reflection through the exact forgetful functor to abelian sheaves.

The derived comparison uses K-flat resolutions and the resolving-class essential
constancy theorem for incoming denominators. Its private `inverted_indDiagram`
constructs outgoing cocones from inverse denominator images and verifies the split
criterion. The existing derived-adjunction compatibility theorem gives the required
Hom identity for the supplied universal pair. The item derives the unit, inverse
transpose and counit equations explicitly. Uniqueness of left derived functors
transports the K-flat comparison from the existing derived-change-of-rings theorem.

## Proved and sorry left

Closed the original hole in `SheafOfModules.sheafRingDerivedCoefficientAdjunction`
(node `lem-pur-sheaf-ring-derived-coefficient-adjunction`). Also proved the two new
public theorems `SheafOfModules.sheafRingCoefficientOrdinaryAdjunction`
(`lem-pur-sheaf-ring-coefficient-ordinary-adjunction`) and
`SheafOfModules.sheafRingDerivedHomComparison`
(`lem-pur-sheaf-ring-derived-hom-comparison`). All private helpers are proved.

Actual direct hole counts: item 1 -> 0; new modules 0 -> 0. No holes added or split
through to future work. Existing imported sorries remain dependency work, including
`derivedChangeOfRingsIndependentCoefficients`; the item is proved from its stated API.

Validation: all three modules compiled together via lcompile.py, and the retained proofs
were checked again with `lcompile.py --all` on 2026-10-19. The first dry run flagged only
the added single-declaration `omit` / `set_option ... in` commands; their exact scope,
the identical original signature and all direct users are now documented in
`coord/changes/S5-sheaf-ring-derived-coefficient-proof-scopes.md`. No direct sorry,
axiom, unsafe declaration or data chosen from mere unproved existence was introduced.

## No longer needed

Removed these proof-only imports from the item:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Paper.PbcCompletedPullbackActual`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`

K-flat resolution and exact factorization are used in the new proved comparison.
The generic pre-derived and everywhere-defined derived-adjunction wrappers are
replaced by the direct compatibility theorem. The completed-pullback and cochain-model
modules have no role in this homotopy-pair argument. The general ringed-topos adjunction
is replaced by the existing private same-site sectionwise construction, reproduced as
private helpers because the original is private and its module imports unrelated
completed coefficient theory. The ordinary module needs neither the derived exact-functor
public import nor the homotopy-adjunction public import from the retained split skeleton.
Original public imports of the item remain unchanged.

Removed the parent's direct tool approvals for
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-exact-functor-derived-functor`, `lem-pc-derived-adjoint-functors`,
`lem-pc-pre-derived-adjoint-functors-general`, and `lem-pc-kflat-resolution`.
The relevant remaining tools occur below the two proved intermediate nodes.
No unit statement or step is bypassed: the unit's realized statement and steps are empty.

## Where the brief, the DAG or earlier work was wrong

The retained attempt claimed that only the topological-space ordinary adjunction was
available. A newer arbitrary-site ringed-topos theorem also exists, but identifies its
universes. More usefully, the scalar-reduction module already contains a private
same-site adjunction proof at independent universes; this delivery reuses that proof.
The source-library sheafification module supplies finite-colimit preservation by toSheaf,
so restriction exactness needs no new sheafified-cokernel argument.

The retained split's exactness witnesses had unconstrained module universes; the new
ordinary statement explicitly uses coefficient universe r, as required by the item.
The item's original signature is unchanged. A stale new-node signature containing
old docstring text was replaced by the actual Lean signature. The current
`lem-pur-derived-change-of-rings` attachment uses a cochain-model interface, while its
existing `derivedChangeOfRingsIndependentCoefficients` theorem supplies the homotopy
universal pair actually needed here. No definition was altered.

Checked identity ring maps, zero rings and complexes, and nonflat ring maps: no
flatness of the map, boundedness or equality of site universes enters the proof.

## New nodes

`lem-pur-sheaf-ring-coefficient-ordinary-adjunction` realizes Steps 1–2, sourced from
Stacks 03D7/03DA, and is proved here. Its conclusion is only the normalized ordinary
adjunction and exactness, with no derived statement.

`lem-pur-sheaf-ring-derived-hom-comparison` realizes the Hom compatibility part of
Steps 3–4, sourced from Stacks 09T5/0FND and 06YY/07A6, and is proved here. It has no
K-flat comparison, unit, inverse-transpose or counit normalization conclusions;
the item proves those consequences separately. Both nodes retain the earlier actual
LeanSearch, LeanFinder, Loogle and source grep searches. The change record is
`coord/changes/S5-sheaf-ring-derived-coefficient-proof-scopes.md`; it documents the scoped
commands flagged by preflight. No consumer adaptations are needed: every existing
signature and visibility stays unchanged. The resumed downstream scan found five actual
declaration users (plus the item), including the newer IntegralConstantCompletion,
CoefficientEvaluationDerivedLeftAdjoint, and ConstantRealizationDerivedScalarExtension
uses; each remains compatible with the unchanged signature. The required dry run passed
compilation, axiom probes and preflight on 2026-10-19 (review class CODEX).

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
