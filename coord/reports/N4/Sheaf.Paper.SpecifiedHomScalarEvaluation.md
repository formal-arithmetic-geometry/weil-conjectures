## What changed

Proved `WeilConjectures.specifiedHomScalarEvaluation`,
`WeilConjectures.specifiedHomScalarCoherence`, and
`WeilConjectures.specifiedHomScalarRationalEvaluation` in the assigned module.
A proved private helper `specifiedHomIdentified_eq` cancels the three completion
isomorphisms, identifying the specified map with `scalarHomOrdinary`.
The integral evaluation theorem uses `scalarInternalHom_complete`, invertibility
from `scalarCompletion_existsUnique`, the actual `scalarHomCompleted` construction,
and the inverse law of closed transposition. Integral coherence specializes the
Hom clauses of `scalarOperationsOrdinary_unit` and `scalarOperationsOrdinary_tower`.
Rational evaluation is definitionally the localized completed comparison.

Existing signatures, definitions, attributes and public imports are unchanged.
The node's proof records this direct route and retains its remaining chain and
rational plans. No change to the unit route, no interface repair, no consumer adaptation.
All private proof imports were redundant through the existing public imports;
removed them after the initial successful compile and rechecked the file.

## Proved and sorry left

Closed 3 of the original 6 holes; added 0 holes; split off 0 statements.

- Proved `WeilConjectures.specifiedHomScalarEvaluation`.
- Proved `WeilConjectures.specifiedHomScalarCoherence`.
- Proved `WeilConjectures.specifiedHomScalarRationalEvaluation`.
- Remaining `WeilConjectures.specifiedHomScalarChain`.
- Remaining `WeilConjectures.specifiedHomScalarRational`.
- Remaining `WeilConjectures.specifiedHomScalarRationalCoherence`.

All six declarations belong to `lem-zl-specified-hom-scalar-evaluation`.
The three remaining holes are the original named public theorem proofs, with
unchanged signatures and their existing complete proof docstrings; no partial
proof contains a hole. This is a partial delivery of a multi-hole module, not
a decomposition that moves any of these original statements under new names.
The proved statements use the declared dependencies `scalarInternalHom_complete`,
`scalarCompletion_existsUnique`, `scalarHomOrdinary_isIso`, and ordinary coherence,
which remain separate proof obligations of their owning module.

## No longer needed

Removed these private imports (existing public imports and all declarations are preserved):

- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `WeilConjectures.Algebra.Homology.HomComplex`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.SfRationalizationKaroubi`.

The proved evaluation and coherence clauses do not need the representative-chain
calculation: the ordinary comparison is already defined as the evaluation transpose,
and the completed comparison is already its explicit completion conjugate.
Consequently they use neither `ringedFiniteFreeHomBaseChange` nor a new choice of
K-flat or K-injective representative. The standalone chain assertion still requires
its original proof plan and dependencies. No DAG node or library module is withdrawn;
no claim is made that any original dependency is globally unnecessary, since all
original chain and rational assertions remain in scope.

## Where the brief, the DAG or earlier work was wrong

The node's old Step 5 described an independent chain calculation as prerequisite
to the displayed comparison identity. The existing Lean definitions already fix
that identity by explicit conjugation, so cancellation proves it directly while
the standalone representative-chain theorem remains a distinct obligation.
The rational evaluation formula likewise unfolds directly to `scalarHomCompleted`.

The current blueprint's `def-weil-derived-pullback-tensor-hom.md` is now in
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/`
`sk-prop-sf-open-closed-triangle/`, and describes operations uniformly for
condensed coefficient rings. The historical common-stage paragraph cited by this
node/module is absent from that current definition. This delivery preserves the
assigned mathematical statements and definitions, and reports the source-reference
drift rather than silently changing them.

Attempted completed-Hom naturality to prepare the rational proof. Its cancellation
argument reduces to completion-unit naturality, but a final rewrite encountered
an elaboration/transparency mismatch between scalar-reduction target presentations.
That exploratory private helper was removed; it contributes no new hole or API.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
