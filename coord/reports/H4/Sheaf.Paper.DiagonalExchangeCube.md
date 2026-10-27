## What changed

Filled `WeilConjectures.diagonalExchangeCube` in
`lean/Sheaf/Paper/DiagonalExchangeCube.lean`. All six public definitions/statements and the
original theorem signature are unchanged. All original public imports are retained.

Private proved helpers implement the two projection pullback squares, diagonal compatibility,
affine-local regularity (including the empty sequence at dimension zero), intrinsic fixed-module
constructible etale-origin witnesses, exceptional mate pasting, unit specialization, and section
cancellation. The categorical pasting calculation follows the proved private calculation in
`Sheaf.Paper.SectionExceptionalFibreCoherence`, using its existing public dependencies directly;
it does not import the section-family theorem or add a dependency on that later argument.

The proof works directly with `ULift (ZMod (ell^r))`, using the adopted source finite-coefficient
constructible-origin and smooth exceptional-base-change APIs. The six-step node proof and its
proof dependencies are updated to match this implementation. The blueprint unit's diagonal,
normal/deformation and orientation route is preserved; this item proves only its assigned cube.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.diagonalExchangeCube`
(`lem-sp-diagonal-exchange-cube`). No holes added or split off. No `sorry` remains in the item.
All added helpers are private and proved; there are no new modules or public declarations.
The complete module compiled through `lcompile.py` in 49.4 seconds. The sole line-width warning
was subsequently fixed. The geometry/witness, mate-pasting and section-cancellation calculations
were also checked independently during debugging. Delivery runs the final compile and preflight.

Edge cases: dimension zero uses the empty regular sequence on the open diagonal; positive
dimension uses properness of the kernel ideal at an actual source point. Empty sources make
these local assertions vacuous. Exponent invertibility is pulled back from the field and does
not assume nonempty schemes. All Cartesian constructions and pasting identities allow arbitrary
nonflat base change; identity base change is included without an extra hypothesis.

## No longer needed

Removed the following private proof imports and direct proof dependencies of this item:

- `Sheaf.Paper.PurityDiagonalBaseChangeCompared` (`lem-pur-diagonal-base-change`): both kappas
  were already expanded in the statement; section compositor coherence gives cancellation.
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`
  (`lem-pur-diagonal-regular-immersion`): use the proved source affine diagonal API and the
  dimension-zero etale case, which match the statement's affine-local predicate directly.
- `Sheaf.Paper.ExchangeFunctoriality` (`fix-lem-exchanges`): use the ordinary finite etale
  exchange-pasting theorem and Mathlib mate pasting, with the specified canonical maps.
- `Sheaf.Paper.PurityFiniteSettingComparisonHypotheses`
  (`lem-pur-finite-setting-comparison-hypotheses`): construct Noetherian/compactification and
  invertible-exponent instances directly in the given finite-type field setting.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem` (`thm-pur-cohomological-smoothness`): use the
  source smooth exceptional-base-change isomorphism at the same finite coefficient ring.
- `Sheaf.Paper.ProEtaleConstructibleOrigin` (`lem-sf-proetale-constructible-origin`): fixed
  lisse finite models, the source constructible-sheaf equivalence and bounded origin theorem
  give precisely the intrinsic fixed-module witnesses without changing coefficient models.
- `Sheaf.Paper.IntegralFinitePullbackComposition`
  (`lem-weil-pbc-proetale-derived-pullback-composition`): this is a finite-level equation;
  the already-public etale compositors and their unit/section coherence suffice.

For `thm-cbc-finite-level-proetale`, the proof uses its adopted source realization
`isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`, which accepts exactly the
constructed finite-coefficient etale-origin witnesses, together with the specified transport
identification. The node dependency is retained; its auxiliary coefficient-extension interface
is not imported directly.
The obsolete top-level tool approvals for the diagonal-regularity, finite-setting,
constructible-origin and integral-pullback dependencies were removed, preserving the order of
the remaining approvals. Statement dependencies were retained verbatim. These are local route
prunings only; no library module or upstream declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The argument is valid. Some planned interfaces use coefficient-extension rings or a different
constructibility presentation, whereas the assigned statement uses literal finite ZMod
coefficients and intrinsic fixed-module constructibility. The narrower existing source APIs
avoid those conversions. The planned positive-dimensional diagonal lemma also uses a stalkwise
predicate; the source affine regular-immersion theorem plus the etale dimension-zero case proves
the exact retained affine predicate. No statement or definition repair was needed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
