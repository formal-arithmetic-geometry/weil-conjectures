## What changed

Replaced the hole in `Sheaf.SixFunctors.RationalExceptionalIdentifications` by a complete
assembly proof. The statement of `rationalExceptional_identifications` and the definition
`exceptionalIdentificationOfIso` are unchanged. The proof imports
`Sheaf.SixFunctors.RationalDualFormulaScalarCounit` and Mathlib's adjunction uniqueness API.
No existing module besides the item is changed; no target or adopted source file changes.

The two comparison isomorphisms are constructed with `Adjunction.rightAdjointUniq` from
single-field normalized dual-formula adjunctions. The proved private lemma
`transported_scalar_counit` transports the system's actual scalar counit equation along
`rationalLeft`. The proved private lemma `rightAdjointUniq_scalar` applies injectivity of
the target adjunction's Hom bijection, then naturality and the two uniqueness counit
equations, to establish the requested comparison square. It does not assume that square.

`RationalDualFormulaAdjunction` defines the actual integral dual-pullback-dual composite
and a normalization predicate. The predicate requires an integral adjunction whose
identity formula component satisfies the existing trace/evaluation characterization,
and requires the rational counit to be its localization. It contains no unknown data or
unproved definition fields. `RationalDualFormulaScalarCounit` states the scalar-extension
counit equation for those normalized adjunctions, with the duality/pullback composite
written explicitly and no exceptional-comparison isomorphisms in its statement.

All three files compiled together in import order through `lcompile.py`: 9.5 s, 8.6 s,
and 13.7 s respectively, with no warnings or errors. The generic helper proofs also
compile. The two new obligations include empty schemes, zero/torsion objects, the ground
field, identity extensions and ramified extensions: no nonempty, positive-rank, unramified,
or nontorsion hypotheses were added. The contravariant scalar composite has exactly the
same order as the existing `dualScalar` definition.

## Proved and sorry left

This is a decomposition, not a complete geometric proof. One existing hole is closed
and two named holes are added (net textual hole change +1; zero holes in the item).

Closed by assembly:

- `WeilConjectures.RationalOperations.rationalExceptional_identifications`
  (`lem-sf-rational-exceptional-identifications`).

The only holes delivered are:

- `WeilConjectures.RationalOperations.rationalDualFormulaAdjunction_exists`
  (`lem-sf-rational-dual-formula-adjunction`): the trace-normalized adjunction over a
  single coefficient field, with its integral localization normalization. This supplies
  no finite-extension square and no comparison from a system right adjoint.
- `WeilConjectures.RationalOperations.rationalDualFormulaScalarCounit`
  (`lem-sf-rational-dual-formula-scalar-counit`): localization of the existing integral
  dual-formula scalar-transpose equation for two given normalized adjunctions. This
  supplies no adjunction or comparison-isomorphism existence result.

The private category-theoretic lemmas are fully proved. No axiom, unproved private helper,
or hole in a definition is introduced. Existing dependency holes remain with their owners.

## No longer needed

No existing import is removed and no whole module is claimed globally pruned. The item's
original public import of `RationalOperationsData` remains. Its proof now uses only the
two normalized subarguments and the existing coefficient-system counit equation. The
following old direct proof edges are removed from the item's `proof_deps`; many remain
needed transitively by the normalized subarguments, so these are not global withdrawals.
In particular the finite-scalar mate need not be reconstructed in the assembly: S already
supplies its invertible comparison and counit equation.

| Former direct node | Recorded module / Mathlib file |
| --- | --- |
| `def-pc-kflat-complex` | `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` |
| `def-pc-sheaf-restrict-scalars` | `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` |
| `def-weil-derived-complete-integral-detailed` | `Sheaf.Paper.SfIntegralConstructible` |
| `def-weil-derived-pullback-tensor-hom` | `Sheaf.Paper.DerivedPullbackTensorHom` |
| `def-weil-integral-rational-qbar-compact-support` | `Sheaf.Paper.QcqsCompactSupportRealization` |
| `def-weil-rationalization-karoubi` | `Sheaf.Paper.SfRationalizationKaroubi` |
| `lem-amb-mate-unit-counit` | `Mathlib/CategoryTheory/Adjunction/Mates.lean` |
| `lem-cbc-proetale-extension-zero` | `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero` |
| `lem-coef-dual-formula-scalar-transpose` | `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` |
| `lem-coef-finite-free-extension` | `Sheaf.Paper.FiniteFreeCoefficientExtension` |
| `lem-coef-finite-scalar-mate-realization` | `Sheaf.SixFunctors.FiniteScalarMateRealization` |
| `lem-coef-integral-finite-extension` | `Sheaf.SixFunctors.CoefIntegralFiniteExtension` |
| `lem-pc-kflat-resolution` | `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` |
| `lem-pc-pre-derived-adjoint-functors-general` | `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` |
| `lem-pur-integral-operations-scalar-extension` | `Sheaf.Paper.IntegralOperationsScalarComparisons` |
| `lem-pur-mate-unit-compatibility` | `Mathlib/CategoryTheory/Adjunction/Mates.lean` |
| `lem-sf-compact-support-restriction-of-scalars` | `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` |
| `lem-weil-compact-support-reduction-tower-functor` | `Sheaf.Paper.CompactSupportReductionTower` |
| `lem-weil-finite-free-completed-scalar-comparison` | `Sheaf.Paper.FiniteFreeCompletedScalarComparison` |
| `lem-weil-pbc-right-adjoint-preserves-limits` | `Mathlib/CategoryTheory/Adjunction/Limits.lean` |
| `lem-weil-pbc-ringed-strict-tower-homotopy-limit` | `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients` |
| `lem-weil-proetale-countable-products-exact` | `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` |
| `prop-coef-integral-exceptional-adjoint` | `WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint` |
| `prop-weil-pbc-rational-transport` | `Sheaf.Paper.PbcRationalTransport` |
| `thm-coef-rational-verdier` | `Sheaf.SixFunctors.RationalVerdier` |

## Where the brief, the DAG or earlier work was wrong

The current server queue at startup lists this as stage 3, one hole, `proof`, `route`.
The rework row and old build log concern a transitive bad import through
`RationalOperationsData` and the old `CoefficientChange` closure. I read both current
server records, confirmed that both source modules are present after restoration, and
preserved the item and its Lean attachment. There is no current assigned declaration-name
collision. The unchanged item compiled in 11.4 s before proof work; the delivered import
chain and new files compile together. No archive is withdrawn or deleted.

The original DAG gives the geometric argument but lacks a declaration connecting the
prescribed rational dual formula to a trace-normalized adjunction and a declaration
localizing the integral scalar-transpose equation in those coordinates. The recorded
integral exceptional-adjoint theorem is on the ordinary etale category with ambient
adjoint hypotheses; it cannot simply be applied as the unconditional pro-etale statement
used by this item. The first new obligation instead starts from the supplied S integral
adjunction, changes its finite-Tor category using `integral_residue_tor`, and uses the
existing canonical formula normalization. The second starts from the existing integral
scalar-transpose theorem. Both missing interfaces are stated explicitly with complete
proof plans. No false assertion or weakened target is used.

Mathlib searches found generic adjunction uniqueness, naturality and localization tools,
which are used for the assembly, but no theorem giving these geometric normalizations.
The unit's route is retained: integral exceptional adjunction, dual formula, finite scalar
transpose, and rational localization. No chapter or unit record is changed.

## New nodes

`lem-sf-rational-dual-formula-adjunction` is attached to
`Sheaf.SixFunctors.RationalDualFormulaAdjunction`. It is the single-field part of original
steps 10--11, including a precise integral trace/counit normalization. Its module also
records `integralDualFormula` and `DualFormulaAdjunctionNormalized`.

`lem-sf-rational-dual-formula-scalar-counit` is attached to
`Sheaf.SixFunctors.RationalDualFormulaScalarCounit`. It is the rational localization part
of original steps 19--20, for adjunctions already supplied and normalized. Its conclusion
is a counit equation on the dual formulas, rather than the item's square involving qF/qG.
The proof combining the two nodes constructs qF/qG and proves that square independently.

Both nodes carry recorded LeanSearch, LeanFinder, Loogle and Mathlib grep results, source
places and detailed natural-language proofs. The item's proof/proof_deps/proof_origin now
follow the actual assembly. No change record is needed: existing interfaces are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalDualFormulaAdjunction": "57ea8ea4f5eeb69ef85fc78d551527fc459dc25d", "Sheaf.SixFunctors.RationalDualFormulaScalarCounit": "d01de62cfa12860103b2a29f0307f6d1b9e1f463", "Sheaf.SixFunctors.RationalExceptionalIdentifications": "0ca8a052072442611d18f9edf7baef6a53d58f84"}, "results": {"Sheaf.SixFunctors.RationalOperations": {"hash": "4e2dd58b9d060b7498c0e0a39f8083bc1e768c81", "status": "OK"}}, "seconds": 103, "time": "2026-10-28T00:47:50+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
