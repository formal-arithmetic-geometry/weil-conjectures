## What changed

Proved both theorems of `Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions`,
without changing any declaration signature or definition. Retained the required proof-only import:
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`.
The open case uses the existing exact derived-adjunction unit theorem. The closed case
uses underived full faithfulness, preservation of K-injectives, and the proved generic
full-faithfulness theorem for total right derived functors. The ordinary-etale clause
is discharged by those existing instances. Updated the item's proof plan and dependencies.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.ProEtale.proEtaleOpenClosedAdjunctions`.
- `AlgebraicGeometry.Etale.ordinaryDerivedOpenClosedAdjunctions`.

Added 0 holes, split off 0 theorems. No `sorry` remains in the delivered module.
This is a proof from existing declarations, not a decomposition. Dependencies retain
whatever axioms they already had; this delivery does not assert they are all sorry-free.
The final proof compiled cleanly on the server in 2.2 seconds. Delivery preflight
checks the actual axiom dependencies again.

## No longer needed

The existing public imports are retained as the module's exported interface.
Removed the following unused private proof imports, added to the shared baseline during
this session:

- `Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.

A trial explicit proof import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful`
is unnecessary: it is already exposed by the required closed-immersion import.

The following planned dependencies are unnecessary as separate inputs to this proof;
they are not imported, and are removed from its `proof_deps`:

- `def-weil-open-closed-recollement`.
- `def-weil-pbc-proetale-operations`.
- `lem-exc-proetale-open-unit`.
- `lem-weil-extension-by-zero-adjunction`.
- `lem-weil-extension-by-zero-exact`.
- `lem-weil-pbc-adjunction-of-natural-bijection`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-localization-universal-property`.
- `lem-weil-pbc-termwise-adjunction-homotopy`.
- `prop-pur-kinjective-resolutions-exist`.
- `prop-weil-pbc-proetale-constant-exact`.

The termwise adjunction, localization, K-injective Hom comparison and resolution choices
are already encapsulated by the existing derived-adjunction and right-derived
full-faithfulness theorems. The intrinsic constant-ring-sheaf operation, extension-by-zero,
and open-unit modules concern a different encoding from this fixed-scalar statement and
are not needed here. The fixed-scalar open full-faithfulness declaration is recorded by
`lem-sfb-finite-extension-by-zero-fully-faithful`; the right-derived generic result is
recorded by `lem-exc-kinjective-derived-fully-faithful`. The obsolete top-level approvals
for `prop-weil-pbc-proetale-constant-exact` and
`lem-weil-pbc-termwise-adjunction-homotopy` are removed. The right-adjoint K-injective
preservation approval is retained. No module is withdrawn, and no whole-project pruning
claim is made: other consumers may still need all these modules.

## Where the brief, the DAG or earlier work was wrong

The long localization/Hom-transpose proof plan was unnecessary for these exact existing
canonical adjunctions. The generic derived-unit and right-derived full-faithfulness API
already supplies its needed conclusions. Several recorded dependencies now use intrinsic
ring-sheaf coefficients whereas this module deliberately states a fixed-scalar result;
the proof uses the existing fixed-scalar declarations, preserving every hypothesis,
universe and conclusion. Complementarity is not needed for either adjunction property,
but its original binder is retained. No source or mathematical statement was changed.
The unit record has no realized statement or steps bypassed by this local shortening.

The shared module was temporarily absent during initial reads and subsequently became
visible. A later compile request received no answer from the server and was retried;
this was infrastructure latency rather than a Lean timeout or proof failure.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
