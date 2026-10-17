# FiniteDiscreteCoefficientRestriction proof-local elaboration settings

## Reason

The complete proof of `finiteDiscreteCoefficientRestrictionForgetIso_linear` needs
private, local instances for monoidal sheafification and the sectionwise module encoding,
an open encoding namespace and local unfolding of
`finiteDiscreteCoefficientEquivalence`. The stage-3 static command comparison classifies
these commands as an interface change and requires this record. Every added instance is
explicitly `private local`; every added setting is confined to `section ProofHelpers`.
That section ends before the assigned public theorem and the final public definition.

No existing public signature or definition body changes. In particular both
`finiteDiscreteCoefficientRestrictionForgetIso` and
`finiteDiscreteCoefficientRestrictionIso` retain their original construction text.
The temporary semireducibility setting ends with the proof section, restoring the
original irreducibility. The new `import all Sheaf.Paper.FiniteDiscreteRestrictionEncoding` is proof-only;
it reuses that module's existing private isomorphism and action lemma without changing
the encoding module or exporting its private declarations. No target definition or
statement changes meaning, so no target statement review is reopened by this proof.

## Old

The existing file had these settings, which are retained verbatim:

```lean
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall
```

There was no `ProofHelpers` section, and the assigned theorem had proof `by sorry`.

## New

The following new commands occur in the private proof section (with private proved
helpers between the displayed excerpts):

```lean
section ProofHelpers

private local instance (T : AlgebraicGeometry.Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := AlgebraicGeometry.Scheme.ProEt.topology T)
    (A := Ab.{u + 1})

private local instance (T : AlgebraicGeometry.Scheme.{u}) :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint

private noncomputable local instance (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}

open CategoryTheory.ConstantInternalModuleSheafEncoding MonoidalCategory

private local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

attribute [local semireducible] finiteDiscreteCoefficientEquivalence

end ProofHelpers
```

The assigned theorem now has a complete proof from the existing sectionwise coefficient
identity. The public definitions are unchanged, and no private helper occurs in a public
signature or in an existing public definition body.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteDiscreteCoefficientRestriction` lists
these 21 downstream modules. Claims were read from the current local claim records.
All effects concern proof elaboration only; no forced adaptations are delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientExchangeFromComparisons | A4 | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Existing signatures and definitions unchanged; no adaptation. Compiled unchanged against the delivered proof. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Existing signatures and definitions unchanged; no adaptation. Compiled unchanged against the delivered proof. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing signatures and definitions unchanged; no adaptation. |

## Status

landed 20261017T031541-L-1622221 2026-10-17 (merge of deliver/B2/Sheaf.Paper.FiniteDiscreteCoefficientRestriction)
