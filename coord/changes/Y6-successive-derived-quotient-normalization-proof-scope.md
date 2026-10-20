# SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization

## Reason

The completed proof adds private helpers, local proof attributes, and private proof imports.
The static preflight flags the additional module commands as an interface change. Every
existing declaration signature, public definition body, and public import is preserved.
No public instance is added: the two proved restriction-exactness lemmas are registered
as instances only locally. Local irreducibility attributes prevent elaboration and linting
from repeatedly unfolding tensor and localization implementations. They do not persist
as public reducibility changes.

## Old

The existing theorem signature is:

```lean
theorem successive_derived_quotient_normalization :
    ∃ p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a,
      Nonempty (Normalization p)
```

Its proof was `by sorry`. The module did not have the private restriction-exactness
lemmas or the local proof attributes listed below.

## New

The theorem signature is identical:

```lean
theorem successive_derived_quotient_normalization :
    ∃ p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a,
      Nonempty (Normalization p)
```

The proof is complete, using canonical restriction comparisons and their left-adjoint
mates. All new helpers are private and proved. In particular:

```lean
attribute [local instance] restriction_limits restriction_colimits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] pure sectionTensor
attribute [local irreducible] changeOfRings changeOfRingsPresheaf
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] restrictionComparison rightComparison
attribute [local irreducible] Functor.mapHomotopyCategory Adjunction.mapHomotopyCategory
  Adjunction.leftAdjointCompIso DerivedCategory.Qh Functor.mapHomotopyCategoryCompIso
  NatTrans.mapHomotopyCategory Functor.mapDerivedCategoryFactorsh
```

The local instance attributes are applied only to proved propositions. Individual private
calculations use `backward.isDefEq.respectTransparency false` where explicit underlying
section calculations require it. Auxiliary sections introduce only proof variables;
no notation or open namespace is added to the public interface. Proof-only import changes
are enumerated in the delivery report. No global instance or new public declaration is
introduced, and no existing public attribute is changed.

## Users

`tools/downstream.py` reports 1,315 transitive importers. Its `--uses` check for the theorem
reports exactly the following two modules. The external use, at line 546 of the integral
residue module, obtains the same existential presentation and normalization as before.
It requires no adaptation. All other public declarations in this module are unchanged,
so consumers of those declarations also require no adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization | Y6 | proof completed; private helpers and local proof attributes |
| Sheaf.Paper.IntegralReductionResidueHomology | unclaimed in shared snapshot | existing use has identical type and meaning; no edit |

No downstream statement becomes weaker, stronger, or different. No definition used by
a target changes, so no target statement review is reopened. No module held by another
group is adapted in this delivery.

## Status

landed 20261020T211905-L-3515788 2026-10-20 (merge of deliver/Y6/Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization)
