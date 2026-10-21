# Sheaf.Paper.ECoefficientSmoothBaseChange private proof environment

## Reason

The conservative preflight scan requires a change record for the new proof-context
commands. They support the exact coefficient-presentation comparisons needed to apply
the existing adic theorem. No existing public declaration, definition body, public import,
attribute or visibility changes. Both original holes are closed without new holes.
No target changes meaning, and no target statement review is reopened.

## Old

The original elaboration options were:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```

The original theorem signatures, verbatim, were:

```lean
theorem sbcPrimeUnitOnSource {U V : Scheme.{u}} (q : U ⟶ V)
    (_hl : IsUnit (l : Γ(V, ⊤))) : ∀ t : U, IsUnit (l : U.presheaf.stalk t)

theorem eCoefficientSmoothBaseChange
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (K : PbcRationalConstructible l E T)
    (L : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K)
    (_hL : L.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl)) :
    IsIso ((sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (∀ L' : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K,
      L'.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) →
      sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L' =
        sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) ∧
    (L.IsSquareConstructiblyAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) sq →
      SbcConstructibleExchangeRepresentation l E sq _hT (sbcPrimeUnitOnSource l g _hl) L)
```

Both theorem proofs were `by sorry`. None of the new private helpers or private local
instances existed.

## New

Both original theorem signatures above are unchanged and their proofs are complete.
All six original definition bodies and all public imports are unchanged. The finite-level
site-comparison import required by the unit route is retained.

The following file-local options occur after all six existing public definitions,
so they only affect the new private proof helpers and the main theorem elaboration:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The unused-section-variable linter is disabled only for `sbcPrimeUnitOnSource`, using
`set_option linter.unusedSectionVars false in`, to retain its original prime instance.
No option is exported to importers. The five added instances are explicitly
`private local instance` declarations: `scalarRealization_equiv`,
`scalarRestriction_additive`, `scalarRealization_additive`, `finiteEncoding_equiv`,
and `finiteEncoding_additive`. Their complete proofs establish exact additive
coefficient equivalences for the private helpers; their instance registrations are
local to this file. All other new declarations are private and fully proved.
There is no global instance, notation, attribute, public helper, or new axiom.

## Users

`tools/downstream.py Sheaf.Paper.ECoefficientSmoothBaseChange --uses
sbcPrimeUnitOnSource eCoefficientSmoothBaseChange sbcRationalExchange
sbcTransportedExchange SbcConstructibleExchangeRepresentation` found exactly the two
consumers below. Inspection confirms they use the retained public interface, including
the unchanged unit-on-stalks lemma and rational exchange definitions. Neither requires
adaptation. The only Lean file delivered is the assigned item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ECoefficientSmoothBaseChange | M7 | Two theorem proofs completed; private proof context only. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | P7 | Identical public interface; no adaptation. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | Identical public interface; no adaptation. |

## Status

landed 20261021T134511-L-1244743 2026-10-21 (merge of deliver/M7/Sheaf.Paper.ECoefficientSmoothBaseChange)
