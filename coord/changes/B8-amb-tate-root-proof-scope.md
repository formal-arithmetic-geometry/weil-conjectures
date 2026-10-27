# Sheaf.Paper.AmbTateRootProjectionReduction private proof scope

## Reason

Preflight classifies the added top-level proof commands as a possible interface
change and requests this record. The delivery fills the existing theorem by the
DAG's four-step reduction. Its signature, all existing definitions and their
bodies, all existing attributes, and all public imports are preserved verbatim.
The added helper instances are explicitly local as well as private.

## Old

```lean
theorem ambTateRootProjectionReduction :
    Nonempty (AmbTateRootProjectionData l E n) := by
  sorry
```

There were no `ambCoeffAlgebra`, `ambLiftCoeffAlgebra`, or `ambBaseInvertible`
helpers and no added local irreducibility registrations for proof helpers.
The existing public command `attribute [irreducible] ambTateFiniteScalar`
and the original section variables and options are unchanged.

## New

The theorem has the identical signature and a complete proof. Its three new
helper instances are registered only within the current section:

```lean
private local instance ambCoeffAlgebra :
    Algebra ℤ_[l] (Padic.coefficientExtensionRing l E (n + 1)) :=
  ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
    (purTwistIntegersMap l E)).toAlgebra

private local instance ambLiftCoeffAlgebra :
    Algebra ℤ_[l] (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
  (ULift.ringEquiv.symm.toRingHom.comp
    (algebraMap ℤ_[l] (Padic.coefficientExtensionRing l E (n + 1)))).toAlgebra

private local instance ambBaseInvertible (T : AmbTateBase l) :
    ∀ x : T.val, Invertible (l : T.val.presheaf.stalk x) :=
  fun x ↦ (T.property x).invertible
```

The added proof-region commands are:

```lean
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSectionVars false
attribute [local irreducible] ambReassoc ambHiso ambDiso
attribute [local irreducible] ambFiniteIso
attribute [local irreducible] ambAlpha
attribute [local irreducible] ambK
attribute [local irreducible] ambB ambDelta
```

These control elaboration of the private helpers and theorem proof. The helpers
are fully constructed or proved, contain no `sorry`, and occur in no public
signature or public definition body. The new imports are private proof imports.
No exported instance registration is added, and no downstream adaptation is needed.

## Users

`tools/downstream.py Sheaf.Paper.AmbTateRootProjectionReduction --uses
ambTateRootProjectionReduction ambCoeffAlgebra ambLiftCoeffAlgebra ambBaseInvertible`
lists two downstream modules, no external textual use of the theorem, and no use
of any new helper. Their public statements keep the same meaning and type.
Holders are from the current claim records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AmbTateRootProjectionReduction | B8 | Existing hole filled; public API unchanged. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.SignedTwistSiteTransport | unclaimed | Public API unchanged; no adaptation. |

No target statement or definition changes, so this proof does not reopen target
statement review.

## Status

landed 20261023T230452-L-3430818 2026-10-23 (merge of deliver/B8/Sheaf.Paper.AmbTateRootProjectionReduction)
