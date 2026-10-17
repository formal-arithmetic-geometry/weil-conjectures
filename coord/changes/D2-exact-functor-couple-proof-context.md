# CategoryTheory.BigradedExactCouple.exactFunctor_couple

## Reason

Complete the restored theorem's proof against the current upstream exact-couple
interface. The implementation adds private construction helpers and their
elaboration contexts. The static checker classifies new `variable` and `omit`
commands as an interface change, although they introduce no exported constant,
notation, attribute, instance or inference rule. The existing public theorem and
public import are unchanged.

## Old

The namespace has the following section variables and a theorem with whole-proof
`sorry`:

```lean
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {s : ℕ}
```

## New

The section variables above are retained. All helpers are private, all data is
constructed, and all proofs are complete. The additional elaboration-context
commands, verbatim (some `omit` forms occur more than once), are:

```lean
variable {Φ}

omit [Φ.Additive] in

omit [PreservesFiniteColimits Φ] in

omit [PreservesFiniteLimits Φ] in

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
```

The public `exactFunctor_couple` signature is byte-for-byte identical to the
restored library version; its proof now constructs all witnesses. Private
constructions occur only in private helpers and the public theorem proof.
No existing public definition or target statement changes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ExactFunctorCouple --uses
exactFunctor_couple` reports 207 downstream modules and no external textual use of
the theorem name. The only changed interface entry from the static checker is
its generic context-command marker, which names no declaration a consumer can
reference. The private additions and local binder annotations have no effect on
any importing module. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExactFunctorCouple | D2 | Complete proof; same public signature. |
| Sheaf.AlgebraicGeometry.HypercohomologyFiltrations | unclaimed | Imports the unchanged public interface; no adaptation. |
| Sheaf.CategoryTheory.ExactFunctorHalfPlane | unclaimed | Existing proved helper reused unchanged. |

All other downstream modules have the same absence of semantic or elaboration
changes. The maintainer's global build remains the independent consumer check.

## Status

landed 20261017T165545-L-3619435 2026-10-17 (merge of deliver/D2/Sheaf.CategoryTheory.ExactFunctorCouple)
