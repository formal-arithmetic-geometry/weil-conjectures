# RingHom.isNagataRing_of_weaklyEtale

## Reason

The completed finite-normalization proof uses pure tensor notation. It adds
`open scoped TensorProduct` inside `namespace RingHom`. The static interface check
requires a change record for this command. All added helper theorems are private
and proved. No existing definition, signature, visibility, instance, public import
or target statement changes.

## Old

```lean
namespace RingHom

theorem isNagataRing_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (f : A →+* B) (hf : @Algebra.WeaklyEtale A B _ _ f.toAlgebra)
    (hA : IsNagataRing A) : IsNagataRing B := by
  sorry
```

The source has no tensor-product scope command or private helpers between the
namespace command and the theorem's docstring.

## New

```lean
namespace RingHom

open scoped TensorProduct

-- Private proved helpers precede the unchanged public signature.
theorem isNagataRing_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (f : A →+* B) (hf : @Algebra.WeaklyEtale A B _ _ f.toAlgebra)
    (hA : IsNagataRing A) : IsNagataRing B
```

The theorem now has a complete proof. The scope command resolves notation in
this file; it introduces no new notation declaration or instance. The existing
public statement and all definitions it uses retain their meanings.

## Users

`tools/downstream.py Sheaf.RingTheory.NagataOfWeaklyEtale --uses
RingHom.isNagataRing_of_weaklyEtale` reports the following two textual users.
The only direct importer is the first row below. None needs an adaptation because the statement and public
imports are unchanged and the scope command is local to this module's elaboration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.LocallyNagataCatenaryOfWeaklyEtale | unclaimed | Existing application has the identical type; no change. |
| Sheaf.RingTheory.NagataOfWeaklyEtale | Q6 | Replaces its one hole with a proof; adds local tensor notation and private proved helpers. |

No consumer is adapted. No target requires a statement or definition review.

## Status

landed 20261020T132027-L-1403631 2026-10-20 (merge of deliver/Q6/Sheaf.RingTheory.NagataOfWeaklyEtale)
