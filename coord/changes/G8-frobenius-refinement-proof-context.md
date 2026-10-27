# FrobeniusSquareExchange proof context

## Reason

Prove recorded-refinement normalization by witness transport and categorical
naturality. Keep the retained object and antecedent explicit during this proof.
Disable the expensive unused-section-variable lint pass in the large module;
all elaboration, kernel and public interface checks remain enabled.

## Old

The declaration context began:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
```

`intrinsicCompactificationComparison_refinement` had its unchanged public
signature and a whole-theorem `sorry` body. No private coordinate-normalization
helpers existed.

## New

The declaration context begins:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option Elab.async true
```

Private proved helpers give conjugation naturality and equivalence triangle
cancellation. The private `coordinateOrigin` wrapper constructs the transported
origin from an explicit object, antecedent and witness; it chooses no data.
Its private normalization theorem proves the refinement formula for this object.
The original public theorem applies this normalization to the recorded witness.
Every existing public signature, definition body and import stays unchanged.

## Users

`tools/downstream.py Sheaf.Paper.FrobeniusSquareExchange --uses
intrinsicCompactificationComparison_refinement` reports the item itself as the
only textual user of the theorem. No consumer needs an adaptation. The new
helpers are private and occur only in this item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusSquareExchange | G8 | One proof completed; private helpers added. |

## Status

landed 20261025T204643-L-2991216 2026-10-25 (merge of deliver/G8/Sheaf.Paper.FrobeniusSquareExchange)
