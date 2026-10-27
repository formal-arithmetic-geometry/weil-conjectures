# Normalized compositor proofs

## Reason

Two existing holes are the universal normalized compositor and its tensor equation.
The ordinary comparison and representative descent APIs already supply the needed
ingredients.

## Old

The two declarations had `sorry` proofs. Repeated inference of the cochain tensor
structure and its totalizability proofs made the expanded arguments expensive.

## New

Unary comparison descent supplies the compositor.
Private category-theoretic lemmas paste representative tensor squares and cancel
computation isomorphisms. Fully faithful resolving restriction extends the resulting
equations to all derived objects. Generic private
restriction lemmas avoid repeated expansion of sheaf-category structures.
The generic square calculations take tensor objects and component maps directly.
Their site specialization uses the existing native cochain comparisons and tensor
model components, without rebuilding a separate tensor functor or comparison.
The original representative construction of the canonical comparison is retained.
Synchronous theorem elaboration is retained. The forgetful functor, sheaf
composition, and native category instances stay folded locally. These proof
controls introduce no mathematical choices.
Backward defeq hints are disabled locally; kernel and transparency checks remain enabled.
Functor whiskering is qualified to avoid the monoidal notation overload.
The tensor-map and compositor proofs share proved additive, zero-colimit,
totalizability and graded-tensor existence instances. Native category structures,
K-flatness and flatness predicates stay folded locally.
The complete pasting and restriction argument is generic in the six categories;
the site theorem specializes it to the prescribed native objects and maps.
The public declaration signatures, definition bodies and imports are unchanged.
The adjunction-conjugate compositor and its cochain lift stay folded locally.
No other module is changed and there are no forced adaptations.

## Users

| Module | Holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteDerivedComparisonNormalization | E1 | Proofs and private helpers only. |

## Status

landed 20261026T065454-L-3002576 2026-10-26 (merge of deliver/E1/Sheaf.Paper.FiniteDerivedComparisonNormalization)
