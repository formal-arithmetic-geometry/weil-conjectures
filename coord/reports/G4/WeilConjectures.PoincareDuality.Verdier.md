## What changed

Repaired every gate objection in the return of head `3806a6461` against current main:

- Restored `isIso_verdierBiduality` with its exact upstream type and original hole.
- Restored `upperShriekDualizingComplexIso`, `absoluteVerdierExchange`, and
  `dualVerdierExchange`, including all original bodies and visibility.
- Restored the public `ShriekComposition` import and removed the replacement `UpperShriek`
  import. All upstream public imports are identical to current main.

Marked the unrestricted assertion `STATEMENT-DISPUTED` in a comment. Added and proved the
separate conditional variant
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_verdierBiduality_of_invertible_of_isDualizable`
in `Sheaf.PoincareDuality.RelativeBiduality`, as the return permits. It assumes explicitly that
`relativeDualizingComplex ℓ a` is invertible and that `K` is dualizable; it is proved directly
from `MonoidalClosed.isIso_toIhomIhom_of_isDualizable` and definitional equality of the two maps.
No existing signature, definition or theorem body is changed. No consumer needs adaptation.

The module and conditional variant both compile through `lcompile.py --all` (53.8 s and 27.1 s,
respectively, within the original 60-second per-file limit). The delivery dry run supplies the
final compilation, axiom and static checks. Change record:
`coord/changes/G4-verdier-relative-biduality.md`.

## Proved and sorry left

Original module: one hole. Holes closed: zero. Holes added: zero. Split-offs: zero.
Actual remaining hole count in the item: one, in
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_verdierBiduality`.
That assertion is retained verbatim and disputed, not proved from the conditional variant.
No node currently records the upstream unrestricted relative biduality assertion.

New fully proved declaration:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_verdierBiduality_of_invertible_of_isDualizable`
(node `lem-pod-relative-biduality-invertible`). Its module has zero holes and does not invoke the
upstream disputed theorem. The existing proof of `isIso_verdierExchange` remains unchanged.
This delivery repairs the returned interface and proves the permitted variant; it does not
claim closure progress on the false unrestricted statement.

## No longer needed

The new `Sheaf.PoincareDuality.RelativeBiduality` proof compiles without the explicit
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic` import; `IsDualizable` and its
instances are already exposed by the public `Verdier` imports. That proof uses the existing
categorical theorem rather than importing any geometric duality theorem about a different
coefficient category. The three absolute-exchange definitions and their public
`ShriekComposition` dependency remain available. No node, module, or unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly removed upstream statements and changed upstream public
imports; this repair restores them all and supersedes its second-reading claims.

STATEMENT-DISPUTED: `Ra^! 𝟙_S` need not be a dualizing object for a singular base. For the
origin of `Spec(k[x,y]/(xy))` over an algebraically closed field of positive characteristic
other than ℓ, the relative dualizing complex on the point has cohomology of ranks one and two
in degrees one and two. The double dual of the unit then has degree-zero rank five, whereas
the unit has rank one. The change record details the normalization triangle, purity on each
smooth normalization branch, and the finite-dimensional computation. This does not dispute
absolute Verdier biduality relative to the coefficient field.

The restored upstream theorem cannot follow from the conditional variant without the missing
hypotheses. Neither invertibility of the relative dualizing complex nor dualizability of every
constructible object is asserted here. The upstream theorem's hole is deliberately and
honestly left visible, as the verbatim-interface rule requires.

## New nodes

`lem-pod-relative-biduality-invertible` records the proved conditional variant, its complete
argument, source and searches. It specializes the existing categorical invertible-object
biduality theorem to the actual condensed bounded constructible category, and identifies the
canonical maps by definitional equality. It is not a split-off obligation and needs no
further proof. There are no new sorried statements. Change record:
`coord/changes/G4-verdier-relative-biduality.md`.

## Second reading by G4

1. **Signatures:** compared both delivered modules with the repository versions. Every existing
   declaration has the same signature and body; `Verdier.lean` gains only the explicit
   `STATEMENT-DISPUTED` comment. Verdict: pass.
2. **Proof validity:** compiled `Verdier.lean` and the new `RelativeBiduality.lean` with
   `lcompile.py --all`; there are no errors, forbidden declarations, or unlisted `sorry`s. The
   conditional theorem closes by the existing `MonoidalClosed.isIso_toIhomIhom_of_isDualizable`.
   Verdict: pass, with the original unrestricted hole honestly retained.
3. **New statement:** searched the repository and project sources for duplicates and checked the
   invertible-plus-dualizable hypotheses on edge cases. The conditional statement is true and
   exactly matches the needed categorical reduction; its node and documentation match.
   Verdict: pass.
4. **Pruning and route:** checked the proof against the categorical shortest route and removed the
   redundant `Rigid.Basic` import after compiling without it. The upstream exchange definitions,
   `ShriekComposition` import, and unit route remain intact. Verdict: pass.
5. **DAG agreement:** checked the new node's declaration, statement, source, proof, and module
   record against the Lean theorem. The node records the conditional theorem and no new `sorry`.
   Verdict: pass.

Changed during second reading: removed the redundant `Rigid.Basic` public import and updated this
report's pruning record. No declarations or statements were changed.
