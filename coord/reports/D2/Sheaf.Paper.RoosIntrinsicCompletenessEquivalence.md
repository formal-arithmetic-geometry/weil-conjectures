## What changed

Replaced the proof of `WeilConjectures.roosIntrinsicCompletenessEquivalence` by an
assembly using the actual integral coefficient ring and quotient tower. All 20
existing declaration signatures and all existing definition bodies are unchanged.
No adopted source-library module is edited.

The assembly proves the signed-cone comparison, normalizes the specified completion
unit, constructs the strict Roos triangle from exact products, and compares rotated
triangles. In the reverse direction it transports the triangle along the specified
unit and supplies the identity K-flat resolution. Private normalization lemmas keep
the canonical and legacy quotient interfaces explicit.
`integralKoszulStep_square`, `integralKoszulUnit_compatible` and the private
`integralKoszulProductUnit_comp` now reuse the proved generic cone identities.

Added the concrete positive-power cone tower, a local criterion interface, the
normalized quotient augmentation, and its unit-preserving Roos comparison. The
quotient augmentation is proved from the existing regular-quotient cone augmentation
and `PrincipalKoszulStrictReplacement.completed_exact`. Its ordinary extension
functor equals the project's chosen reduction functor by the object and map
normalizations; its component formula proves both strict compatibility equations.

## Proved and sorry left

Closed the sole original hole,
`WeilConjectures.roosIntrinsicCompletenessEquivalence`, with a complete Lean assembly.
The delivery adds one retained hole:

- `WeilConjectures.IntegralPrincipalCone.localCriterion`, node
  `lem-pur-integral-principal-cone-local-criterion`.

This is a decomposition: one upper hole is replaced by one separate singleton
completion theorem. It is not a claim of an axiom-free proof of the target closure.
The retained theorem is strictly a subargument: it concerns arbitrary natural
scalars and their local completion criterion, and contains no quotient comparison,
signed-fiber comparison, or existential Roos completeness convention. Its source,
complete natural-language proof, and DAG node are supplied. Its zero-scalar,
invertible-scalar, zero-complex and empty-site cases have been checked in words.

The new declarations `WeilConjectures.integralPrincipalConeQuotientAugmentation`
and `WeilConjectures.integralPrincipalConeQuotientComparison` are proved, as are the
construction lemmas `CochainComplex.PrincipalCone.square`, `compatible` and
`productUnit_comp`. No private helper or definition contains `sorry`.

Validation: all four supporting modules compile together. The augmentation compiles
with no `sorry` in 10.7 seconds and the Roos comparison in 4.5 seconds. The full main
proof compiles without warnings in 35.6 seconds. All 20 existing signatures and all existing definition
bodies are unchanged. The unchanged direct consumer
`Sheaf.SixFunctors.OpenRoosUnitAdjunction` compiles in 13.3 seconds against the
new main module. The packet has zero holes in the main module and one hole
in the new local criterion; net change is zero, so this is a decomposition.

## No longer needed

Removed the unused public imports `Sheaf.Paper.IntrinsicCompletionCompleted` and
`Sheaf.Paper.KoszulReconstruction` from this item. Its only direct Lean consumer,
`Sheaf.SixFunctors.OpenRoosUnitAdjunction`, explicitly imports the general intrinsic
implementation and uses the unchanged integral declarations. No module is withdrawn;
no whole-library pruning is claimed.

The main proof does not use
`def-pur-completed-coefficient-presentation-transport`,
`prop-weil-pbc-koszul-reconstruction`,
`lem-weil-pbc-completed-koszul-quotient-comparison`,
`lem-weil-strict-roos-derivation`, or
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`. The direct scalar-cone quotient
augmentation and exact-products triangle replace those detours. Their existing
statements, statement dependencies and other consumers are retained.

`lem-weil-pbc-ringed-koszul-completion-reflector` is no longer applied directly by
the main proof; it remains needed by the retained local criterion's proof plan.
The quotient augmentation uses `completed_exact` from the existing principal strict
replacement; it does not separately apply `lem-pod-completed-integral-scalar-regular`.
That source dependency remains needed wherever the strict-replacement proof uses it.

## Where the brief, the DAG or earlier work was wrong

The planned general reflector and completed-coefficient comparisons do not directly
instantiate at the item's independent scheme and coefficient universes or at its
concrete scalar-cone models. The local criterion isolates the singleton reflector
argument on the actual site and slices. The quotient comparison is proved directly
through the existing independent-universe regular-quotient interface.

The intrinsic fiber uses the negative of the ordinary Roos endomorphism. The square
(1,-1), shifted by minus one, gives the required isomorphism and preserves the whole
zero-homotopy unit. An arbitrary TR3 comparison is used only to transfer local
vanishing; it is never identified with the canonical completion unit.

The first preflight found that LeanFinder and Loogle had incorrectly been counted
as separate search categories. Added actual LeanSearch queries and their results
to all four new nodes; the existing semantic/type searches and source grep remain.

The prior missing published-artifact failure no longer prevents compilation.
Subsequent busy-server replies were retried. Explicit equality casts between the
canonical and legacy towers, and generic lemmas for their product projections, avoid
unfolding large coefficient constructions during the final triangle transport.
A later delivery check hit the 60-second limit. Removed an unused private transition
normalization and sealed the representative/restriction isomorphism constructors
locally; their types supply all the proof uses. The three scalar-cone
compatibility proofs now apply the proved generic PrincipalCone lemmas directly,
avoiding repeated concrete cone and product expansions. Performance revalidation is
in progress.

## New nodes

- `def-pur-principal-cone-tower`: explicit power-cone tower and normalized unit.
- `lem-pur-integral-principal-cone-local-criterion`: the retained singleton local
  criterion, with independent site and coefficient universes.
- `lem-pur-integral-principal-cone-quotient-augmentation`: proved strict levelwise
  quasi-isomorphic augmentation to actual quotients.
- `lem-pur-integral-principal-cone-quotient-comparison`: proved passage to the Roos
  comparison, preserving the whole unit.

Change record: `coord/changes/roos-principal-cone-route.md`.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
