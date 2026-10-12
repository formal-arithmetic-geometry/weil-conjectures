## What changed

Proved `isAnalyticallyUnramified_of_isNagataRing` in
`lean/Sheaf/RingTheory/IsAnalyticallyUnramifiedOfIsNagataRing.lean`, preserving its signature,
visibility, public imports and existing docstrings. Added four proved private helpers: the field
case, the normal induction step, descent through a finite injective extension, and application of
that descent to the explicit normalization `integralClosure A (FractionRing A)`.

The proof follows Stacks [0331](https://stacks.math.columbia.edu/tag/0331), with the product of
local completions supplied by the existing [07N9](https://stacks.math.columbia.edu/tag/07N9)
decomposition. It uses the principal clause (1) of
[031T](https://stacks.math.columbia.edu/tag/031T), avoiding the fractional-principal construction.
Natural-number induction uses a dimension upper bound rather than choosing an exact dimension.
The quotient dimension drop is Mathlib `ringKrullDim_succ_le_of_surjective`; completion descent
uses flatness and injectivity of the tensor inclusion. All four principal-criterion hypotheses
are established in Lean, including the exact mapped maximal ideal in the prime-quotient notion.

Added proof imports of `AdicCompletionRingEquiv`, `CompletionFiniteExtensionDecomposition`,
`NagataDomainN2`, and `NormalDomainPrincipalQuotientAssociatedHeight`, plus Mathlib
`AdicCompletion.AsTensorProduct` and `KrullDimension.NonZeroDivisors`. Updated the item's DAG
proof, proof dependencies and proof origin. No statements or definitions changed. The item is
not one of `sk-thm-p1.realized`'s statement or step nodes; that unit's route is retained.

## Proved and sorry left

Closed: `isAnalyticallyUnramified_of_isNagataRing`
(node `lem-weil-pbc-local-nagata-domain-analytically-unramified`): 1 of 1 local holes.
Added: zero holes. Remaining in the delivered module: none. All new private helpers are proved.

This is a proof from existing library declarations, including declarations whose dependencies
still contain `sorry`; it is not a claim that the target's entire import closure is sorry-free.
No new intermediate statement was split off, and no data definition was added.

The single-file compile passed without warnings. Import-removal checks also confirmed that the
remaining two explicit Mathlib proof imports are required.

## No longer needed

Removed original proof imports:

- `Sheaf.Algebra.ChangeIdealCompletion`: completion products are supplied by the existing finite
  decomposition theorem, rather than assembling cofinal filtrations in this module.
- `Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes`: the normal-case proof uses
  `Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span` directly. The fractional-principal
  quotient node `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass` is no longer needed
  on this proof route.
- `Sheaf.RingTheory.JapaneseDomain`: redundant direct import; the necessary N-1/N-2 definitions
  and `isN1_of_isN2` are exposed by the retained public `NagataRing` import.

During development, also removed unused trial imports `Mathlib.RingTheory.LocalRing.Quotient`,
`Mathlib.RingTheory.Localization.Integral`, `Mathlib.RingTheory.Flat.Localization`,
`Mathlib.RingTheory.Flat.Stability`, and `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` after
compilation. Their needed facts are already exposed by the retained imports.

The full `Sheaf.RingTheory.CompletionFiniteExtension` wrapper and its additional tensor-to-
completed-algebra equivalence are unnecessary: only `CompletionFiniteExtensionDecomposition`
is imported. No new node for finite-completion descent is needed.

The following original DAG dependencies are removed from the item's direct proof dependencies:

- `def-weil-pbc-nagata-ring`
- `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`
- `lem-weil-pbc-finite-algebra-local-radical`
- `lem-weil-pbc-completion-exact-finite-modules`
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`
- `lem-weil-pbc-product-of-localizations-at-maximal`
- `lem-weil-pbc-localization-at-prime-of-quotient`
- `lem-weil-pbc-noetherian-submodule-finite`
- `lem-weil-pbc-change-ideal-completion`
- `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass`

Some completion ingredients remain dependencies inside the reused decomposition theorem; this
list records direct pruning, not a claim that all these modules leave every target's closure.
In particular the Japanese definitions are still used, so their definition node is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable mathematical interface was found. The DAG's fractional-principal
route was longer than needed: its already stated principal-associated-height lemma suffices,
and minimality follows from height one and containment of the nonzero element.

The local source `.tex` was absent; Stacks Tags 0331, 07N9 and 031T were read on the official
Stacks site. The requested initial searches found no direct Mathlib theorem; LeanSearch for the
finite completion comparison returned Internal Server Error and is recorded as unavailable.

An attempted refinement through `CompletionAtQuasiFinitePrimeMap` could not compile because its
published `.olean` was absent. Its declaration was not restated. The delivery uses the available
completion decomposition instead and compiles against the published library.

## Second reading by Y3

1. **Visible declarations:** Compared the delivered module with the repository version. The target theorem signature and all existing declarations are unchanged byte for byte; only proof imports and proof bodies differ.
2. **Proof validity:** Compiled the module successfully with `lcompile.py`; it contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof is constructive apart from permitted classical choice and uses only the allowed imported declarations.
3. **Split statements:** No statements were split off and no new nodes were added. The target is proved directly, so there are no new statement-strength or edge-case concerns.
4. **Pruning and route:** Checked the proof against the DAG route and retained induction, normalization, finite-completion decomposition, and the principal-quotient criterion. Removed the unused completion/change-ideal, fractional-principal, Japanese wrapper, and trial imports; updated `proof_deps` to match the route actually used.
5. **DAG agreement:** The target node's proof description remains mathematically accurate, and its direct `proof_deps` now records the declarations used by the delivered proof. The unit route and `realized` records are untouched.

Changed only the target proof module, its proof-dependency metadata, and this report. No definitions or statements were changed.
