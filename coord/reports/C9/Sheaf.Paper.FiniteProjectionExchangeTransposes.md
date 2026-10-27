## What changed

The statement of FiniteStatement and the signature of
AlgebraicGeometry.ProEtale.FiniteProjectionExchange.finite_projection_exchange_transposes
are unchanged. Its proof now computes both proper-route transposes from the published
projection counit equation, tensor naturality and mateEquiv_counit. The proper-first
calculation uses the canonical tensor-square equation. Injectivity of the adjunction
Hom equivalence gives equality of the proper routes. An explicit composite of mu,
tensor of beta with the identity, and gamma proves the open-source essential-image
claim; the target is directly an extension-by-zero object. Open assembly supplies
the diamond and restriction equations. The left refinement equation implies the
right refinement equation by rewriting each diamond. Identity normalization supplies
the last clause.

Four new modules isolate the still-unproved geometric normalization steps:
FiniteProjectionTensorSquare, FiniteProjectionOpenAssembly,
FiniteProjectionRefinementLeft and FiniteProjectionIdentityNormalization.
Each contains one public named theorem with its source, complete natural-language
argument, blueprint tag and node. The tensor square needs no cartesianness, the open
assembly needs no constructibility, and the identity law is independent of any
square or refinement. The refinement lemma states only the left word. Thus none is
the original statement with a renamed or repackaged hypothesis.

The original coordinate block is moved, with identical names, signatures and bodies,
to FiniteProjectionExchangeData and publicly re-exported. This is necessary to let
the new lemmas mention the coordinates without importing the theorem they prove.
No compile-time split, new choice of operation, upstream source edit or target edit
is involved. The original node records the actual Lean proof; the coordinate node
owns the moved declarations. The change record is
coord/changes/C9-finite-projection-exchange-coordinate-location.md.

## Proved and sorry left

Original module: one hole, named
AlgebraicGeometry.ProEtale.FiniteProjectionExchange.finite_projection_exchange_transposes,
is closed by a complete Lean proof from the four split statements. There are zero
remaining holes in the item module. Its private properFirst_transpose,
exchangeFirst_transpose, open_source_mem_essImage and diamond_equality are proved.

Added holes, all in namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange:

- tensor_square: lem-sf-finite-projection-tensor-square, module
  Sheaf.Paper.FiniteProjectionTensorSquare.
- open_factor_assembly: lem-sf-finite-projection-open-assembly, module
  Sheaf.Paper.FiniteProjectionOpenAssembly.
- refinement_left: lem-sf-finite-projection-refinement-left, module
  Sheaf.Paper.FiniteProjectionRefinementLeft.
- identity_normalization: lem-sf-finite-projection-identity-normalization, module
  Sheaf.Paper.FiniteProjectionIdentityNormalization.

FiniteProjectionExchangeData contains zero holes. This delivery is a decomposition,
not a proof of the target closure: one original hole closed and four holes added,
net minus three before any closure/baseline adjustments. Dependencies of the four
lemmas may themselves remain unproved. No axiom or hollow definition is added.

## No longer needed

Removed from the item's direct private imports:

- Sheaf.Paper.ExchangeFunctoriality
- Sheaf.SixFunctors.OpenTensorNormalization
- Sheaf.Paper.ProEtaleConstructibleOrigin
- Sheaf.Paper.PullbackTorAmplitude
- Sheaf.Paper.FiniteCoefficientTensorCtf
- Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.AlgebraicGeometry.PullbackBoundedConstructible
- Sheaf.Paper.CompactificationCoherence

These are not claimed to be globally pruned. Their relevant proof dependencies
are retained on the four split nodes, where the fixed-scalar comparison calculations
are still needed. In particular, the source-library declarations stay intact.
The original public prerequisites are preserved through the public coordinate import.
The original node's cross-unit tool approvals are removed there because their uses
now belong to the split nodes: ringed derived monoidal comparisons, the arbitrary-K
bounded-constructible pullback lemma, and the coefficient DVR result. The reviewer
may approve those tool uses on the new nodes; no new approval is asserted here.

No existing node or module is withdrawn. The original unit's route through finite
projection/exchange coherence remains; zero current direct Lean importers is not
used to infer that the item is unnecessary. All original mathematical dependencies
needed for the remaining geometric arguments are retained in their new nodes.

## Where the brief, the DAG or earlier work was wrong

The original proof plan correctly specifies the mathematical calculation. Its
ringed-derived monoidal comparison result is in a different presentation from the
published fixed-scalar maps used by this file; it does not directly prove the exact
fixed-scalar tensor-square equation by applying its Lean signature. The normalized
fixed-scalar identification is isolated in tensor_square. Similarly the open
normalization and finite refinement bridges are stated explicitly rather than
pretending their existing abstract signatures rewrite the specified maps directly.
No original statement is disputed or weakened. A read-only dependency walk also
encountered an existing unrelated cycle between
lem-pc-ring-hom-extension-differential and
lem-pc-ring-hom-extension-differential-adjacent in the inherited closure. No new or
changed node has a dependency path back to itself; this packet does not alter that
unrelated pre-existing cycle.

Small-case checks: tensor_square allows degenerate commutative squares and arbitrary
unbounded objects; identity comparisons make both words coincide. Open assembly is
an equation for canonical maps and uses no invertibility of proper projection or
exchange. Its extra hypothesis is only the proper subdiagram equality, which is
proved independently in the parent. Empty schemes and zero objects cause no witness
or nonemptiness assumption. The refinement lemma retains every finite-Tor and
constructibility hypothesis and every supplied origin witness of the original law;
no finite-Tor hypothesis on K or absolute separatedness is introduced. Identity
normalization is stated for any finite commutative coefficient ring and objects supported by
the coordinate definitions, with no accidental compactification-independence claim.

## New nodes

- def-sf-finite-projection-exchange-coordinates: unchanged explicit coordinate
  constructions moved out of the item to prevent import cycles. Zero holes.
- lem-sf-finite-projection-tensor-square: original plan step 1, canonical monoidality
  in the published fixed-scalar presentation; used in the proper-first transpose.
- lem-sf-finite-projection-open-assembly: original plan steps 2 and 5, the open
  restriction calculation and assembly with the independently proved proper equality.
- lem-sf-finite-projection-refinement-left: original plan steps 6 and 7, witnessed
  domains and intertwining for one word. The other word is proved from the diamond.
- lem-sf-finite-projection-identity-normalization: original plan step 8, the identity
  compactification calculation alone.

All new nodes are in sec-six-functors and retain the original unit assignment and
blueprint ancestry. Actual Mathlib search queries and results are recorded in the
nodes and the launcher search log. No other module is adapted. Change record:
coord/changes/C9-finite-projection-exchange-coordinate-location.md.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
