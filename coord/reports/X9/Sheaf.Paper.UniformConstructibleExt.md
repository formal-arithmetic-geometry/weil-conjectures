## What changed

In `Sheaf.Paper.UniformConstructibleExt`, proved
`AlgebraicGeometry.ProEtale.uniformConstructibleExt_exists`: the complete first clause of
`uniformConstructibleExt`, with precisely the standing hypotheses and no extra lattice
assumption. Proved `AlgebraicGeometry.ProEtale.uniformConstructibleExt_cutoff`: finiteness
and the natural-number representation of the displayed open-closed cutoff.

The proof uses the current `uniformConstructibleExtRational` declaration, including its
fixed source refinement. It proves covariant target-filtration induction and contravariant
source-filtration induction directly from Mathlib's Ext exact sequences. A finite maximum
of source bounds works simultaneously for all targets. Private proved helpers handle
zero objects, quotient isomorphisms, exact sequences, and finite filtrations. The argument
includes empty filtrations, zero objects, empty strata, and both allowed base fields.

The original theorem's signature and docstring are preserved. The required downstream
scan found 207 transitive importers; textual use of `uniformConstructibleExt` occurs only
in its own declaration. The four direct importers are `IndHeartIIVanishing`, `FiniteWindow`,
`ConstructibleCompactness`, and `FiniteWindowBounded`. Their sources were read; no existing
interface changes, and none needs an adaptation. Its unsupported explicit
cutoff clause is flagged for independent review. The node records the actual partial
proof and its unresolved step. No definition or existing theorem signature changes.

Validation: single-file remote compilation passes without warnings. All new proofs contain
no direct holes. The retained original theorem has its original whole-proof `sorry`.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. Split off: **0**. Net hole change: **0**.
This is a partial proof plus a statement dispute, not a complete proof or decomposition.

Proved from the existing declared dependencies:
- `AlgebraicGeometry.ProEtale.uniformConstructibleExt_exists` (entire existence clause).
- `AlgebraicGeometry.ProEtale.uniformConstructibleExt_cutoff` (explicit cutoff finiteness).

The sole remaining direct hole is
`AlgebraicGeometry.ProEtale.uniformConstructibleExt`, node
`sk-lem-uniform-constructible-ext`. Its statement is unchanged. Its second clause still
needs an argument giving the original cutoff without a global source-model lattice, or
a human correction of the unit's statement. No unproved theorem was added and no hole
was moved into another declaration or a definition.

## No longer needed

Removed direct proof imports:
- `Sheaf.Paper.FormalClosedSupport`, node `sk-lem-formal-closed-support`;
- `Sheaf.Paper.FormalClosedSupportII`, node `sk-lem-formal-closed-support-ii`;
- `Sheaf.Paper.UniformConstructibleExtIntegral`, node
  `det-uniform-constructible-ext-integral`;
- `Sheaf.Paper.UniformConstructibleExtTorsion`, node
  `det-uniform-constructible-ext-torsion`;
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, node `sk-def-sf-setting`;
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  node `sk-def-sfb-dc-setting`.

The rational theorem packages its own torsion, integral, and support arguments; the completed
proof needs only that declaration, the coefficient-heart filtration, the cohomological
dimension bounds and generic Mathlib Ext exactness. This removes redundant direct edges,
not a claim that all those modules leave the targets' transitive import closure. The
standing scheme/coefficient hypotheses remain explicit. No realized unit step is bypassed.

The interrupted sandbox's unsupported `finiteFiltrationExtBound` and
`uniformOpenClosedLisseExtNat` declarations were never in the shared library and are not
delivered. The former was false for an arbitrary nonmonotone property P; it has been replaced
by a direct maximum-and-filtration argument for the actual Ext-vanishing predicate.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the second clause and the original DAG step 2 ask for the original
unrefined cutoff for every lisse source. The current rational declaration instead has a
fixed finite source refinement and its maximum cutoff. Its final clause recovers the
original cutoff only if its chosen source model admits a lisse integral lattice globally.
That hypothesis is absent in this item. See the rational node's `split_report.source_error`
and `statement_change`, which already request the corresponding parent/unit correction.
Finiteness of the refined maximum does not identify it with the original displayed cutoff.

This is a precise proof/interface dispute, not a claimed formal counterexample to the
Ext conclusion itself. The invalid refined-cutoff inequality is not asserted in this
delivery. The original statement is not weakened, and no new unsupported statement is
introduced to conceal the gap. Please bring the unit-level correction already requested
by the rational node to the human. The first clause is now proved independently and can
be reused whichever decision is made about the explicit second clause.

The retained attempt also selected the essentially-smallness clause instead of the
filtration, used an arbitrary-property bound lemma lacking monotonicity, and attempted
to use subobjects of a module as schemes. These are repaired in the compiled proof.

Change record: `coord/changes/X9-uniform-constructible-ext-partial.md`.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
