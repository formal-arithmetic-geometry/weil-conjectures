## What changed

Replaced the hole in `Algebra.CotangentDifferentialSequence.sequence_nonempty` by the
canonical construction. Private proved helpers construct scalar-extended differential
maps, their generator formulas and isomorphisms, and the full-site coefficient functors.
The three projection identifications give natural transformations; polynomial differential
bases identify their values with inclusion and projection on finitely supported functions.
The objectwise kernel universal properties assemble to prove presheaf short exactness.
All public statements and definitions, including the complete `Sequence` record, retain
their signatures and bodies. Internal isomorphisms are irreducible after their formula
lemmas, to prevent repeated expansion of their constructions during elaboration.

The preflight-requested command change record is
`coord/changes/Z7-cotangent-differential-proof-commands.md`. It documents the
new scope, elaboration options and attributes on newly added private helpers.
The downstream consumer check finds zero Lean importers; no adaptations are needed.

The projection record is obtained from the existing lower-shriek theorem after obtaining
a bar system from `categoryColimitBarSystem_exists`. These dependencies retain their
existing postponed proofs; no data definition chooses an arbitrary existence witness.

## Proved and sorry left

Closed the one hole: `Algebra.CotangentDifferentialSequence.sequence_nonempty`
(node `lem-trf-cotangent-differential-presheaf-ses`). Added zero holes; zero `sorry`
remain in the delivered Lean file. No intermediate statement was split off.
This is a proof from the existing dependency declarations, not a claim that their
transitive axioms are already free of `sorryAx`.

Verification: the complete item compiles cleanly through `lcompile.py` in 48.4 seconds.
The public imports and the entire `Sequence` record are unchanged.

## No longer needed

Removed proof imports `WeilConjectures.CategoryTheory.Sites.PresheafFreeNerveExact`
and `Mathlib.Algebra.Homology.ExactSequence`. The node
`lem-sc-presheaf-free-nerve-exact-eval-glue` is unnecessary for this proof:
objectwise kernel lifts assemble directly in the ordinary functor category.
Its obsolete `tool_uses` entry is removed from this node. Its upstream declaration
and module are preserved.

The proof does not use `CotangentSheaf.exists_model` or its resolution-comparison
assertion: it constructs coefficients directly by the universal differential relations.
`CotangentSheafModel` remains a public import, as in the original interface.
No existing public import is removed. No module is withdrawn, and no unit route is
bypassed (the item's unit record has no realized statement or proof step for this node).

## Where the brief, the DAG or earlier work was wrong

The stated coefficient model uses a coordinate presentation category, whereas the item
uses the full presentation site. Its existence theorem cannot directly provide this
`SiteCoefficients`; the same universal construction gives it directly on the full site.
The DAG and theorem docstring now describe this construction and the direct kernel proof.
The existing bar-system existence theorem is explicitly recorded as a proof dependency
because the available lower-shriek interface takes a bar system as an argument.

Searches with LeanFinder, Loogle and ripgrep find the usual right-exact transitivity
sequence, not the entire natural polynomial-pair sequence with normalized base-change
and coordinate formulas. The proof reuses Mathlib's `tensorKaehlerEquiv`,
`mvPolynomialBasis`, and scalar extension of bases, exactly the algebraic ingredients
of Stacks `cotangent.tex`, lemma-triangle-ses (08QU), and `algebra.tex`,
lemma-differentials-base-change (00RV) and lemma-differentials-polynomial-ring (00RX).
Empty and infinite variable sets are included by `MvPolynomial` and `Finsupp`; the
zero ring and arbitrary coefficient maps are included without flatness hypotheses.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
