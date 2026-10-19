## Worker report

The module `Sheaf.TraceFormula.ComparisonEqualizerClassKilling` defines the canonical helper `sliceCohomologyRestriction` and states the local
killing lemma for a positive cohomology class on a singleton coarse-topology cover.
It uses the canonical slice comparison and relocalization constructions from
`Sheaf.TraceFormula.ComparisonInductionStep`.

The Lean binders render the node's hypotheses as follows. `C`, `τ`, `τ'`,
`hτsite`, `hτ'site`, and `hτ` are the small category, two site structures, their
site axioms, and the refinement `τ' ≤ τ`. `P` is the class of morphisms. `A'` is
a predicate on abelian `τ'`-sheaves over each slice. `hzero`, `hiso`, `hkernel`,
`hcokernel`, and `hextension` give zero, isomorphism, kernel, cokernel and
short-exact extension closure (the weak Serre condition). `hbaseChange` states
stability of `P` under every existing pullback; `hrelocalization` is closure under
the canonical inverse-image functor of `relocalization`; `htauSheaf` says each
member already satisfies the `τ`-sheaf condition; and `hderivedImage` places every
ordinary right-derived direct image in `A'`.

For `f : X ⟶ Y`, `hf : P f`, and `hcover : Presieve.singleton f ∈ τ Y`, the
coefficient is `H : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat` with `hH : A' Y H`.
The degree and positivity clause are `(q : ℕ)` and `hq : 1 ≤ q`. The class is
`θ : Sheaf.H' H q (Over.mk f)`, i.e. cohomology of the object `X → Y` on the
slice site over `Y`. `heq` uses an arbitrary pullback object for `f` with itself;
the two maps are the cohomology-presheaf maps induced by `pullback.fst` and
`pullback.snd`, with the common object-over-`Y` proof supplied by
`pullback.condition`. This is exactly
`pr₁* θ = pr₂* θ`.

The conclusion gives an index type `I`, arrows `a i : Yj i ⟶ Y`, and a
`τ'`-covering presieve. For each index, a pullback of `f` along `a i` is chosen;
the displayed cohomology-presheaf map induced by the first projection sends
`θ` to zero. The common object is `Yj i ×_Y X → Y`, so this is precisely the
restriction to `Yj i ×_Y X` in the node.

Dependency declarations used: `CategoryTheory.Precoverage.IsSiteForCoverings`
from `Sheaf.CategoryTheory.SiteCoveringAxioms`; `CategoryTheory.GeometricMorphism`
and `CategoryTheory.RefinedTopologyComparison.relocalization` from
`Sheaf.TraceFormula.ComparisonInductionStep`; and Mathlib's
`CategoryTheory.presheafToSheaf`/the cohomology presheaf `Sheaf.cohomologyPresheaf`.
The size convention node is metatheoretic and has no declaration.

Edge cases checked: `q = 1` is allowed by `hq`; empty indexing types are allowed
by the existential cover (as for any valid empty covering); zero coefficients and
zero classes are allowed; and no nonemptiness or characteristic assumption is
introduced. Pullback universes use the same `Type u` as `C`, as required for
slice objects.

Searches made: `msearch.py ... leanfinder` for local equalizer cohomology killing
(no exact match); `msearch.py ... loogle` for sheaf/equalizer declarations (only
generic equalizer and Mayer–Vietoris results); `msearch.py ... grep` for
`equalizer.*class|makeClassZero|class.*zero` (no match); `rg` through
`WeilConjectures/` and `lean/Sheaf` for the target notion (no existing declaration).
Thus this is a new statement module.

## Second reading by Q94

Read the node and module independently. Every site, weak-Serre, base-change,
relocalization, sheaf-condition, derived-image, singleton-cover, positivity,
equalizer, and local-vanishing clause is represented by a corresponding Lean
binder or conclusion. The two equalizer maps use the two canonical pullback
projections and the conclusion uses the first projection to the original `X`;
no hypotheses or cases are added or omitted.

## Maintainer review fix (NT-stage2 cc reviewer, 2026-10-18)

When this delivery was committed (52fb9a8c, base ebb061d0), the item had already been
stated and landed on newtargets-dag by group Q114 (batch d3e3c858, reviewed by
NT-stage2-cc-8a34759ee, docstring fix). This delivery would have replaced that reviewed module by
an equivalent statement whose docstring only paraphrases the proof (H8) and whose helper
`sliceCohomologyRestriction` has no source place (H8); the report's search claim that no
declaration exists was stale (H4). The fix keeps the landed module
`lean/Sheaf/TraceFormula/ComparisonEqualizerClassKilling.lean` verbatim (same declaration
`CategoryTheory.RefinedTopologyComparison.comparisonEqualizerClassKilling`, eight-step proof
docstring, explicit `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` import). Both
renderings say the same as the node and Stacks Tag 0EZD; per-file compile of the kept module is
clean (nt_compile).
