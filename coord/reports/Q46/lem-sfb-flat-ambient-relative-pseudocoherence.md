## Worker report

Item: lem-sfb-flat-ambient-relative-pseudocoherence. The module
`Sheaf.AlgebraicGeometry.FlatAmbientRelativePseudoCoherence` states
`AlgebraicGeometry.Scheme.isPseudoCoherentRelativeTo_iff_flatAmbient_pushforward`.
Its sole proof is `sorry`; it introduces no definitions. Only the item's `lean`
field changes. No statement correction or disputed statement is needed.

The source was read in `literature/stacks-project/more-morphisms.tex`,
`lemma-check-relative-pseudo-coherence-on-charts` (Tag 09UU), whose clauses (1)
and (3) give the equivalence in each integer degree. Quantifying over degrees
gives the node's pseudo-coherence equivalence. The docstring preserves all four
steps of the accepted proof, including its use of closed-immersion invariance
for arbitrary derived objects rather than the quasi-coherent-only finite-map
criterion cited in the printed proof.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes X, P, S | `{X P S : Scheme.{u}}` |
| X → P → S | `(i : X ⟶ P) (g : P ⟶ S)`; the structure morphism of X is `i ≫ g` |
| i a closed immersion | `[IsClosedImmersion i]` |
| P → S flat | `[Flat g]` |
| P → S locally of finite presentation | `[LocallyOfFinitePresentation g]` |
| Every E in D(O_X) | `(E : schemeDerivedCategory X)` with no cohomology restriction |
| E pseudo-coherent relative to S | `IsPseudoCoherentRelativeTo (i ≫ g) E` |
| If and only if | `↔` |
| Ri_*E | `(schemeDerivedDirectImage i).obj E` |
| Absolute pseudo-coherence on P | `IsPseudoCoherent P ((schemeDerivedDirectImage i).obj E)` |
| No quasi-compactness, properness or Noetherian hypothesis | None occurs in the signature |

Local finite type of `g` follows by Mathlib's finite-presentation instance;
local finite type of `i` follows from closed immersion; their composite has its
composition instance. These are inferred, not additional hypotheses.
The universal `HasDerivedCategory.{w}` binder is the localization parameter
already required by the relative definition on its varying affine chart
schemes. The further binder over `P.Opens` supplies the existing absolute
definition's localized-site derived categories. They are size/encoding data,
not geometric assumptions. The same `w` is used throughout as in the dependency
interface; `u` and `w` are explicitly declared, and `autoImplicit` is false.

Recorded dependency declarations used, after reading their definitions and
docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with category
  morphisms `X ⟶ P` and `P ⟶ S`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`. The morphism-conventions node
  deliberately has no declaration and refers to these canonical classes.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` (available through the public imports).
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo`, defined by
  `∀ m : ℤ, IsMPseudoCoherentRelativeTo f m E`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`, the existing local bounded-above
  finite-free model predicate on the over-site.

Proof dependencies already stated are imported without `public`:
`Sheaf.AlgebraicGeometry.ClosedSupportRelativePseudoCoherence`
(`Scheme.isMPseudoCoherentRelativeTo_iff_closedImmersion_pushforward`),
`Sheaf.AlgebraicGeometry.MPseudoCoherentComplex` (`Scheme.IsMPseudoCoherent`),
`WeilConjectures.AlgebraicGeometry.DerivedPullback` (`derivedPullback`),
`WeilConjectures.AlgebraicGeometry.PerfectComplex` (`Scheme.IsStrictlyPerfect`,
`Scheme.IsPerfect`), and `Mathlib.AlgebraicGeometry.AffineSpace` (`AffineSpace`).
The other Mathlib proof dependencies are already public statement imports.
The proof nodes lem-sfb-flat-lfp-structure-relative-pseudocoherence,
lem-sfb-relative-pseudocoherence-composition and
lem-sfb-relative-pseudocoherence-all-affine-charts had no Lean module recorded
at inspection, so they have no import yet. They are not missing statement
interfaces and do not require adding modules in this delivery.

Edge cases checked before writing: empty X (both predicates concern the zero
pushforward), empty P (then X is empty), empty S (all schemes in the diagram
are empty), zero E, identity immersion, non-quasi-compact ambient schemes,
non-Noetherian bases, arbitrary unbounded E, and degree zero/all positive and
negative integers inside the relative predicate. The statement adds no finite
cover, global bound, quasi-coherent cohomology or finiteness of the defining
ideal of the closed immersion. The composition encoding covers every diagram
in the node without requiring a separately chosen structure morphism and an
extra commutativity hypothesis.

Searches, all on 2026-10-24:

- `msearch.py ... leanfinder`: query "A closed immersion into a flat locally
  finitely presented ambient scheme detects relative pseudo coherence by
  absolute pseudo coherence of derived pushforward"; eight hits on flatness,
  universally open morphisms and immersion properties, none stating the result.
- `msearch.py ... loogle`: query `"IsPseudoCoherentRelativeTo"`; zero hits.
- `msearch.py ... grep`: query `PseudoCoherent|pseudoCoherent|pseudo_coherent`;
  zero Mathlib hits.
- `msearch.py ... leansearch`: query "For a closed immersion into a flat locally
  finitely presented ambient scheme a complex is relatively pseudo coherent if
  and only if its derived pushforward is pseudo coherent"; eight hits on closed
  immersion properties and ordinary pushforward, none stating this result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `pseudoCoherent|PseudoCoherent|pseudo_coherent`, then the narrower
  `IsPseudoCoherentRelativeTo|isPseudoCoherentRelativeTo` and ambient-name
  patterns: existing absolute and relative predicates and the closed-support
  degreewise theorem were found; no duplicate ambient equivalence exists.
- `rg` for the item id in `lean/WeilConjectures`: no match. The upstream name
  inventory was searched as well, without an existing ambient declaration.

Validation: the prescribed `scompile.py Q46
lem-sfb-flat-ambient-relative-pseudocoherence <module>` completed successfully
for both its sandbox and library-name checks, with no errors or warnings.

## Second reading by Q46

I reopened the item and final module and checked the signature against every
row above after compilation. This is a worker self-check; no second agent was
started, as the dispatch brief explicitly prohibits it. The maintainer's
independent delivery review remains the independent reading.

The left side uses the composite to S, not the immersion to P. The right side
uses derived direct image along i, not along g or the composite. It uses the
recorded absolute `Scheme.IsPseudoCoherent`, not the relative predicate for the
identity or a new all-degree definition. All three geometric hypotheses have
their exact canonical classes; local finite type is inferred. E is an arbitrary
object of the unbounded derived category. Both directions are present, and no
additional geometric hypothesis or conclusion was found. The sole postponed
theorem has its matching DAG node and the full four-step proof docstring.
No mismatch requiring a source or statement change was found.
