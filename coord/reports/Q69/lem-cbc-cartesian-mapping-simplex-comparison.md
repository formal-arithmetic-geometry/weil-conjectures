## Worker report

The module `Sheaf.CategoryTheory.CartesianMappingSimplexComparison` states the selected-edge
restriction of the marked mapping-simplex comparison.  It defines the fibre map
`SSet.Enhanced.cartesianMappingSimplexFiber`, the marked pullback objects
`restrictedMappingSimplex` and `restrictedCartesianFibration`, the induced pullback map
`restrictedMappingSimplexUnderlyingMap`, and the two canonical underlying maps for inclusions
of simplicial subsets.  The final declaration is
`SSet.Enhanced.cartesian_mapping_simplex_comparison`; its proof is `sorry` as required for
stage 2.

The Lean hypotheses render the node clause by clause as follows.  `n : ℕ` is the chosen
nonnegative dimension.  `p : Y ⟶ Δ[n]` and `[Quasicategory Y]`, together with `hp`, give the
inner-fibration and cartesian-lift clauses of a cartesian fibration over the standard simplex.
`A : SimplexChain n`, `q : mappingSimplex A ⟶ Y`, and `hq : q ≫ p = mappingSimplexProjection A`
state the chain, presentation map, and map over `Δ[n]`.  `hcart` says every mapping-simplex
edge whose fibre coordinate is degenerate is sent by `q` to a `p`-cartesian edge.  `hfib`
requires categorical equivalences on every vertex fibre through
`cartesianMappingSimplexFiber`.  `k : K ⟶ Δ[n]` and `hk` encode a simplicial subset degreewise
injectively; `E : Set (K _⦋1⦌)` and `hE` say that the selected edge set contains all degeneracies.
The existential `qKE` is a marking-preserving map from the degreewise pullback source to the
pullback target, its underlying map is exactly `restrictedMappingSimplexUnderlyingMap hq k E`,
and `SSet.Marked.weak qKE` is the weak equivalence in the marked model over a point.  The final
universal clause quantifies `K'`, its inclusion `ι` (with `hι` and `_hιmono`), and `E' ⊆ E`;
it supplies the smaller comparison map and marked inclusion maps whose underlying maps are the
canonical pullback maps and whose square commutes.

The dependency declarations used are:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, including `SSet.Enhanced.SimplexChain` and
  the simplicial-set primitives;
- `Sheaf.CategoryTheory.InfinityFibrations`, including
  `SSet.Enhanced.InnerFibration` and `SSet.Enhanced.IsCartesianEdge`;
- `Sheaf.AlgebraicTopology.JoyalModelStructure`, including the quasicategory and categorical
  equivalence interfaces;
- `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`, including
  `SSet.Enhanced.mappingSimplex`, `markedMappingSimplex`,
  `mappingSimplexProjection`, and `mappingSimplexFiberInclusion`;
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`, including `SSet.Marked`, `Marked.Hom`,
  and `SSet.Marked.weak`.

The proof-plan imports also recorded in the file are
`Sheaf.CategoryTheory.HomotopyEquivalenceWeak`, `Sheaf.CategoryTheory.InfinityMappingComposition`,
`Sheaf.CategoryTheory.PointwiseEquivalences`, `Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest`,
`Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`,
`Sheaf.CategoryTheory.MarkedRelativeCartesianModel`,
`Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`, and
`Sheaf.AlgebraicTopology.RealizationCylinder`.

I checked the edge cases `n = 0`, empty `K`, empty fibres of `A`, and degenerate edges.  The
pullback definitions retain their canonical degeneracies; `hE` covers the degenerate selected
edges, and the theorem introduces no nonemptiness assumption.  The `n = 0` case has only
constant base simplices, so the same fibre and marking terms apply.

Searches for an existing declaration were made before writing the module: `leanfinder` for
“Restriction of a mapping simplex quasi-equivalence to a simplicial subset with selected marked
cartesian edges” (no matching declaration), `loogle` for `SSet, Cartesian` and for quoted
`SSet, Fibration` (no matching declaration), `grep` in Mathlib for
`mappingSimplex|mapping.simplex|[Cc]artesian[Ff]ibration|[Mm]arked[Ss]et` (no matching
quasicategorical comparison), `rg` in `WeilConjectures/` for mapping-simplex and cartesian
comparison names (no match), and `rg` in `lean/Sheaf` for the full item id (no existing module).
The stage-1 node's recorded searches likewise found only unrelated simplicial-set and
model-category declarations.

No `STATEMENT-DISPUTED` flag or node fault was found.


## Second reading by Q69

I am the independent second reader, not the author of the worker report. I read the
node, all five statement-dependency nodes and their recorded source declarations,
and the delivered module together. There is no maintenance repair note, statement
correction, new node or dependency-module delivery. The natural-language statement
is correct and unchanged.

Source check: this node explicitly cites HTT rather than a Stacks tag. I opened
https://www.math.ias.edu/~lurie/papers/HTT.pdf, Section 3.2.2 (PDF pp. 196-198 and
204; printed pp. 179-181 and 187). The mapping-simplex formula uses arbitrary
simplicial sets, not necessarily quasicategories, in the chain. Notation the project server
marks exactly degenerate fibre coordinates. Definition the project server requires precisely
the over-base equation, preservation of these marked edges, and categorical
equivalences on vertex fibres. Proposition the project server(2) includes every base map,
including empty bases, and Proposition the project server supplies the relative marked
comparison. Selected markings are the node's expressly identified agent
formulation, not a quotation of that proposition. I checked its seven-step
argument: the interval tests, the full subcategories of marking-preserving
functors, and restriction of the inverse equivalence to their cores supply the
absolute marked conclusion without marking unselected transports.

Here is my object/hypothesis/conclusion inventory and its Lean match:

1. Nonnegative dimension and small ambient sets: `{n : ℕ}`, `{Y : SSet.{u}}`,
   `A : SimplexChain.{u} n`, and `{K : SSet.{u}}`. Verdict: exact; arbitrary `u`,
   no positivity, cardinality, nonemptiness or fibrancy condition on `A` or `K`.
2. Cartesian fibration over the standard simplex: `p : Y ⟶ Δ[n]`,
   `[Quasicategory Y]`, `hp : Marked.Over.relativeFibration false p`. Verdict:
   exact. I read both `Enhanced.cartesianFibration` in `InfinityFibrations` and
   `Marked.Over.relativeFibration` in `MarkedRelativeCartesianModel`. For `false`,
   the latter is the same inner-fibration plus prescribed-target cartesian-lift
   condition. The extra source vertex `b` in the former and in the original file
   is determined by the source of the base edge. This existing arbitrary-base
   interface avoids requiring a separately supplied quasicategory instance on
   the standard simplex. A cartesian fibration over a simplex has quasicategorical
   total space, so `[Quasicategory Y]` excludes no case of the node.
3. Contravariant chain: `SimplexChain n = (Fin (n + 1))ᵒᵖ ⥤ SSet` in the
   presentation dependency. Its dependent-pair mapping simplex has simplices
   `(α,a)` in the fibre at the last vertex and the prescribed transition after
   restriction. Verdict: same chain and same simplex, not an ordinary categorical
   fibration or a quasicategory-only special case. The worker report attributed
   `SimplexChain` to the wrong module: it is declared in
   `CartesianMappingSimplexPresentation`, not `EnhancedDiagramsCones`.
4. Presentation map over the simplex: `q : mappingSimplex A ⟶ Y` and
   `hq : q ≫ p = mappingSimplexProjection A`. Verdict: exact. The underlying
   simplicial set of `markedMappingSimplex A` is definitionally `mappingSimplex A`.
5. Preservation of the specified transport edges: `hcart : ∀ z ∈
   (markedMappingSimplex A).marking, IsCartesianEdge p (yonedaEquiv.symm
   (q.app _ z))`. Verdict: exact. The dependency's marking is exactly the range
   of the fibre degeneracy at `α(1)`; `IsCartesianEdge` is the final-outer-horn
   definition from `InfinityFibrations`. `InnerFibration` itself is Mathlib's
   `SSet.InnerFibration`, not an `SSet.Enhanced.InnerFibration` declaration as
   the original worker report suggested.
6. Every vertex-fibre comparison is a categorical equivalence: `hfib : ∀ i :
   Fin (n + 1), CoherentNerve.IsCategoricalEquivalence
   (cartesianMappingSimplexFiber A p q hq i)`. Verdict: exact. I read the
   categorical-equivalence definition in `CoherentNerveInfrastructure` (testing
   restriction on cores), and the comparisons with the Joyal model in
   `CoherentNerveComparison` and `JoyalFunctorEquivalenceTest`; this is the same
   categorical equivalence, not weak homotopy equivalence of the original sets.
   The fibre helper now calls the already recorded
   `mappingSimplexPresentationFiber` with a sharply marked target. A sharp
   target imposes no preservation hypothesis on `q`; the resulting map is the
   same canonical strict pullback map from `A_i` to `{i} × Y`. Reversing the
   displayed pullback factors only reverses the conventional order of a fibre.
7. Simplicial subset and selected edges: `k : K ⟶ Δ[n]` and degreewise
   injectivity `hk` encode `K ⊆ Δ[n]`, while `E : Set (K _⦋1⦌)` and
   `hE : ∀ x, K.σ 0 x ∈ E` encode exactly the permitted edge set. Verdict:
   exact; a mono presentation covers every subset, with no assumption that
   `K` itself is quasicategorical.
8. The two marked restrictions: `restrictedMappingSimplex A k E` has underlying
   `pullback k (mappingSimplexProjection A)` and marks edges with base coordinate
   in `E` and mapping-simplex coordinate marked. `restrictedCartesianFibration
   p k E` has underlying `pullback k p` and uses `Marked.cartesianNatural p`
   on the second coordinate. Verdict: exact under `hp` and `hE`. The explicit
   union with pullback degeneracies adds no edges: their base projections are
   degenerate and hence in `E`, their source fibre coordinates are degenerate,
   and degenerate target edges are cartesian for an inner fibration. The natural
   marking's explicit degeneracy alternative is likewise redundant here (HTT
   the project server; the relative-calculus dependency states its natural-marking assertion).
   These unions make the helper definitions valid even before hypotheses are
   supplied; they do not alter the theorem's selected markings.
9. Canonical marking-preserving comparison: the existential `qKE` is a morphism
   in the existing category `SSet.Marked`; its subtype property is preservation
   of marking. `qKE.val = restrictedMappingSimplexUnderlyingMap hq k E` fixes its
   underlying map to the pullback lift `(k,m) ↦ (k,q(m))`. Verdict: exact; no
   arbitrary comparison map, equivalence or choice replaces the canonical map.
10. Absolute marked weak equivalence: `SSet.Marked.weak qKE`. I opened `Marked`,
    `Marked.Hom`, `markedCategory`, `natural`, `mapSharpPre` and `weak` in
    `MarkedPointCartesianModel`. Verdict: exactly the point-model testing
    condition against every small naturally marked quasicategory, not the
    relative model over `K` or merely an unmarked equivalence.
11. Naturality for smaller subsets/markings: universal `K'`, `k'`, `ι`,
    `hι : ι ≫ k = k'`, degreewise injectivity `_hιmono`, `E'`, `_hE'`, and
    `_hsub : ∀ e ∈ E', ι.app _ e ∈ E` give exactly `K' ⊆ K`, `E' ⊆ E`.
    The existential `qK'E'`, `iM`, `iY` are marked morphisms; their three
    `.val` equations identify the canonical smaller comparison and both
    pullback inclusions, and the last equation is the restriction square.
    Verdict: exact. Equality on `.val` is equality of marked morphisms since
    `Marked.Hom` is a subtype with proof-irrelevant preservation data. The
    underlying inclusion maps are injective because they are pullbacks of `ι`.
    Weak equivalence of the smaller comparison follows by applying the same
    universally quantified assertion to `k'`; the canonical `.val` equation
    fixes the resulting marked morphism uniquely. No equality of induced
    markings is claimed when `E'` is strictly smaller.
12. Quantifier order: `p, hp, A, q, hq, hcart, hfib` precede arbitrary `K, k, hk,
    E, hE`; the canonical comparison precedes the universal restriction clause.
    Verdict: same order and same uniform naturality as the node; no compatibility
    data have been made hypotheses.

Edge cases: `n = 0` is admitted by the natural-number binder; `Fin (n+1)` then
has its sole vertex. The argument's degenerate interval test is the identity
transition of `A_0`. Empty `K` produces two empty pullbacks and the unique
comparison. Empty fibres are allowed in `SimplexChain` and in the fibre
hypothesis; no vertex is selected from them. `E` can be empty only when its
required degenerate edges are absent, in particular for empty `K`; for nonempty
`K` it can be precisely the degenerate edges. `K'` and its fibres may also be
empty. All simplicial sets use an arbitrary common small universe `u`, exactly
as the node and its dependencies; there is no independent smaller testing
universe or extra universe equality. Zero modules, schemes and characteristic
are not notions in this simplicial-set statement.

Independent H4 searches (2026-10-17), using different wording from the first
worker: `msearch.py ... leanfinder "Mapping simplex quasi-equivalence restricted
to a subcomplex with chosen Cartesian transport edges"` returned only generic
subcomplex/restriction declarations. `msearch.py ... leansearch "A
quasi-equivalence of a mapping simplex with a Cartesian fibration remains a
marked equivalence after selecting base edges"` returned generic model-category
and ordinary fibred-category results. A broad Loogle query with `pullback` was
not parsed (unknown identifier); I replaced it with the successful quoted query
`"SSet.Subcomplex.fromPreimage"`, which returned the generic unmarked preimage
map and its equations, not the selected-marking comparison. Local `rg` over
Mathlib/AlgebraicTopology and all of `WeilConjectures` for
`mapping.?simplex|marked.?simplicial|cartesian.?fibration|selected.*mark`
(case-insensitive) had no matches. Local `rg` in `lean/Sheaf` and `dag/nodes`
for mapping-simplex fibre, restriction, selected-marking and cartesian-fibration
terms found the existing presentation, fibration, natural-marking and slice
interfaces, but no existing statement of this restriction result. I opened
those exact declarations and reused them. The universal unmarked comparison
is an existing proof-dependency node with no recorded Lean module; it is not
silently replaced or restated and has no import to add yet.

Repairs made: (a) use the existing `Marked.Over.relativeFibration false` instead
of expanding the cartesian-fibration clause, (b) use the existing
`markedMappingSimplex` marking directly in `hcart`, (c) call the existing
`mappingSimplexPresentationFiber` for the fibre helper, (d) reuse the existing
`Marked.cartesianNatural` for target markings, (e) restore the full seven-step
node proof in the theorem docstring, including marking reflection, core
homotopies and all edge cases, (f) change the six imports used only by the proof
to ordinary imports and retain public imports for the two reused interfaces,
and (g) add the standard copyright header. The theorem's mathematical content
was already correct; these repairs remove repeated constructions and satisfy
H4/H8/H9. The node's `lean.statement` was synchronized verbatim with the final
signature. All seven declarations have source/blueprint docstrings, every
object/map has real constructed data, and the sole postponed proof is the
named main theorem with `sorry`. There are no file-local notations/instances,
private copies or unbound variables/universes.

Validation: the final module passed `scompile.py Q69
lem-cbc-cartesian-mapping-simplex-comparison <module>` in both sandbox and
library-path modes (1.6 s and 1.9 s), with no errors or warnings. No other
module or dependency record is changed. Delivery preflight follows below.
