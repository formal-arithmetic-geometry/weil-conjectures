## Worker report

The module `Sheaf.AlgebraicGeometry.EtalePairwiseProductGraphNormalization` states
`AlgebraicGeometry.Etale.etalePairwiseProductGraphNormalization`. It constructs the literal
product presentation and the two displayed lambda isomorphisms, and states that the
specified graph comparison is lambda₁ followed by inverse lambda₂. Definitions have real
data. The only postponed proofs are `PairwiseProduct.b_projections`,
`PairwiseProduct.geometry`, and the main theorem; each has this node's blueprint marker
and its natural-language proof. These auxiliary theorem statements are the projection
identities and geometric clauses already contained in the assigned node.

Sources read: Stacks `more-etale.tex`, labels lemma-shriek-proper-and-open (0F7B),
lemma-shriek-proper-and-open-compose (0F7C),
lemma-shriek-proper-and-open-compose-horizontal (0F7D), and lemma-shriek-composition
(0F7J); the current blueprint's `sk-thm-sf-comp-composition.proof.md`, especially
Canonicity and associativity; and upstream `LowerShriekComposition.lean`, lines 193–268.
As the node explicitly says, this is the agent-stated extension of the graph formula,
not a claim that Stacks states this exact generality verbatim.

Hypotheses and clauses, matched to Lean:

- Finite commutative A is `(A : Type (u + 1)) [CommRing A] [Finite A]`. Schemes are
  `Scheme.{u}`, with explicit universe `u`. The coefficient and derived categories are
  the existing `ModuleCat.{u + 1} A` and `DerivedCategoryModule A T`; no bounded or
  constructible subcategory is substituted.
- An arbitrary scheme map is `{f : X ⟶ Y}`. A supplied open-then-proper factorization
  is `(c : Compactification f)`, used in the existing graph comparison. The two
  presentations are `(s t : EtaleGraphPresentation f)`, whose fields supply the proper
  first maps `a`, open middle maps `e`, proper structural maps `p`, and equations `fac`.
  Nothing requires f itself to be proper.
- The assigned comparison C is exactly `etaleGraphComparison A c s t`, defined in the
  recorded dependency as inverse B_(s,c) followed by B_(t,c). No endpoint isomorphism
  is chosen in this delivery.
- In namespace `EtaleGraphPresentation.PairwiseProduct`, `P s t` is literally
  `pullback s.p t.p`, and `U s t` is literally `pullback (s.e ≫ s.p) (t.e ≫ t.p)`.
  The maps `b`, `a`, and `p` are respectively `pullback.map` of the two open maps over
  the identity of Y, `pullback.lift s.a t.a` using the supplied factorization equalities,
  and first ambient projection followed by `s.p`. Its equality to the second expression
  is the existing `pullback.condition`; it is not made an additional hypothesis.
- `b_projections` states exactly the two projection equations for this product map,
  and is used only as proof data in the subsequent canonical pullback lifts.
- `O₁`, `O₂` are the literal pullbacks of the two ambient projections along `s.e`, `t.e`.
  Their first projections are the node's bν, their second projections are qν.
  Properness of qν follows from the existing proper pullback-projection instance;
  openness of bν follows from the existing open pullback-projection instance.
- `v₁`, `v₂` are the actual induced maps `pullback.lift b` with the two U projections,
  using `b_projections`. `z₁`, `z₂` are definitionally `a ≫ v₁` and `a ≫ v₂`.
  They are not unconstrained maps or existential choices.
- `Geometry` is the proof-only record of the node's geometric conclusions: `properA`,
  `openB`, `properP`, `openV₁`, `openV₂`, `properZ₁`, `properZ₂`, `fac`, `z₁_q`,
  `z₂_q`, `v₁_b`, `v₂_b`. The theorem `geometry` has all these conclusions without
  additional geometric hypotheses. `presentation` uses its proof fields and the
  already constructed U, P, a, b, p. No unknown mathematical data is extracted from it.
- The generic helper `etaleProductGraphLambda` writes the exact displayed lambda word.
  It first inserts the inverse `rightDerivedLowerStarCompOfEq z q s.a hz` in Ra,
  i.e. kappa_(q,z) in the node's notation. It applies
  `openImmersionLowerShriekLowerStarExchangeIso A Dsq`, whiskered by Rz and Rp,
  and composes the two proper direct images using the same canonical compositor.
  It then applies inverse `rightDerivedLowerStarCompOpenImmersionLowerShriekIso`
  for `t.a ≫ v = z`, and the inverse canonical
  `mapDerivedCategoryOpenImmersionLowerShriekComp` for v then j, transported along
  `v ≫ j = t.e`. Associators explicitly keep these natural isomorphisms composable.
- `lambda₁` and `lambda₂` instantiate this word with the first and second actual product
  projections and their neighborhoods. Their D squares are
  `(IsPullback.of_hasPullback ...).flip`. The E squares are the identity-top Cartesian
  squares constructed by the existing shrinking helper from `a ≫ v = z`; that helper
  is exactly Gamma_E followed by the canonical identity-open normalization. Inverting
  it supplies Gamma_E inverse with that normalization inserted. The cube dependency's
  Cartesian normalization identifies these existing exchange maps with its specified
  Gamma maps; there is no choice of an arbitrary comparison family here.
- The conclusion is an equality of natural isomorphisms:
  `etaleGraphComparison A c s t = lambda₁ s t A ≪≫ (lambda₂ s t A).symm`.
  Since Lean's functor composition reads in order of application, this is precisely
  C_(t₂,t₁) = lambda₂⁻¹ lambda₁, with source F_(t₁) and target F_(t₂).
- There is no quasi-compactness, Noetherianity, boundedness, constructibility, residue
  characteristic, or composition-of-two-scheme-maps hypothesis or conclusion.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the ordinary unbounded category.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek` and its
  `preservesFiniteLimits_openImmersionLowerShriek` exactness instance.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, proper
  pullback projections and composition; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` and its standard pullback/composition instances.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`, `snd`,
  `lift`, `map`, and the projection/condition equations.
- `Sheaf.AlgebraicGeometry.EtaleGraphComparisonBaseChange`:
  `EtaleGraphPresentation`, its `functor`, and `etaleGraphComparison` (through its
  explicitly specified `etaleGraphComparisonFromOpen`).
- `Sheaf.AlgebraicGeometry.EtaleProperOpenExchangeCube`:
  `ProperOpenDerivedComparisonFamily`, `etaleProperOpenExchangeCube`, particularly
  its Cartesian normalization and two pasting laws. The corresponding existing
  Cartesian constructors are `openImmersionLowerShriekLowerStarExchangeIso` and
  `rightDerivedLowerStarCompOpenImmersionLowerShriekIso` from
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, the normalized direct-image
  compositor characterization. For the concrete étale categories the already existing
  `rightDerivedLowerStarComp`, defined as conjugate of exact inverse-image composition,
  and `rightDerivedLowerStarCompOfEq` supply the canonical construction, as in the
  recorded graph-model dependency. No second compositor is defined.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `openImmersionLowerShriekComp` and `openImmersionLowerShriekComp_coherence`.
  The concrete derived compositor is the existing
  `mapDerivedCategoryOpenImmersionLowerShriekComp`.
- Proof import `Sheaf.SixFunctors.EtaleLocallyClosedGraphModel`: its explicitly constructed
  `locallyClosedGraphIso`, with the B₁/B₁₂/B₂ formula. The geometric proof dependencies
  are Mathlib's proper base change, composition, proper-to-separated and open base change,
  available through the recorded imports.

Edge cases checked before writing and in the final reading: empty X leaves all pullback
maps and graph lifts meaningful and proper; identical presentations use the diagonal,
not an assumption that the ambient product equals either factor; identity opens retain
canonical identity normalizations; non-quasi-compact opens are admitted by every
constructor used; arbitrary unbounded complexes are retained; the zero coefficient ring
is allowed. All morphisms in lambda have the correct direction. Literal products preserve
all source scheme universes; the coefficient universe is the recorded six-functor convention.

Searches actually run (msearch.py, with this group and item):

- LeanFinder: `Canonical pairwise graph comparison of proper open proper presentations
  equals comparison through their product presentation` — eight hits about ordinary
  categorical product comparisons and topological sheaf pairwise covers, no match.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsOpenImmersion` — zero hits.
- Mathlib grep: `etaleGraphComparison|pairwise.*[Pp]roduct|productGraph` — ten irrelevant
  arithmetic pairwise-product and topology/sheaf-cover hits, no matching theorem.
- LeanSearch: `Canonical product graph comparison for proper pushforward and extension
  by zero in the unbounded etale derived category` — eight ordinary product and
  pushforward-composition hits, no graph-normalization theorem.
- Direct rg of the read-only `lean/WeilConjectures` and `lean/Sheaf` trees for
  `pairwise.*[Pp]roduct|productGraph|etaleGraphComparison` found the recorded graph-comparison
  dependency and unrelated pairwise-product material, but no assigned statement.
  Direct grep of the node id in `lean/WeilConjectures` found no declaration.
  The existing product-graph model and all dependency interfaces were read in full.

No new independent notion, dependency repair, statement correction, or disputed statement
was needed. The original node is changed only in `lean`.

Validation: prescribed scompile.py passed both its sandbox compile and final module-name
compile with no errors or non-sorry warnings. A first attempt exposed one missing functor
associator in the final open-composition stage of lambda; the explicit associator and
right whiskering were added, and both compiles then passed.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
