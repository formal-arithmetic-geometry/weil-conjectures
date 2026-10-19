## Worker report

The module `Sheaf.CategoryTheory.SpacesKappaLimitFilteredColimit` states
`CategoryTheory.Spaces.spaces_kappa_limit_filtered_colimit`, with `sorry` as its
only theorem proof. No mathematical result is proved. Its three helpers belong
to this node's canonical comparison construction: `InterchangeColimit` records
a coherent colimit functor with its actual universal cocones; `interchangeRows`
is the transpose of the specified bifunctor; `IsInterchangeImageCone` fixes the
image of a cone, both its apex and its entire coherent transformation. There is
no new independent mathematical notion, new node, or dependency module.

The source was opened online: Lurie, *Higher Topos Theory*, March 10, 2012,
https://www.math.ias.edu/~lurie/papers/highertopoi.pdf, Proposition the project server,
printed pp. 391--392 (PDF pages 408--409, zero-based). Its forward implication
is precisely preservation of κ-small limits by the space-valued colimit
functor. The Lean formulation spells out both this cone-preservation statement
and the equivalence of its induced canonical comparison.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Smaller universe and containing universe | Explicit `universe u`; small spaces are Kan complexes in `Type u`; `Spaces.infinityCategory.{u}` is their coherent nerve in `SSet.{u + 1}`. Both shapes live in that containing universe. |
| Infinite regular cardinal in the smaller universe | `(κ : Cardinal.{u}) (_hκ : κ.IsRegular)`. Mathlib's `IsRegular` includes `aleph0 ≤ κ`, so infinitude is not omitted. |
| κ-small simplicial set K | `(K : SSet.{u + 1})` and `_hK : SSet.Presentability.IsKappaSmall κ K`, counting the sum of all nondegenerate simplices. There is no quasicategory assumption on K. |
| Small κ-filtered quasicategory I | `(I : SSet.{u + 1})`, `[SSet.Quasicategory I]`, `_hI : SSet.Presentability.IsSmall.{u, u + 1} I`, and `_hfiltered : SSet.Presentability.IsKappaFiltered κ I`. Smallness is relative to u, not merely to the containing universe. |
| Every coherent diagram X: K × I → S | `∀ (X : K ⊗ I ⟶ infinityCategory.{u})`; the cartesian tensor is the degreewise simplicial product. The braiding and `MonoidalClosed.curry` define `interchangeRows X : K ⟶ Fun(I,S)`, sending k to X(k,-), with all coherences. |
| The actual colimit operation and its legs | `InterchangeColimit I` includes a simplicial functor, a coherent unit, both endpoint equations in every degree, and colimitingness of the very cocone with that apex and unit component for every I-diagram. It does not take a bare map or an unconnected equivalence as colimit data. `Nonempty (InterchangeColimit I)` is a conclusion, not an extra hypothesis. |
| Source colim_i lim_k X(k,i) | `c` is any limiting cone over `interchangeRows X` in `Fun(I,S)`. Its apex is i ↦ lim_k X(k,i), by the pointwise-limit assertion in the node's proof. `L.functor.app _ c.1.1` is its I-colimit. Existence of such c is explicitly concluded. |
| Target lim_k colim_i X(k,i) | `interchangeRows X ≫ L.functor` is k ↦ colim_i X(k,i). The variable `t` is any limiting cone over this diagram. The theorem also produces a limiting `q`, so target-limit existence is explicit. |
| Canonical comparison, including all projection compatibilities | `IsInterchangeImageCone L X c q` fixes `q.1` to the pair consisting of the colimit of the source apex and the full original cone transformation postcomposed by L. An edge `e` in the cone category from q to t is precisely the induced comparison together with its coherent compatibility with all projections. The theorem supplies such an edge and treats every such edge. |
| The comparison is an equivalence | `IsEquivalenceEdge infinityCategory.{u} e.1.1`, where `e.1.1` is the edge on apices of this morphism of cones. It is the stated comparison, not an arbitrary equivalence between the two endpoints. `IsLimiting ... q` also states the equivalent cone-preservation formulation directly. |
| Empty K allowed | There is no `Nonempty K` or selected vertex. For empty K a limiting cone in `Fun(I,S)` is terminal, its image cone is terminal in S, and the comparison to any terminal cone is an equivalence. This is the filtered-colimit-of-terminal-spaces assertion. |

The choices `L`, `c`, and `t` are universally quantified universal-property
presentations of the operations in the displayed formula. They add no
assumptions: existence of L and c is explicitly asserted, and q supplies a
possible t. No object or map is defined by `Classical.choose` or `Nonempty.some`
from an unproved mere existence theorem. No fixed representative of a colimit
is substituted for the canonical operation. The universal cocone in L makes
its effect on the original cone legs exactly the original projection followed
by the colimit cocone leg, including its higher coherences. This is the
canonicality check in proof step 8. The complete eight-step proof plan is in
the theorem docstring.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `IsKappaSmall`, `IsKappaFiltered`. The local
  dependency record initially had no `lean`; `scompile.py --source
  Sheaf.CategoryTheory.PresentableInfinityCategory` showed the published source,
  and the shared DAG subsequently recorded the same interface (NU, 2026-10-17).
  Its full smallness and filteredness definitions were read; no repair was needed.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `diagramVertex`, `evaluation`,
  `constantDiagrams`, `coneCategory`, `coconeCategory`, `IsLimiting`,
  `IsColimiting`. The actual comma pullback definition and docstrings were read,
  including the directions of both endpoints. A cone edge's first coordinate
  is its map on apices.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.infinityCategory`, defined as the coherent nerve of all
  small Kan complexes, including the empty complex. Its full definition and
  enrichment were read. The ordinary homotopy category is not substituted.
- Mathlib's cartesian closed simplicial set structure supplies `⊗`, `β_`,
  `ihom`, and `MonoidalClosed.curry`; `Cardinal.IsRegular` is read from
  `Mathlib.SetTheory.Cardinal.Regular`.

All currently recorded proof-dependency modules are imported privately:
`Sheaf.CategoryTheory.SimplicialModelNerveLocalization`,
`Sheaf.CategoryTheory.CoherentNerveComparison`,
`Sheaf.AlgebraicTopology.FilteredColimitWeakHomotopyEquivalence`, and
`Sheaf.AlgebraicTopology.KanQuillenRightProper`. The other six proof dependencies
have no recorded module in the snapshot: `lem-coef-infinity-cofinal-kappa-poset`,
`lem-coef-infinity-yoneda-presheaf-limits`,
`lem-coef-simplicial-model-coherent-diagrams`,
`lem-coef-simplicial-presheaf-projective-model`,
`lem-coef-enriched-diagram-rectification`, and
`lem-coef-infinity-limits-products-pullbacks`. They are named in the proof
plan and do not supply notions needed to type the statement.

Edge cases checked mathematically before writing: K empty; K a point; arbitrary
finite simplicial shapes when κ = aleph0; discrete shapes with fewer than κ
vertices; non-discrete shapes (no replacement by ordinary categories); I a
point; empty I (excluded by the empty-test-shape clause of κ-filteredness);
κ = aleph0 without any countable-product condition; and X taking empty Kan
complex values. K and I can be small models represented in the containing
universe: `HasCardinalLT` and `Small.{u}` compare their sizes across universes,
so no literal level-size equality of their presentations is imposed.

Searches made (2026-10-17, msearch output also in `searches.jsonl`):

- `msearch.py ... leanfinder "Kappa small limits of spaces commute with kappa
  filtered infinity colimits"`: eight hits, including
  `CategoryTheory.Limits.colimitLimitToLimitColimit_isIso` and
  `filtered_colim_preservesFiniteLimits_of_types`. These concern ordinary
  category diagrams and Type-valued colimits, not coherent simplicial limits
  in spaces.
- `msearch.py ... loogle '"colimitLimitToLimitColimit"'`: ten ordinary-category
  comparison declarations, no exact match.
- `msearch.py ... grep 'colimitLimitToLimitColimit|IsKappaFiltered'
  CategoryTheory`: eleven hits in ordinary categorical limit/colimit files,
  no quasicategorical result.
- `msearch.py ... leansearch "Filtered infinity colimits of spaces preserve
  kappa small simplicial limits"`: eight hits, all ordinary-category
  finite-limit/filtered-colimit or accessibility results.
- Read Mathlib `CategoryTheory/Limits/ColimitLimit.lean:59` and
  `FilteredColimitCommutesFiniteLimit.lean:324`; their full contexts use
  ordinary categories and limits/colimits. The latter is finite-shape and
  Type-valued, so neither states this node.
- `rg -n 'IsKappaSmall|IsKappaFiltered|[Pp]resentable.*[Ii]nfinity|kappa.*limit|spaces_kappa'
  lean/Sheaf /home/ubuntu/weil-src-slopmaster2/WeilConjectures` found the landed
  presentability definitions but no statement of the item.
- `rg -n 'lem-coef-spaces-kappa-limit-filtered-colimit'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no match.
- `rg -n 'ColimitFunctor|colimitFunctor|mappedCone|ImageCone'
  lean/Sheaf/CategoryTheory /home/ubuntu/weil-src-slopmaster2/WeilConjectures`:
  only an unrelated ordinary site-system import, no reusable coherent
  colimit-presentation or image-cone interface.
- `tools/lean_names_upstream.py show` and an exact-name `rg` in
  `dag/lean_names_upstream.json`, Mathlib, upstream WeilConjectures, and
  `lean/Sheaf`: none of the four delivered declaration names exists.

No statement correction, dispute, or dependency fault remains. The node copy
changes only `lean`, with all four declarations recorded.

Validation: the prescribed `scompile.py Q78
lem-coef-spaces-kappa-limit-filtered-colimit <module>` passed both sandbox and
library-path compilations in 2.4 s and 2.2 s respectively, with no errors or
warnings. All universes and binders are explicit, and `autoImplicit` is false.
The first two compile attempts diagnosed namespace resolution for evaluation
and standard-simplex endpoints; the final file qualifies both dependency names.

## Second reading by Q78

I independently read the node, the delivered module, both statement-dependency
nodes and their actual Lean modules, and the spaces construction they use.
I opened the source itself: Lurie, *Higher Topos Theory*, March 10, 2012,
[Proposition the project server](https://www.math.ias.edu/~lurie/papers/highertopoi.pdf),
printed pp. 391--392 (PDF pages 408--409, zero-based). This node cites HTT,
not a Stacks tag. I also read the immediately preceding construction of the
colimit functor on p. 391: its coherent universal cocones explain the data
in `InterchangeColimit`. The forward implication has precisely the stated
filteredness and size hypotheses, with no additional geometric assumptions.

Here is my object/hypothesis/conclusion inventory and its correspondence.
Each row has verdict **matches**.

| Node item | Lean and verification |
| --- | --- |
| A smaller universe, small spaces, and a containing universe | `universe u`; `infinityCategory.{u} : SSet.{u + 1}` is literally `SimplicialNerve Kan.{u}`, with the internal-Hom enrichment of all small Kan complexes. This is the space infinity category, retaining mapping spaces. The ordinary localized homotopy category is not used. |
| Infinite regular cardinal in the smaller universe | `κ : Cardinal.{u}` and `_hκ : κ.IsRegular`. I opened Mathlib `Regular.lean`: the first field of `IsRegular` is `aleph0_le`. Thus infinitude is part of the hypothesis, including `κ = aleph0`. |
| A κ-small simplicial shape K | `K : SSet.{u + 1}` and `_hK : IsKappaSmall κ K`. The dependency definition is `HasCardinalLT (Σ n : ℕ, K.nonDegenerate n) κ`, exactly the node's size condition over all dimensions. No category, quasicategory or nonemptiness assumption is imposed on K. |
| A small κ-filtered quasicategory I | `I : SSet.{u + 1}`, `[SSet.Quasicategory I]`, `_hI : IsSmall.{u, u + 1} I` and `_hfiltered : IsKappaFiltered κ I`. I read `IsSmall` and `IsKappaFiltered` in the recorded module: the former measures smallness in u; the latter tests every κ-small simplicial diagram and demands a coherent cocone, including the empty diagram. |
| Every coherent X on K × I | `∀ ... (X : K ⊗ I ⟶ infinityCategory.{u})`. Mathlib's cartesian simplicial tensor is the degreewise product. `interchangeRows X` curries `(β_ I K).hom ≫ X`, hence sends k to the whole coherent row X(k,-). The braiding has the correct direction. |
| The actual I-colimit operation | `L : InterchangeColimit I` has its functor on `Fun(I,S)`, an entire coherent unit with source the identity and target the constant-diagram composite, and colimitingness of that very unit component with its specified apex. The source and target equations hold as simplicial maps, not only on vertices. `Nonempty (InterchangeColimit I)` is concluded, so no existence assumption is added. |
| The inner limits on the source side | `∃ c, IsLimiting (interchangeRows X) c`, followed by quantification over every such c. By pointwise limits in `Fun(I,S)`, c's apex is the coherent diagram i ↦ lim_k X(k,i). Its existence is stated, not hidden in a choice. |
| Source of the displayed comparison | In `IsInterchangeImageCone L X c q`, the first coordinate of q is `L.functor.app _ c.1.1`, exactly colim_i lim_k X(k,i). |
| Target of the displayed comparison | `interchangeRows X ≫ L.functor` is k ↦ colim_i X(k,i), and `t` satisfies `IsLimiting` for this diagram. Existence follows from the supplied limiting image cone q, so the universal quantifier over t is not vacuous. |
| Canonical comparison and all its projection compatibilities | The second coordinate of q is the entire cone transformation of c postcomposed with L, via `((ihom Δ[1]).map ((ihom K).map L.functor)).app _ c.1.2`. I read the dependency's actual comma-subcomplex and cone definitions: coordinate one is the apex and coordinate two is the coherent transformation. Thus this fixes all legs and higher coherences. An edge e in this same cone category, with `δ 1 e = q` and `δ 0 e = t`, is the induced comparison with these compatibilities. |
| The comparison is an equivalence | The theorem supplies such an e and requires `IsEquivalenceEdge infinityCategory.{u} e.1.1` for every such e. The first coordinate of a cone edge is precisely its edge on apices. Source is q, target is t. It also states `IsLimiting ... q`, the equivalent preservation-of-limit-cones formulation of HTT condition (2). |
| Every choice of universal presentations, in the same mathematical order | κ, K and I and their hypotheses precede the conclusion; L, X, limiting c, and limiting t are arbitrary presentations of the operations in the formula. Existence of L and c is separately asserted, and q supplies a target limit. These presentations add no hypothesis and do not replace the canonical comparison with an arbitrary equivalence between endpoints. |
| Empty K is included | There is no selected vertex or nonemptiness binder on K. Its limiting cone is a terminal object of `Fun(I,S)`; the theorem sends it to a terminal cone of S and makes the resulting comparison an equivalence. This is exactly the node's final clause. |

Edge cases checked independently: empty K, a point K, finite non-discrete
simplicial shapes when κ = aleph0, discrete shapes of cardinality less than κ,
a point I, and arbitrary empty-valued space diagrams. Empty I is correctly
excluded by filteredness, since the test K = empty requires a cocone vertex.
The empty Kan complex is retained by `Spaces.Kan`, so no nonempty-space
assumption has slipped in. There is no zero-object, scheme, degree-n or
characteristic input to this statement. Both shapes live with S in u+1,
while `Small.{u}` and the cross-universe cardinal bound measure their sizes
in u; there is no independent index universe making a size test vacuous,
and no equality between unrelated object/morphism universes. All universes
and variables are explicitly bound under `autoImplicit false`.

Independent searches used different formulations from the first reader:

- `msearch.py ... leanfinder "The colimit functor of a filtered quasicategory
  preserves small homotopy limits of spaces"`: eight hits, on ordinary
  simplicial-set colimits, finite presentability, and homotopy-category
  products/terminal objects; none states the coherent interchange theorem.
- `msearch.py ... loogle '"PreservesLimitsOfSize"'`: twelve hits for ordinary
  categorical preservation predicates and their instances, not the notion
  of limits in the quasicategory of spaces.
- `msearch.py ... leansearch "Homotopy filtered colimits commute with finite
  homotopy limits in Kan complexes"`: eight ordinary-category comparison
  results, including `colimitLimitIso` and `IsIPC.isIso`; no exact match.
- `rg` with `homotopy.*[Ll]imit`, `[Ll]imit.*homotopy`,
  `[Cc]olimit.*[Kk]appa`, and `[Ff]iltered.*[Kk]an` in the project's
  `lean/Sheaf/CategoryTheory`, upstream `WeilConjectures/CategoryTheory`,
  and Mathlib's `CategoryTheory` and `AlgebraicTopology`: only unrelated
  triangulated limits, ordinary categorical statements, and the existing
  space/simplicial infrastructure.
- Exact names `spaces_kappa_limit_filtered_colimit`, `InterchangeColimit`,
  `interchangeRows`, and `IsInterchangeImageCone` searched across upstream
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  none is already declared. Broader searches for `colimitFunctor`,
  `ColimitFunctor`, `ImageCone`, and `mappedCone` found no reusable coherent
  colimit-presentation or image-cone construction.
- I opened the actual nearby candidates: Mathlib
  `FilteredColimitCommutesFiniteLimit.lean:324` and upstream
  `WeilConjectures/Mathlib/CategoryTheory/Presentable/Limits.lean:46`.
  The former is Type-valued finite-limit interchange in ordinary categories;
  the latter is accessibility of an ordinary Type-valued limit functor.
  Neither covers quasicategorical indexing or homotopy limits of spaces.
  I also opened `SpaceUniversalColimits`, `InfinitySiftedColimitCalculus`,
  and the declarations of `EnhancedFunctorConeCalculus`; these give slice
  base change, cocone preservation, and mapping-space calculus, not this
  statement or its coherent colimit-functor presentation.

There are no new nodes or dependency-module repairs to review. The three
helpers are the presentation and the canonical comparison data of this
node itself. Their data are explicit: the structure specifies universal
cocones, the transpose is a real curry construction, and the image-cone
predicate is an equality of the full data. No data are obtained from a
sorry or from a merely existential unproved choice. There is one theorem,
whose complete proof is `sorry`; no mathematical result is proved. Each
helper has its source/blueprint docstring, and the theorem docstring follows
all eight node proof steps, including the empty product and the actual
projection/cocone-leg identification. All four currently recorded
proof-dependency modules are privately imported; the six unrecorded ones
listed in the worker report remain unrecorded in this reading's snapshot.
No released stage-2 repair note exists for this item.

Mismatches and changes: none in the Lean, the node's mathematical statement,
or the dependency interfaces. I retained the module and node copy unchanged
and added this second-reading record. There is no `statement_change`, so
no correction/citer audit is called for. The only changed node field relative
to the shared base is `lean`.

Validation rerun: `scompile.py Q78
lem-coef-spaces-kappa-limit-filtered-colimit
.../lean/Sheaf/CategoryTheory/SpacesKappaLimitFilteredColimit.lean` passed
both sandbox and library-path compilation in 1.9 s each, with no errors
or warnings. A direct text comparison confirms `lean.statement` is verbatim
the theorem signature, and every Lean line is at most 100 characters.
