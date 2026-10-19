## Worker report

The module `Sheaf.CategoryTheory.OrdinaryNerveDiscreteHomComparison` states the
ordinary-nerve counit comparison. The node's natural-language statement, dependency
lists and proof are unchanged. All definitions have explicit data and all named
theorems have exactly `by sorry` proofs. No dependency module or new node is needed:
the additional declarations are the canonical augmentation, strict Hom pairing and
well-definedness lemmas belonging to this comparison itself, as authorized in the
brief's missing-helper rule. Every declaration is listed in `lean.declarations`.

Hypothesis and clause correspondence:

- A V-small ordinary category is `(C : Type u) [SmallCategory C]`. Both its object
  and Hom sets lie in u; spaces of u-small Kan complexes lie in `SSet.{u+1}`. There
  is no nonemptiness, finite, connectedness, groupoid or skeletal hypothesis.
- `ordinaryDiscreteCategory C` is C with constant simplicial Hom sets. Its identity
  and composition are `ordinaryDiscreteId` and `ordinaryDiscreteComp`, evaluated
  degreewise as ordinary identity and composition. The abbreviation
  `ordinaryDiscrete` reuses Mathlib's constant functor.
- B is exactly `SSet.Pinched.rigidification.obj (nerve C)`. The canonical ordinary
  objects are its `SSet.Pinched.vertex` applied to `ComposableArrows.mk₀`.
- `ordinaryStringMap` sends every simplex in the subset-path nerve to `s.map` of
  the endpoint inequality, regardless of the intervening subset. This includes
  repeated vertices. `ordinaryString` is this enriched simplex. Its naturality
  assembles `ordinaryAugmentationAdjoint`; `ordinaryAugmentation` is its image
  under the existing left-Kan-extension/restricted-Yoneda adjunction, rather than
  a chosen map from an existence theorem. Thus the node's augmentation formula
  is real data, not an additional arbitrary hypothesis.
- `ordinaryAugmentation_vertex` states that this augmentation fixes ordinary
  objects. `ordinaryAugmentationHom` transports its enriched Hom map by exactly
  these endpoint equalities.
- The target identification is `ordinaryDiscreteSingularIso`: its inverse is the
  canonical characteristic-simplex unit. Its named `IsIso` theorem justifies
  this uniquely determined inverse. `ordinaryHomComparison` is precisely
  `singularRealization.map (ordinaryAugmentationHom C c x)` followed by that
  identification. The theorem's first conjunct asserts the recorded
  `SSet.Enhanced.IsWeakHomotopyEquivalence` for all c,x.
- Naturality for precomposition and postcomposition by B is expressed by the
  enriched composition equation, with `ordinaryTopComp` using the dependency's
  actual `topEnrichment`. It holds for arbitrary enriched simplicial parameters,
  in every degree; applying it twice gives the three-factor action in the node.
- The unit conjunct `ordinaryTopId C c ≫ ordinaryHomComparison C c c =
  ordinaryDiscreteId C c` compares the actual enriched units as simplicial maps.
  It carries the singular identity vertex and its degeneracies/unit homotopy to
  the ordinary identity and its degenerate unit homotopy.
- Naturality in ordinary C is the fourth conjunct: for every ordinary functor F,
  Sing realization of `ordinaryRigidMap F` intertwines the two canonical Hom
  comparisons and the constant simplicial map induced by `F.map`. The rigid
  map is the existing `SSet.Pinched.mappingMap`, with canonical vertex transport.
- The concrete pairing H_C is reused verbatim as `yonedaPairing (nerve C)`.
  `ordinaryHomPairing C` is the strict discrete Hom pairing constructed on each
  pair of ordinary strings, with reflected first-variable paths and ordinary
  second-variable paths acting by precomposition and postcomposition. Its
  constant target values are `ordinaryHomValue`, including empty Hom sets.
- The fifth conjunct quantifies an actual edge e of the internal functor
  simplicial set with the specified endpoints and asserts
  `SSet.Enhanced.IsEquivalenceEdge` of that same edge. It additionally requires
  its component at every ordinary pair (c,x), read through the coherent interval's
  unique endpoint path, to be exactly `diagramVertex (ordinaryHomComparison C c x)`.
  `HEq` here transports the source/target Kan objects determined by the endpoint
  equations. It is equality of the actual component maps, not just existence of
  an unrelated coherent equivalence or pointwise equivalences.
- The sixth conjunct restricts the equivalence along every `r : J ⟶
  ordinaryHomIndex C`; this includes restriction of either variable and fixing
  either variable, hence both representable and corepresentable families.
- The last conjunct is the same coherent natural equivalence after the canonical
  degreewise universe lift to `max (u+1) v`, for every v, including the identity
  lift. This is the containing-universe interpretation of the same Kan complexes,
  maps and inverse triangles. No equality of the small-space and ambient universes
  is imposed.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`,
  `IsWeakHomotopyEquivalence`, `diagramVertex`, `evaluation`,
  `AreNaturallyEquivalent`; its ordinary nerve and product/internal-Hom primitives
  are Mathlib's. The full source/signatures and their conventions were read.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `Kan`, `infinityCategory`,
  `singularRealization`, `topEnrichment` and the actual enriched composition and
  unit. Its full source was read, including the singular Kan and finite-product
  laws used by the proof plan.
- `Sheaf.CategoryTheory.InfinityPresheafYoneda`: `YonedaSimplex`,
  `yonedaPairing`, its reflected-subset construction, and `yonedaRigidSimplex`.
  The full source/signatures and docstrings were read; there is no replacement
  definition of H_C.
- The existing rigidification is
  `Sheaf.CategoryTheory.PinchedRigidificationResolution`:
  `SSet.Pinched.coherentSimplex`, `rigidification`, `coherentSimplexInclusion`,
  `vertex`, `mappingMap`, `pinched_rigidification_resolution`. Its full source
  and colimit/adjunction implementation were read.
- Proof-only imports retain the recorded proof route:
  `Sheaf.CategoryTheory.KanMappingHomotopyInvariance`,
  `Sheaf.AlgebraicTopology.RealizationSingularUnitWeak`,
  `Sheaf.AlgebraicTopology.RealizationWeakEquivalence`,
  `Sheaf.CategoryTheory.PointwiseEquivalences`, and
  `Sheaf.CategoryTheory.KanCoherentNerveQuasicategory`. Their recorded theorem
  signatures, hypotheses and full proof docstrings were read.

Edge cases: empty C makes all object-indexed clauses vacuous and gives the unique
transformation on the empty pairing index. Empty Hom gives constant empty targets;
its realization and singular complex are empty. The discrete Kan proof uses only
positive-dimensional horns, so does not assume a point. The same-object case
retains the actual identity/unit equation. Parallel arrows and noninvertible arrows
remain distinct constant labels; no contractibility or groupoid assumption is used.
All ordinal maps include degeneracies/repeated vertices. Arbitrary ambient universe
lifts include v=0 and larger v. No `let` occurs in a theorem signature.

Searches made (in addition to reading the existing node's search records):

- `msearch.py leanfinder`: "Rigidification counit of ordinary category nerve mapping
  simplicial sets weakly equivalent to discrete Hom bifunctor". Eight hits concern
  ordinary nerve/homotopy-category adjunctions, chiefly
  `CategoryTheory.nerveAdjunction.isIso_counit`, `nerveFunctorCompHoFunctorIso` and
  `SSet.OneTruncation₂.ofNerve₂`; none supplies the enriched counit or concrete
  two-variable comparison.
- `msearch.py loogle`: `CategoryTheory.nerve.homEquiv`. Ten hits identify ordinary
  nerve edges with arrows and functoriality. Read the declaration in
  `Mathlib.AlgebraicTopology.SimplicialSet.Nerve`: its type is about `SSet.Edge`,
  not the rigidification Hom complexes. Thus it is not this statement.
- `msearch.py grep`: `rigidification|discreteEnrichment|ordinaryNerve` in
  `AlgebraicTopology`: zero hits.
- Direct `rg` of the project source, Mathlib and `lean/Sheaf` for augmentation,
  discrete enrichment, ordinary Hom comparison and the chosen declaration names;
  and the item id in the upstream source: no existing match. The similarly named
  private helper in `KInjectiveSchemeEvaluationModels` concerns scheme modules,
  not simplicial categories. Read Mathlib's `SimplicialNerve`, enriched-category
  and ordinary nerve interfaces rather than introducing duplicate primitives.
- Kerodon source opened online: https://kerodon.net/tag/03N6 and
  https://kerodon.net/tag/03N7. They define the strict enriched Hom pairing and
  assert it models the Hom functor for a locally Kan simplicial category. As the
  node itself says, the specific Sing-realization counit comparison is the
  agent-formulated calculation in HTT 1.1.5/2.2.4/5.1.3, not a quotation of 03N7.

Validation: prescribed `scompile.py` single-file checks, within the default 60 s
per-file limit. The explicit constructions were checked in both sandbox and module
positions. No global build, direct git command, live edit or shared-repository
write was performed. No statement correction or disputed assertion is needed.

## Second reading by Q66

I independently read the node and the complete module. The binders match: `C` is
small in universe `u`, with no nonemptiness or finiteness assumption. The first four
conjuncts render, respectively, the component weak equivalence, enriched composition,
the enriched unit equation, and functoriality in an arbitrary ordinary functor `F`.
The fifth conjunct uses the specified internal-Hom edge, its endpoint equations,
equivalence condition, and `HEq` component equations; it does not replace the edge
by unrelated pointwise equivalences. The sixth conjunct quantifies every restriction
map `r`, and the final conjunct is the stated arbitrary universe lift. The helper
definitions are canonical constructions with real data, while every postponed fact
is a named `sorry` theorem. Empty categories, empty Hom sets, repeated vertices,
identity arrows, and all ambient universe lifts remain included. I found no mismatch
between the node and Lean statement, and no change was needed.
