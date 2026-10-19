## Worker report

The module `lean/Sheaf/CategoryTheory/CoconeRestrictionInitial.lean` states
`SSet.Enhanced.cocone_restriction_initial`, with one `sorry` and no proved theorem.
The helper `rightJoinPrismSimplex` supplies real data for the specified cylinder
map on each simplex. No definition or theorem from another DAG node is restated.
There is no statement correction and no disputed mathematical assertion.

Hypothesis and clause correspondence:

- A small simplicial set is `K : SSet.{u}`. The containing universe is
  `max u v`, with arbitrary `v`; `E : SSet.{max u v}` and `[Quasicategory E]`.
  `SSet.uliftFunctor.{v}.obj K` transports the small base to that containing
  universe. This imposes no equality between the base and target universes.
- The right join is the existing `rightJoinCone`, and its pure-base inclusion
  is the existing `rightJoinConeInclusion`. The supplied `c` is a simplicial
  map from exactly that right join into `E`.
- The induced coherent cocone is supplied as the vertex `μ` of
  `coconeCategory (rightJoinConeInclusion _ ≫ c)`, with its defining coordinate
  equations. `hμ_apex` specifies the image under `c` of the pure new final
  vertex, using `orderedJoinInr`. `hμ` specifies the entire transformation
  `coconeHomotopy _ μ` in every degree, for every base simplex and interval
  simplex. These binders unpack the canonical induced cocone; they do not
  allow a different transformation, an arbitrary comparison map, or an
  existence-based choice. Both the apex and transformation are specified,
  including when the base is empty.
- `rightJoinPrismSimplex` first takes the canonical `joinGenerator` of the
  original `n`-simplex with the point, giving an `(n+1)`-simplex. It then
  restricts by the order map supplied by the existing `simplexFinalPrism n`
  on the identity `n`-simplex and the interval simplex. That map keeps the
  initial vertices where the interval has value zero and sends every final
  vertex where it has value one to the new final vertex. Consequently this
  is precisely the interval-splitting formula of the node, including its
  pure-factor cases, without introducing a second join construction.
- The mathematical hypothesis that this induced coherent cocone is
  colimiting is exactly `hc : IsColimiting (rightJoinConeInclusion _ ≫ c) μ`.
  `IsColimiting` is the recorded initial-object predicate on the actual
  coherent comma cocone category, not ordinary Hom-set initiality.
- `∀ t : rightJoinCone ... ⟶ E` covers every target cone. There is no equality
  or equivalence hypothesis on the restrictions of `t` and `c`.
- The first two conclusion clauses assert `KanComplex` for the right-pinched
  mapping spaces in the full cone functor object and the base functor object.
- The last clause is `IsWeakHomotopyEquivalence (mappingSpaceMap
  ((MonoidalClosed.pre (rightJoinConeInclusion ...)).app E)
  (diagramVertex c) (diagramVertex t))`. Thus the map itself is exactly
  restriction, and the endpoint images are the restricted diagrams. Weak
  equivalence uses the dependency's geometric-realization, component, and
  based-homotopy-group predicate.

Dependencies read and used:

- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `coconeCategory`,
  `IsColimiting`, `mappingSpace`, `mappingSpaceMap`, `diagramVertex`, and
  `IsWeakHomotopyEquivalence`. I read their full definitions and docstrings.
- Landed `def-coef-infinity-relative-cone`, module
  `Sheaf.CategoryTheory.RelativeInfinityCone`: `rightJoinCone` and
  `rightJoinConeInclusion`, defined from the existing ordered join and its
  pure-factor inclusion. The full node statement and module were read.
- Landed `lem-coef-infinity-slice-right-fibration`, module
  `Sheaf.CategoryTheory.JoinSliceRightFibration`: `joinGenerator` and
  `orderedJoinInr`. These are construction helpers; its right-fibration
  theorem is not reasserted. The full signature/docstring and node statement
  were read.
- Landed `lem-coef-infinity-final-index-colimit`, module
  `Sheaf.CategoryTheory.FinalIndexColimit`: `coconeHomotopy` and
  `simplexFinalPrism`. The complete module and node statement were read.
- The underlying `orderedJoinFunctor` and `joinAugmentation` come from
  `Sheaf.AlgebraicTopology.PushoutJoinSaturation`, whose construction and
  declaration docstrings were also inspected.

The three added `stmt_deps` already have landed Lean records. The standing
brief §5 expressly permits adding landed dependencies; no dependency record
is changed. A graph traversal through statement and proof dependencies of
all three finds no path back to the item (98, 86, and 92 reachable nodes,
respectively), so these additions do not create a dependency cycle.

Edge cases checked before writing:

- Empty `K`: the right join still has the new vertex. `hμ` is vacuous on base
  simplices, but `hμ_apex` still fixes the apex. Colimiting means this apex is
  initial. The conclusion is `Map(initial,t) → point`, a weak equivalence.
- A one-point base: the cone is an arrow, and a colimiting cone has an
  equivalence as its structural arrow. The varying-base mapping assertion
  is the expected universal-arrow property.
- Disconnected or higher-dimensional bases are unrestricted; `hμ` is imposed
  on all simplices, not only vertices or edges.
- The constant-zero interval simplex yields the original base simplex;
  the constant-one interval simplex yields the degenerate cone-point
  simplex; mixed simplices retain exactly the initial zero block.
- Empty mapping spaces are allowed. Kan complexes carry no dimension-zero
  inhabitation hypothesis. No completeness, nonemptiness, or existence of
  other colimits is assumed for `E`.
- Both universes are explicitly bound. The target can lie in any containing
  universe; lifting only changes the representation of the small base.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A colimit cocone in a quasicategory is initial
  relative to restriction to its base, inducing weak equivalences on mapping
  spaces with varying target bases”. Eight hits, including ordinary
  `CategoryTheory.Limits.Cocone.isColimitEquivIsInitial` and horn filling,
  but no coherent varying-base statement.
- `msearch.py ... loogle`: `SSet.Quasicategory,
  SSet.Enhanced.IsColimiting, SSet.Enhanced.mappingSpaceMap`. Zero hits;
  the external index does not know the side-library enhanced definitions.
- `msearch.py ... grep`: `join|rightCone|cocone|colimit|mappingSpace` under
  `AlgebraicTopology/Quasicategory`. Zero hits.
- `msearch.py ... leansearch`: “A colimit diagram induces equivalences on
  outgoing mapping spaces under restriction from a cone to its base in an
  infinity category”. Eight ordinary colimit results, including
  `IsColimit.homEquiv`, `Cocone.isColimitYonedaEquiv`, and WithInitial cocone
  transport. None applies to arbitrary quasicategories and their mapping
  simplicial sets. The ordinary cone-category source and IsLimit source
  were opened to check the distinction.
- `rg` in Mathlib, upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no existing `cocone_restriction_initial`
  or `rightJoinPrismSimplex`; upstream search for this node id had no match.
  Searches for right joins, cocone restriction, join/cocone conversion,
  cylinder maps, and interval splitting found the landed constructions used
  above. They found no canonical right-join prism map already defined.
- The existing `lem-coef-infinity-join-cone-calculus` node was read; it has no
  Lean record. No theorem from it is assumed or restated: only the canonical
  simplex formula explicitly specified by the present item's own statement
  is encoded here using already landed data constructions.

Source check: opened [Kerodon 02XB](https://kerodon.net/tag/02XB),
[02X1](https://kerodon.net/tag/02X1), and
[01KX](https://kerodon.net/tag/01KX). The colimit dual of 02XB with target a
point gives precisely relative initiality under restriction, and 02X1
confirms that its mapping-space test quantifies over arbitrary target base
diagrams. The module docstring gives the complete natural-language proof
route: fixed-fiber comparison, initiality, cartesian restriction, and the
fiberwise-to-relative initiality criterion.

Validation: `scompile.py Q115 lem-coef-infinity-cocone-restriction-initial
lean/Sheaf/CategoryTheory/CoconeRestrictionInitial.lean` compiled both the
sandbox and library forms cleanly (1.4 s and 1.5 s), without warnings. All
Lean lines have length at most 100. All variables and universes are explicitly
bound, and the sole theorem proof is `sorry`.

Further source verification opened Kerodon Example the project server (04J5),
Proposition the project server (02WU), and Corollary the project server (02VW). The last
two give exactly the cartesian-fibration and initial-object steps of the
docstring proof, with their original (not opposite) orientations.


## Second reading by Q115

I independently opened the repository node, its sandbox copy and Lean module,
all four statement-dependency nodes and their recorded source modules. I also
read the ordered-join construction in `PushoutJoinSaturation.lean`, the three
available proof-dependency declarations, and the as-yet-unbound
`lem-coef-infinity-join-cone-calculus` node. There are no new nodes or dependency
repair modules in this delivery, no statement_change, and no repair-note file
for this item. The mathematical statement and its signature require no change.

Source reading: [Kerodon 02XB](https://kerodon.net/tag/02XB) assumes an arbitrary
simplicial set K and a functor of infinity categories. Taking the target category
to be a point and dualizing gives initiality relative to base restriction for
colimits. [Kerodon 02X1](https://kerodon.net/tag/02X1), condition (2), tests the
mapping-space square against every comparison diagram, with no equality of
boundary diagrams. [Kerodon 04J5](https://kerodon.net/tag/04J5) supplies the
fixed-boundary join/slice comparison; the present node explicitly specifies its
coherent comma convention and cylinder map. These are online Kerodon references,
not Stacks tags, so there is no corresponding Stacks .tex source to consult.
Neither source adds completeness, finiteness, nonemptiness, or an ordinary
category hypothesis to this specialization.

Object/hypothesis/conclusion inventory and correspondence (all verdicts pass):

1. Small simplicial set K: `(K : SSet.{u})`, with `universe u v` explicitly
   declared. No quasicategory structure is imposed on K. The target is
   `(E : SSet.{max u v}) [Quasicategory E]`. The degreewise `uliftFunctor.{v}`
   is Mathlib's size transport, so the two sizes are not forced equal.
2. The specified ordered right cone and base inclusion: `rightJoinCone` and
   `rightJoinConeInclusion` from `RelativeInfinityCone.lean` are respectively
   `orderedJoinFunctor.obj (K, Δ[0])` and `orderedJoinInl K Δ[0]`.
   I read these definitions and the terminal augmentation/convolution giving
   the pure and mixed summands. These are the node's join, not an arbitrary
   cone object or the left join. `c` is a map from exactly this cone into E.
3. The induced coherent cocone, including its apex: `μ` is a vertex of
   `coconeCategory (rightJoinConeInclusion _ ≫ c)`. Its existing comma definition
   fixes the zero endpoint to that base diagram and the one endpoint to the
   constant diagram on `μ.1.1`. `hμ_apex` identifies that apex with the image
   under c of the pure second-factor vertex, using `orderedJoinInr`.
4. The prescribed whole cylinder transformation: `hμ` is quantified over every
   `n : ℕ`, every base n-simplex `s`, and every interval n-simplex `a`.
   It equates `coconeHomotopy ... μ` with `c.app _ (rightJoinPrismSimplex _ n s a)`.
   I unfolded `coconeHomotopy`: its two internal-hom identifications extract and
   uncurry precisely the transformation stored in the comma vertex. Thus these
   equations specify all higher coherences, not only the component arrows.
   The helper first forms the convolution generator of s with the point and
   applies the simplex operator given by `simplexFinalPrism n` on `(id,a)`.
   Reading that prism's `toFun`, vertex i goes to i if a(i)=0, and to the new
   last vertex otherwise. This is exactly the node's interval-splitting map.
   The extra μ binder with these defining equations is an explicit presentation
   of the induced cocone, not an additional unrelated cocone assumption.
5. Colimiting hypothesis: `hc : IsColimiting (rightJoinConeInclusion _ ≫ c) μ`.
   I read `IsColimiting`, `IsInitial`, `mappingSpace`, and `IsContractible`:
   this is weak contractibility of all outgoing right-pinched mapping spaces
   in the actual coherent comma category. It is not ordinary Hom-set initiality.
6. Every target cone, including a varying base: `∀ t : rightJoinCone ... ⟶ E`
   follows the colimiting hypothesis. No restriction on t or equation with the
   restriction of c occurs anywhere in its binders.
7. Source Kan clause: the first conjunct is `KanComplex (mappingSpace
   ((ihom (rightJoinCone ...)).obj E) (diagramVertex c) (diagramVertex t))`.
   `ihom` is the existing functor simplicial set, and `diagramVertex` converts
   each actual map to its degree-zero simplex. These are the required endpoints.
8. Target Kan clause: the second conjunct uses `(ihom (uliftFunctor.obj K)).obj E`
   and the vertices of `rightJoinConeInclusion _ ≫ c` and
   `rightJoinConeInclusion _ ≫ t`. Both endpoint diagrams are the actual
   restrictions, with their simplicial data retained.
9. Actual weak equivalence: the final conjunct applies
   `IsWeakHomotopyEquivalence` to `mappingSpaceMap
   ((MonoidalClosed.pre (rightJoinConeInclusion _)).app E)
   (diagramVertex c) (diagramVertex t)`. I read `mappingSpaceMap`: it applies
   the simplicial functor degreewise to the pinched simplex, with the induced
   endpoint images. Here the functor is precisely precomposition/restriction.
   The weak-equivalence predicate uses realization, bijectivity on path
   components and all positive based homotopy groups, as required by the node.
   All three conjuncts concern the same two mapping spaces and restriction map.

Edge cases: for empty K, hμ has no base simplices to constrain but hμ_apex
still fixes the unique apex datum. The comma cocone category is then E up to
the canonical identification, and colimiting is initiality of that apex. The
conclusion becomes its contractible outgoing mapping space mapping to a point.
For K a point, the structural arrow of a colimit is an equivalence; arbitrary
t remains an arbitrary arrow and its base is allowed to differ. At n=0 the
helper gives the two endpoint vertices; all-zero interval simplices give the
pure base simplex, all-one simplices give the degenerate apex, and a mixed
interval simplex retains precisely its initial zero block. Degeneracies and
higher-dimensional K are unrestricted. Empty mapping spaces are allowed by the
recorded Kan convention. Empty E admits no c since the right cone has a vertex;
this correctly makes the implication vacuous, including when K is empty.
There are no ring, characteristic, scheme or zero-object parameters here.
The universe lift is coordinatewise and preserves every simplex and operator;
setting v=0 includes equal sizes, while arbitrary v includes larger target sizes.

Independent searches, using different formulations from the first worker:

- `msearch.py ... leanfinder`: "Restriction along the inclusion into a simplicial
  right cone is fully faithful on outgoing morphism spaces from a colimit
  diagram". Eight hits, mostly fully faithful nerves and simplex inclusions;
  none concerns this relative colimit mapping-space assertion.
- `msearch.py ... loogle`: `"Cocone", "IsInitial"`. Three ordinary category
  results, including `CategoryTheory.Limits.Cocone.isColimitEquivIsInitial`.
  I opened its Mathlib source and category binders; it cannot state this
  arbitrary-quasicategory assertion with a varying target base.
- `msearch.py ... leansearch`: "Colimit diagrams in an infinity category
  represent the functor of coherent cocones over varying diagrams". Eight
  ordinary colimit constructions/universal properties, no matching declaration.
- `rg` on Mathlib's AlgebraicTopology and CategoryTheory/Limits, upstream
  WeilConjectures, side `lean/Sheaf/CategoryTheory` and AlgebraicTopology, and
  `dag/lean_names_upstream.json`, using `prism|Prism`, cone/restriction in both
  orders, colimit/restriction, and both proposed declaration names. No existing
  theorem or general right-join cylinder helper was found. I read the nearby
  `simplexFinalPrism`, `rightPinchPrism`, join generators and inclusions: the
  first is reused, the second interchanges the factors of the standard-simplex
  prism, and none supplies the helper for a general K. The existing
  join-cone-calculus DAG node gives the comparison theorem; this delivery
  neither restates nor assumes that theorem as a hypothesis.

Mismatches found and repairs:

- H8: the first docstring described the source's cartesian-fibration argument,
  rather than carrying the node's four proof steps. Replaced only that proof
  prose with the node's opposite/joint-boundary comparison, natural pinch and
  realization comparisons, fixed-base colimit criterion, trivial-fibration
  base change, and final Kan/restriction identification, in that order.
- Stage-2 rule 7: explicit non-public proof imports were missing for the stated
  proof dependencies `lem-coef-infinity-pinch-comparison`,
  `lem-cbc-enhanced-functor-cone-calculus`, and
  `lem-coef-kan-quillen-right-proper`. Added their three module imports.
  The join-cone-calculus node has no Lean record/module yet, so there is no
  module to import for it. No construction required to type the item is absent.
- No mathematical, dependency-interface, hollow-definition or signature defect
  was found. There is one helper with real construction data and one theorem
  whose entire proof is `sorry`. No theorem was proved. The existing
  `lean.declarations` lists exactly these two declarations; no node record
  change was needed during second reading.

Validation after these repairs: `scompile.py Q115
lem-coef-infinity-cocone-restriction-initial
lean/Sheaf/CategoryTheory/CoconeRestrictionInitial.lean` passed in both sandbox
(1.6 s) and library (1.5 s) forms, with no errors or warnings. An exact text
comparison confirms `lean.statement` is verbatim the theorem signature. No line
exceeds 100 characters, and both universes and every variable are explicitly
bound under `autoImplicit false`. Only `lean` and the three landed additions to
`stmt_deps` differ from the repository node; the natural statement and proof
fields are unchanged.
