## Worker report

The module `Sheaf.AlgebraicTopology.KanHomotopyCartesianInvariance` states
`SSet.Enhanced.kan_homotopy_cartesian_invariance`, with its proof exactly `by sorry`.
It introduces no definitions and proves nothing. The node's statement is unchanged.

Hypothesis and conclusion correspondence:

- Small simplicial sets: `{Q X Y Z Q' X' Y' Z' : SSet.{u}}`, with `universe u`
  explicitly declared. The eight objects have no Kan or inhabited instances.
- First square: `a : Q ⟶ X`, `b : Q ⟶ Y`, `f : X ⟶ Z`, `g : Y ⟶ Z`;
  its strict commutativity is `h : a ≫ f = b ≫ g`.
- Second square: `a'`, `b'`, `f'`, `g'` have the corresponding primed types;
  `h' : a' ≫ f' = b' ≫ g'` is its strict commutativity.
- The four maps of corners are `eQ`, `eX`, `eY`, `eZ`, with exactly the
  source/target types specified in the node.
- Commutation with every edge is rendered by `ha : a ≫ eX = eQ ≫ a'`,
  `hb : b ≫ eY = eQ ≫ b'`, `hf : f ≫ eZ = eX ≫ f'`,
  and `hg : g ≫ eZ = eY ≫ g'`. These are all four faces, in diagram order.
- Their weak homotopy equivalences are the four hypotheses `heQ`, `heX`, `heY`,
  `heZ`, each using the existing `SSet.Enhanced.IsWeakHomotopyEquivalence`.
- Homotopy cartesianness of the first square is the first existential:
  `Xf`, `Yf`, maps `i`, `j`, `ff`, `gf`; `i ≫ ff = f` and `j ≫ gf = g`;
  `IsWeakHomotopyEquivalence i` and `IsWeakHomotopyEquivalence j`;
  `Fibration ff` and `Fibration gf`; then `c : Q ⟶ pullback ff gf` with
  the two specified projection equations and `IsWeakHomotopyEquivalence c`.
  This is verbatim the left-hand condition of `kan_fibrant_path_recognition`.
- The second existential renders exactly the same condition for the primed square,
  including both weak equivalences, both fibrations, both projection equations,
  and the weak-equivalence comparison from `Q'`.
- The connective is `↔`, so both preservation and reflection are included.

Dependency declarations read in full and used:

- Public import `Sheaf.AlgebraicTopology.KanFibrantPathRecognition`, declaration
  `SSet.Enhanced.kan_fibrant_path_recognition`. Its two-leg condition supplies
  precisely the conclusion convention. The theorem is used by the recorded proof plan.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones` (publicly exposed by recognition),
  `SSet.Enhanced.IsWeakHomotopyEquivalence`: realization induces a component
  bijection and bijections on all positive based cubical homotopy groups.
- Mathlib's `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  and `HomotopicalAlgebra.Fibration`, with the scoped
  `SSet.modelCategoryQuillen` Kan-fibration instance used by recognition itself.
- Proof import `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`,
  `SSet.KanQuillen.right_proper_kan_quillen_core`: functorial replacements,
  identification of Kan objects, and model two-out-of-three.
- Proof import `Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`,
  `SSet.Enhanced.kan_homotopy_pullback_invariance` and its canonical
  `simplicialHomotopyPullbackMap`: weak equivalence of the replaced path pullbacks.

One-definition check: `SSet.IsHomotopyCartesian` in
`Sheaf.AlgebraicTopology.SharpPullbackCalculus` expands to the same existential.
That module owns the downstream `lem-coef-sharp-pullback-calculus`, whose proof
explicitly depends on this item. Importing it here would create a cycle when that
proof import is added. Recognition already deliberately expands this same condition
for this reason; this item follows its usable recorded interface. There is no private
copy or new predicate. The item is not an already existing statement: the sharp
calculus gives sharp-map criteria and pasting, not arbitrary objectwise invariance.

Edge cases checked: identities on the four corners give a reflexive iff; an empty
corner is not excluded by any binder or weak-equivalence definition; all-empty
squares are permitted; no point is selected. Non-Kan original objects remain
arbitrary, since only the proof plan passes to Kan replacements. A terminal base
specializes to product comparison without changing the statement. The universe `u`
is arbitrary, so there is no finite/countable or fixed-small-universe restriction.
Both replacements in each condition map to the original base, not to its fibrant
replacement, and neither leg's fibration requirement is omitted.

Searches made on 2026-10-17:

- `msearch.py ... leanfinder`: "Objectwise weak homotopy equivalences of strictly
  commutative squares of arbitrary simplicial sets preserve and reflect homotopy
  cartesianness". Eight hits: bifibrant weak-equivalence transport, Whitehead,
  homotopy-class pre/postcomposition and path/cylinder homotopy invariance; no
  square theorem. These require different objects or conclude different properties.
- `msearch.py ... leansearch`: "Objectwise weak equivalences of squares of simplicial
  sets preserve and reflect homotopy cartesian squares". Eight hits include
  `Square.IsPullback.iff_of_equiv` and `.map_iff`, ordinary categorical pullback
  transport, and weak-equivalence instances in over/bifibrant categories. None
  states homotopy cartesianness under corner weak equivalences.
- `msearch.py ... loogle`: `HomotopicalAlgebra.PathObject,
  HomotopicalAlgebra.WeakEquivalence`. Five hits on path-object construction,
  diagonal/projection weak equivalences and right-homotopy invariance. No match.
- `msearch.py ... grep`: `homotopy.?cartesian|homotopy.?pullback|fibrant.*cospan`
  in Mathlib/AlgebraicTopology: zero hits.
- `rg` for `homotopy.?cartesian|homotopy.?pullback` and the item id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no matching theorem.
- `rg` across `lean/Sheaf` located the recognition, path-pullback invariance and
  downstream sharp calculus modules, all inspected. No arbitrary-square invariance
  statement exists there. The proposed full declaration name has no occurrence in
  Mathlib, upstream sources or `lean/Sheaf`; the upstream name index has no match.

Source access: the specified Rezk PDF URL was opened, but the web reader received
an anti-bot verification page. No source-based change is made or claimed; the
unchanged node and its recorded recognition dependency supply the exact convention.
The module docstring includes the node's complete three-step natural-language proof.

Validation: `scompile.py NW lem-coef-kan-homotopy-cartesian-invariance` compiled
the sandbox and library forms cleanly (1.9 s and 1.6 s respectively), with exit 0.

No new nodes, dependency repairs, statement correction, or disputed statement.

## Second reading by NW

Independent second reading of the immutable delivery. I read the item node, the full
`lem-coef-kan-fibrant-path-recognition` dependency node and declaration, the source-place
record, the delivered module, and this report. The item introduces eight small simplicial
sets in one arbitrary universe `u`, four maps and one strict commutativity equation for
each square, four corner comparison maps, four edge-commutation equations, and four
`IsWeakHomotopyEquivalence` hypotheses. The Lean binders `a b f g`, `a' b' f' g'`, `h h'`,
`eQ eX eY eZ`, `ha hb hf hg`, and `heQ heX heY heZ` render exactly those objects and
hypotheses with the stated orientations; no Kan, inhabitance, nonemptiness, point,
Noetherian, finiteness, or characteristic assumption is added.

Both conclusion sides are the dependency's two-leg fibration-replacement condition
verbatim: `Xf,Yf` (respectively primed), weak-equivalence maps `i,j`, maps `ff,gf` into
the original base, both factorization equalities, both fibration clauses, and a map from
the square corner into the categorical pullback satisfying both projection equalities and
weak equivalence. The connective is `↔`, so preservation and reflection are both present.
The same-universe quantification is the small-simplicial-set convention used by the
dependency; empty and non-Kan corners remain allowed, and identity comparisons, empty
squares, and terminal bases are covered.

I checked the exact declarations used in the read-only group clone:
`SSet.Enhanced.kan_fibrant_path_recognition`,
`SSet.Enhanced.kan_homotopy_pullback_invariance`,
`SSet.KanQuillen.right_proper_kan_quillen_core`, and
`SSet.Enhanced.IsWeakHomotopyEquivalence`. Their universes and interfaces agree with
the imports and docstring proof plan. The module has no definition, private copy,
pro-etale substitute, or dependency-cycle import; the named downstream sharp-calculus
predicate is intentionally not imported because it depends on this item. Mathlib/project
searches recorded in the worker report found no exact existing theorem. The Rezk URL
remains inaccessible behind verification, as already recorded; no source-based correction
is claimed.

The module docstring and declaration docstring name the Rezk source place and
`(blueprint: lem-coef-kan-homotopy-cartesian-invariance)` and give the three proof steps.
The declaration is a theorem with the permitted `by sorry` proof and no hollow definition.
No line exceeds 100 characters and `set_option autoImplicit false` leaves no unbound
variables. The immutable module compiled successfully with:
The command was `scompile.py NW lem-coef-kan-homotopy-cartesian-invariance`,
with the snapshot file path supplied as the Lean file argument.
(local sandbox and library forms, exit 0; only the expected `sorry` warning).

Finding and repair: the prior section was labelled a self-check and expressly delegated
independent review to the maintainer, so it did not satisfy the real second-reading
requirement. This replacement section records the independent audit above. No Lean, node,
or statement change is needed.
