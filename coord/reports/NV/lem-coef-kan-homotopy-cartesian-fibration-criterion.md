## Worker report

The module `Sheaf.AlgebraicTopology.KanHomotopyCartesianFibrationCriterion` states
`SSet.Enhanced.kan_homotopy_cartesian_fibration_criterion`. Its only theorem proof
is `by sorry`; it introduces no definitions. The item's node changes only in `lean`.
No missing interface, correction, or disputed statement was found.

Source checked: Rezk, *Fibrations and Homotopy Colimits of Simplicial Sheaves*,
[Section 2.3 and Lemma 2.5, printed p. 4](https://rezk.web.illinois.edu/rezk-sharp-maps.pdf).
The initial direct browser request encountered verification; the web search returned
that primary PDF's complete relevant section and proof. Section 2.3 defines the
condition by replacing both cospan legs over the same base. Lemma 2.5 supplies the
right-proper comparison for one fibration leg. The module's docstring gives all three
steps of the node's expanded proof, including pullback invariance for the converse.

Hypothesis and clause correspondence:

- Small simplicial sets: `{Q X Y Z : SSet.{u}}`, with explicit `universe u`.
  This is the dependency's size convention, at arbitrary universe `u`.
- Maps `a`, `b`, `f`, `g`: precisely the four typed morphism binders
  `(a : Q ⟶ X) (b : Q ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)`.
- Commutativity `fa = gb`: `(h : a ≫ f = b ≫ g)`, in Lean composition order.
- The single Kan hypothesis on `g`: `[Fibration g]`, with
  `open scoped SSet.modelCategoryQuillen`. The scoped Mathlib instance defines
  fibrations by `J.rlp`, where `J` consists of all positive-dimensional horns.
- Homotopy cartesianness: the left side is literally the existential condition
  from `SSet.Enhanced.kan_fibrant_path_recognition`, without its separate
  fibrant-replacement/path-model parameters. The binders `Xf`, `Yf`, `i`, `j`,
  `ff`, `gf` introduce both replacements over the original `Z`;
  `i ≫ ff = f ∧ j ≫ gf = g` specifies the factorizations;
  `IsWeakHomotopyEquivalence i ∧ IsWeakHomotopyEquivalence j` specifies weak
  replacement maps; `Fibration ff ∧ Fibration gf` specifies both fibration legs.
  The existential `c` has both required projection equations and is weak. These
  equations uniquely characterize the induced map by the pullback universal
  property; this is not an arbitrary existential comparison.
- The canonical strict comparison `Q → X ×_Z Y`: `pullback.lift a b h`.
  Its projections are exactly `a` and `b`, by Mathlib's pullback lift equations.
- Weak homotopy equivalence of this map: the right side is
  `IsWeakHomotopyEquivalence (pullback.lift a b h)`.
  The dependency's predicate tests realization on components and on all positive
  homotopy groups at every basepoint, including the empty case.
- The equivalence “if and only if”: `↔` between precisely these propositions.
- No Kan-complex or nonemptiness assumption: none occurs in any binder.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.KanFibrantPathRecognition`,
  `SSet.Enhanced.kan_fibrant_path_recognition`: full signature and proof docstring
  read; its left-hand existential supplies the exact notion used here. Publicly
  imported. No second predicate is defined. The existing downstream
  `SSet.IsHomotopyCartesian` in `SharpPullbackCalculus` has this same body, but
  importing that node would reverse the proof-dependency direction; the recorded
  recognition interface already deliberately expands this condition.
- `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`,
  `SSet.KanQuillen.right_proper_kan_quillen_core`: full signature and proof
  docstring read; publicly imported. Its weak equivalences are the same
  realization predicate and its fibration structure is the scoped horn-lifting
  structure; factorization, right properness and two-out-of-three are the proof
  inputs, not additional hypotheses of the theorem.
- `Sheaf.AlgebraicTopology.KanPullbackFibrationInvariance`,
  `SSet.Enhanced.isWeakHomotopyEquivalence_pullback_map`: the stated proof
  prerequisite, imported without `public`. Full signature and proof docstring
  read. It requires Kan fibrations only on the two corresponding cospan legs,
  with arbitrary objects, exactly as the converse uses it.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.IsWeakHomotopyEquivalence`: read its definition and docstring;
  obtained through the public dependency imports.
- Mathlib `AlgebraicTopology.SimplicialSet.CategoryWithFibrations`: read
  `SSet.modelCategoryQuillen.J`, its scoped `CategoryWithFibrations` instance and
  `fibration_iff`. Mathlib `CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  read the canonical lift interface and projection equations, also already
  available through the dependency imports.

Edge cases checked against the node and source:

- Empty `Z`: any displayed maps into it force empty sources; both sides allow
  this case and impose no chosen vertex.
- Empty `Y` (hence empty `Q`): the strict pullback is empty. `∅ → Z` is Kan
  (all horns have a vertex), and the two-leg condition permits the identity
  replacement of this leg. Both sides include this case.
- Empty `Q` with nonempty strict pullback: the strict comparison is not weak on
  components, so the equivalence correctly excludes this from homotopy cartesian.
- `Z = Y = Δ[0]` and `g` the identity: the right side tests precisely `a : Q → X`;
  no Kan condition is introduced on `X`.
- Arbitrary non-Kan bases are admitted: take `g = 𝟙 Z`, always a Kan fibration.
  No terminal fibration on `Z` or replacement of the base occurs in the signature.
- The fibration hypothesis is substantive: the two different vertex inclusions
  into `Δ[1]` have empty strict pullback and nonempty contractible homotopy
  pullback; the non-fibration right leg is correctly excluded.

Searches performed in this session (the msearch wrapper also records these in
`searches.jsonl`):

- LeanFinder: “A commutative square of simplicial sets with a Kan fibration leg is
  homotopy cartesian exactly when its strict pullback comparison is a weak homotopy
  equivalence”. Eight hits: trivial-fibration pullback instances, homotopy classes,
  Whitehead, covering homotopy. None states this criterion.
- LeanSearch: “A square of simplicial sets with a Kan fibration leg is homotopy
  cartesian iff the strict pullback comparison is a weak equivalence”. Eight hits:
  ordinary pullback/bicartesian squares, the scoped fibration instance, stability
  under base change and trivial-fibration pullback. No matching theorem.
- Loogle: `HomotopicalAlgebra.Fibration, HomotopicalAlgebra.WeakEquivalence`.
  Twelve hits: model axioms, trivial fibrations and abstract homotopy-category
  statements, with no two-leg homotopy-cartesian predicate or matching statement.
- msearch grep of Mathlib: `homotopy.?[Cc]artesian|homotopy.?[Pp]ullback`.
  Zero hits.
- Direct `rg` of upstream `WeilConjectures` and project `lean/Sheaf/AlgebraicTopology`:
  `homotopy.?[Cc]artesian|[Hh]omotopy[Pp]ullback|kan.*[Cc]riterion`.
  Upstream has no match. Project hits include `SharpPullbackCalculus` (the same
  replacement predicate but a different theorem with sharpness assumptions),
  `KanFibrantPathRecognition` (used), and other path/mapping-space constructions.
  No matching criterion theorem exists.
- Direct upstream `rg` for the item's id: zero hits.
- Direct `rg` for the proposed name `kan_homotopy_cartesian_fibration_criterion`
  in upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`: zero hits before
  creating the file.

Validation: prescribed `scompile.py NV lem-coef-kan-homotopy-cartesian-fibration-criterion`
compiled this single delivered file in its sandbox and library views, each clean
(1.7 s and 1.9 s respectively). Every universe and variable is explicitly bound;
`set_option autoImplicit false` is present. Lines are at most 100 characters.

## Second reading by NV

Independent maintainer reading of immutable delivery
`f7e20df09d816dcf9aa0264caa75a767ed9552c3`, 2026-10-17. This reader did not
write or previously second-read the delivery. This section replaces the delivered
worker self-check; the Worker report above is preserved verbatim.

I read the packet, the immutable item node and module, both statement-dependency
nodes, their recorded source modules and docstrings, the pullback-invariance proof
prerequisite, and the weak-equivalence and Mathlib fibration/pullback declarations.
The snapshot dependency records agree with the corresponding read-only NV records.

Clause-by-clause comparison:

- Small simplicial sets are `{Q X Y Z : SSet.{u}}`. The explicit arbitrary universe
  `u` is the recognition dependency's convention; there is no universe equality
  imposed between otherwise independent constructions.
- The four arrows are exactly `(a : Q ⟶ X) (b : Q ⟶ Y) (f : X ⟶ Z)
  (g : Y ⟶ Z)`. Commutativity is `(h : a ≫ f = b ≫ g)`.
- The only original-leg hypothesis is `[Fibration g]`. With the opened
  `SSet.modelCategoryQuillen` scope this is the right lifting property against
  every positive-dimensional horn, including both outer horns.
- The left side quantifies both replacement objects `Xf Yf` and all four arrows
  `i j ff gf`. Its two factorization equations, two weak-equivalence clauses,
  two fibration clauses, and comparison with both projection equations and its
  weak-equivalence clause reproduce the entire left side of
  `SSet.Enhanced.kan_fibrant_path_recognition`, identically after whitespace
  normalization. The projection equations uniquely specify the comparison, so
  the existential does not permit an unrelated map.
- The right side is precisely
  `IsWeakHomotopyEquivalence (pullback.lift a b h)`. Mathlib's `lift_fst` and
  `lift_snd` give the stipulated coordinates. The predicate from
  `EnhancedDiagramsCones` tests bijectivity on realized path components and all
  positive based homotopy groups. The conclusion is the full equivalence `↔`.
- No Kan-complex or nonemptiness assumption on any original object occurs.
  All variables and universes are bound, with `autoImplicit false`.

Source and proof audit: I read the indexed text of Rezk Section 2.3 and Lemma 2.5,
printed p.4. The author's direct PDF returned a browser verification page; web
search exposed the relevant primary-paper text through its CiteSeer copy. Section
2.3 uses the two-leg weak-equivalence/fibration factorizations over the same base.
Lemma 2.5 uses right properness for the one-fibration pullback comparison, without
requiring fibrant corners. The delivered three-step proof correctly extends that
comparison to an arbitrary commuting square. In step 1 the comparison is the base
change of `i` along the first projection, a pullback of `g`. Step 2 uses the
admissible identity replacement of `g`. In step 3 the recorded invariance theorem
applies with corresponding fibration legs `g` and `gf`, component maps `j`, identity,
`i`, and the factorization equations. Swapping the coordinates is an isomorphism;
the composite from `Q` has exactly the replacement comparison's coordinates.
Two-out-of-three gives the converse. The module docstring records all three steps.

Edge cases checked: empty base (forcing all sources empty), either empty cospan
source, empty `Q` with a nonempty strict pullback (rejected by the component test),
`g` the identity on an arbitrary non-Kan base, and `Y = Z = Δ[0]`. No argument
chooses a point. The distinct vertex inclusions into `Δ[1]` show why the fibration
hypothesis must be retained; neither inclusion satisfies it.

Independent `rg` searches for homotopy cartesian/pullback terminology and for the
proposed declaration name found no duplicate in Mathlib or upstream
`WeilConjectures`. The project recognition and invariance declarations state
different results. `SharpPullbackCalculus.IsHomotopyCartesian` has the same
replacement body, but belongs to the downstream calculus; expanding the already
recorded recognition interface here adds no second definition and avoids that
import dependency. All three required search kinds are recorded in the Worker
report. No missing helper or unusable recorded dependency was found. No §1(B) or
§1(C) repair, new node, or citer audit is needed.

Gates: the delivered module has no definitions and exactly one theorem with proof
`by sorry`; no local theorem was proved. Both module and theorem docstrings name
the source and blueprint item. Imports distinguish statement from proof
prerequisites; no pro-etale substitute is involved. All Lean lines are at most
100 characters. The JSON `lean.statement` is the exact source signature with
whitespace flattened, and only the item's `lean` field differs from the NV context
node. No Lean or node change is required.

Fresh reproducibility check: the prescribed `scompile.py NV
lem-coef-kan-homotopy-cartesian-fibration-criterion <immutable module path>` exited
0 with no diagnostics. Its current implementation dispatches to the server's
private side overlay; it reported sandbox compilation in 1.9 s and library-view
compilation in 1.5 s, each with the 60-second per-file limit. This reproduces the
Worker report's clean two-view per-file result. No global build, live Lean write,
Git mutation, delivery, or landing was performed.

Finding and correction: H11 / brief §6 requires an independent reading. The old
section was a substantive but explicitly worker-authored self-check. This complete
replacement report records the independent reading above. Mathematics, statement,
Lean source, and node records require no correction.
