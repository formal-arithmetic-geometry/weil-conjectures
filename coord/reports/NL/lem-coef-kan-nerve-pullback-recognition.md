## Worker report

The module `lean/Sheaf/CategoryTheory/KanNervePullbackRecognition.lean` states
`SSet.Enhanced.kan_nerve_pullback_recognition`.  It uses the coherent nerve of small Kan
complexes (`CategoryTheory.Spaces.infinityCategory`) and the path-pullback and cone
conventions from `SSet.Enhanced`.  Its first clause is the mapping-space (limiting-cone)
recognition: for every test Kan complex `X`, the internal-Hom square has the canonical
constant-path comparison, and this universal test is equivalent to the weak-equivalence
status of the original comparison `homotopyPullbackComparison f g r s hcomm`.

The strict square hypotheses are rendered by the four explicitly bound simplicial maps
`f : A ⟶ B`, `g : A ⟶ C`, `r : B ⟶ D`, `s : C ⟶ D`, Kan-complex instances for all
four corners, and the exact commutation equation `hcomm : f ≫ r = g ≫ s`.  The strict
comparison is the existing canonical path comparison, so its coordinates are the two
projections and the constant path at the common composite.

The specified-commutation clause binds an actual path map
`α : A ⟶ (ihom Δ[1]).obj D`, with both endpoint equations.  It binds a triangle witness
`T : A ⟶ (ihom Δ[2]).obj D` through all three face equations and compares the weak
homotopy-equivalence status of `specifiedHomotopyPullbackComparison` with the strict
constant-path comparison.  The final clause binds a second strict Kan square, maps
`a,b,c,d` on all corners, the four square-compatibility equations, and weak homotopy
equivalences on each corner map; it states invariance of the homotopy-cartesian test.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `SSet.Enhanced.mappingSpace`,
  `SSet.Enhanced.mappingSpaceMap`, `SSet.Enhanced.IsLimiting`, and the coherent cone
  infrastructure.
* `Sheaf.CategoryTheory.CoherentNerveInfrastructure`, declarations
  `CategoryTheory.CoherentNerve.nerveFunctor` and `CategoryTheory.CoherentNerve.SCat`.

The path comparison declarations are imported from their owning project modules:
`SSet.Enhanced.homotopyPullbackComparison` in
`Sheaf.CategoryTheory.RelativeInfinityCone` and
`SSet.Enhanced.specifiedHomotopyPullbackComparison` in
`Sheaf.CategoryTheory.InfinityHomotopyPullbackPasting`; these are canonical constructions
of the same path model and are not redefined.

Edge cases checked in the statement and source conventions: all four Kan complexes may
be empty or disconnected; no connectedness or chosen basepoint is bound; `X` ranges over
all small Kan complexes, including the empty one; the path object retains all simplicial
higher simplices; and the strict commutation case uses the constant path.  No additional
fibration, nonemptiness, or finite-generation hypothesis is present.

Searches made:

* `msearch.py ... leanfinder "A strict square of Kan complexes is a pullback in the homotopy coherent nerve of Kan if and only if it is a homotopy cartesian square"`: ordinary nerve/Segal and model-category hits only; no complete match.
* `msearch.py ... loogle "SSet.KanComplex, SimplicialNerve, IsHomotopyPullbackSquare"`: zero hits (the tool reported `SimplicialNerve` as an unknown identifier).
* `msearch.py ... grep "homotopyPullbackComparison|specifiedHomotopyPullbackComparison" AlgebraicTopology`: no Mathlib hits.
* `rg` over `lean/Sheaf` and the read-only upstream source found the canonical path comparisons in
  `RelativeInfinityCone.lean` and `InfinityHomotopyPullbackPasting.lean`, and no existing
  declaration for this recognition theorem.

Compilation was run with `scompile.py NL lem-coef-kan-nerve-pullback-recognition` and completed
cleanly for the module.

## Earlier second reading (a previous round; superseded)

The declaration, imports, explicit universes, endpoint equations, path coordinates, and invariance binders were reread against the two recorded dependency modules and the source description. The clean `scompile.py` result was reproduced; no additional statement or dependency change was made.

## Second reading by NL

This reading supersedes the earlier second reading above. I opened the current DAG
statement and all nine proof steps, both original statement-dependency modules, the
additional existing square-cone/space/path-comparison nodes and declarations, and the
Lean file. The old Lean did NOT state the node. I repaired the Lean; the mathematical
node statement and proof are unchanged. There is no `statement_change`.

Source reading: the node cites no Stacks tag. I read Riehl--Verity,
https://math.jhu.edu/~eriehl/recognizing.pdf, Theorem 6.1.4 on printed p.43 and Theorem
6.2.7 on printed p.51 (and their proofs and the surrounding size conventions).
The source assumes a Kan-enriched category, a simplicial indexing set and the actual
transposed coherent diagram/cone. Its recognition concerns that cone, not its boundary
homotopy classes. The second theorem's smallness is handled in a containing universe:
small Kan complexes have simplex universe u and their entire coherent nerve has universe
u+1. No Noetherian, finiteness, nonemptiness or fibration assumption is introduced.
For the fixed cospan, the pseudo-cone has exactly the two projection maps and its path
coordinate. I also read the existing square-cone definition node and its complete
`SuspensionSquareComparison` implementation: the square is the product of intervals,
its incoming boundary removes (0,0), and the coordinatewise-min contraction supplies
the entire specified cone cylinder. This is precisely the limiting-cone convention
needed here, including both nondegenerate square triangles.

Object/hypothesis/conclusion checklist (the step-1 list, with its Lean and verdict):

* Small Kan complexes and their function-complex enrichment: `Spaces.Kan`, the existing
  `Spaces.kanEnrichment`, and `Spaces.infinityCategory` from
  `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`. I read these definitions: enrichment
  is the restriction of Mathlib's internal-Hom enrichment, and the infinity category is
  literally `SimplicialNerve Kan`, not a localization category or ordinary nerve. PASS.
* Subset-poset coherent nerve and its maps: the existing `CoherentNerveInfrastructure`
  imports Mathlib's `SimplicialNerve`; its `nerveFunctor` acts by enriched
  postcomposition. The new `kanNerveObject`, `kanNerveHom`, `kanNerveEdge` and
  `kanNerveTriangle` merely read coordinates of that existing nerve. The triangle
  reads the subset inclusion {0,2} into {0,1,2}, oriented diagonal-to-composite. PASS.
* Four corners: every strict/specified clause explicitly binds
  `{A B C D : SSet.{u}}` with the four `[KanComplex ...]` instances. No selected
  basepoints, connectedness, essential-smallness hypotheses or added fibrations. PASS.
* Boundary arrows: the four maps are `f : A ⟶ B`, `g : A ⟶ C`, `r : B ⟶ D`,
  `s : C ⟶ D`. `KanSquarePresentation` pins corners (0,0),(1,0),(0,1),(1,1) to
  A,B,C,D with its four object equations, and pins every boundary edge to precisely
  these maps using four HEq equations on map vertices. HEq is used only to transport
  the dependent function-complex types along those endpoint equalities. PASS.
* Strict commutation: the first clause alone has
  `hcomm : f ≫ r = g ≫ s`. Its path is explicitly
  `f ≫ r ≫ constantDiagrams Δ[1] D`, and its comparison is the existing
  `homotopyPullbackComparison f g r s hcomm`. I read its body: the two pullback lifts
  use f and g, and the path coordinate is that constant path at fr. PASS.
* Path pullback P: `homotopyPullbackComparison` and
  `specifiedHomotopyPullbackComparison` target the same existing
  `simplicialHomotopyPullback r s`. I followed its iterated pullback and evaluations:
  the path starts at r(b) and ends at s(c), retaining all higher simplices. No private
  path model or unconstrained comparison map was introduced. PASS.
* Strict coherent square and limiting-cone conclusion: the first clause asserts
  nonemptiness of the matching presentations, and for EVERY presentation p states
  `(∃ t : SuspensionComparison.SquareCone p.square,
  IsLimiting (SuspensionComparison.boundary p.square true) t.cone) ↔ ...q...`.
  `SquareCone` fixes both its apex and full cylinder, so existentially binding a
  representative cannot substitute an unrelated limiting cone. Its existence is
  ordinary endpoint verification, not a new mathematical hypothesis. PASS.
* Specified H: the second clause binds any
  `α : A ⟶ (ihom Δ[1]).obj D` and the two exact evaluation equations to fr and gs.
  This is the internal-Hom transpose of the node's `A × Δ[1] → D`; the symmetry in
  `kanCommutationEdge` accounts explicitly for Mathlib's tensor-factor convention.
  There is NO `hcomm` in this clause. PASS.
* Triangle witnesses: `KanSquarePresentation.commutation` supplies T in the actual
  2-simplices of Fun(A,D). Its δ₂ is the square's A-B-D triangle, δ₀ is the supplied
  α edge, and δ₁ is the A-C-D triangle. Thus left triangle followed by α equals
  right triangle with a specified witness; it does not require the three faces to
  equal α. A normalized presentation has diagonal fr, constant left triangle and
  right triangle α, with T the corresponding degenerate 2-simplex. The theorem
  asserts presentations exist for every H, and tests all compatible presentations.
  PASS; in particular the conclusion is never vacuous from missing presentations.
* Specified cartesian iff weak comparison: the second clause uses the SAME limiting
  square-cone predicate and exactly
  `specifiedHomotopyPullbackComparison f g r s α hα₀ hα₁`, with the given H coordinate.
  It does not assert independence from H or compare H to a constant path. PASS.
* Whole coherent diagram equivalences: the third clause quantifies all
  `F G : SuspensionComparison.square ⟶ Spaces.infinityCategory.{u}` and assumes
  `AreNaturallyEquivalent F G`. I read that predicate: it supplies an edge of the
  entire internal functor simplicial set with the two inverse-triangle witnesses.
  It preserves AND reflects the displayed limiting-cone predicate. It applies also
  when neither coherent square is a strict presentation. The product of intervals
  is the standard simplicial model of N([1] × [1]). PASS.
* Objectwise weak-equivalence zigzags of strict diagrams: the last clause binds
  both strict squares, all four corner maps a,b,c,d, all four naturality equations,
  both strict-commutation equations, and all four weak-equivalence hypotheses.
  The iff between `IsHomotopyPullbackSquare` tests handles each step in either
  direction, hence every finite zigzag by iteration. By the first clause this is
  the node's cartesianness assertion. PASS.
* An arbitrary coherent square equivalent to a strict presentation: combine the
  third clause's iff for that ENTIRE square equivalence with the first clause's
  iff for the presentation. This is exactly the final 'in particular' statement;
  it imposes no strictness condition on the arbitrary coherent square. PASS.
* No replacement by vertices or edge classes: the full square simplicial map,
  both of its triangles and the function-complex composition witness remain in
  `KanSquarePresentation`, and equivalence is in the entire functor object. PASS.

Mismatches found and repaired:

1. The old Lean asserted a universal internal-Hom weak-equivalence test instead of
   `IsLimiting` of the actual square cone. Replaced it by limiting-cone recognition.
2. The old specified clause inherited strict commutation and compared its H-dependent
   comparison with the constant-path comparison. Removed both errors: arbitrary H
   with its endpoints is tested against the corresponding coherent square.
3. Its triangle assumption required all three faces to equal α. This can discard
   nontrivial loop commutations and does not specify the two square triangles.
   Replaced it by the exact left-triangle/α/right-triangle composition witness.
4. It omitted equivalence invariance for arbitrary coherent square diagrams and
   coherent-to-strict presentation comparison. Added the general functor-equivalence
   clause; its combination with recognition gives the latter comparison.
5. It added a standalone quasicategory conjunct not in this node's conclusion. Removed
   that redundant conjunct; the recorded quasicategory theorem remains a proof import.
6. The theorem docstring lacked all nine proof steps. Added the entire argument in
   order, including currying, arrow-model transport, two-out-of-three, the Δ[0]
   converse, whole-diagram invariance and strict zigzags. Imported every recorded
   available proof-dependency module. The point-family-q-counit node has no Lean
   record yet, so its proof import is omitted and its role remains in the docstring.
7. Added the already landed notion nodes for the exact existing spaces category,
   square cones and two canonical path comparisons to stmt_deps. No dependency
   interface was repaired and no new DAG node was needed. Traversing their statement
   and proof dependencies finds no path back to this item.

Edge cases: A,B,C,D and the test complexes may be empty or disconnected, and the
statement has no inhabitance assumption. For discrete complexes it is the ordinary
bijection criterion; D = point gives the product criterion. All simplicial degrees,
including degree zero and degeneracies, are retained by the existing nerve and the
full square map. An empty apex presents a cartesian square precisely when its path
pullback is empty. No variable index set is imposed: the indexing square is the
fixed finite cospan cone. No characteristic, ring, scheme or nonzero-object condition
occurs. The nerve lives in u+1 while each Kan complex lives in arbitrary u, with the
square shape instantiated in u+1; no extra universe equation is imposed.

A diagnostic example distinguishes the repair from the old statement: take B=C=point,
D=K(C₂,1), and A the discrete two-element Kan complex with all four boundary maps
constant. Its path pullback is equivalent to the discrete group C₂. A homotopy H
assigning the two loop classes bijectively makes q a weak equivalence, whereas the
constant homotopy does not. Thus H must be kept. An all-three-faces-equal triangle
would force its loop class to be idempotent and excludes the nontrivial loop.

Independent duplicate searches, using queries different from the first report:

* LeanFinder via `msearch.py NL lem-coef-kan-nerve-pullback-recognition leanfinder
  "homotopy coherent nerve Kan complexes cartesian limiting cone path pullback recognition"`:
  eight ordinary nerve/strict-Segal hits, no recognition theorem.
* Loogle via msearch, `SimplicialNerve`: zero hits; the service does not index that
  identifier. This limitation is recorded, rather than treated as positive evidence.
* LeanSearch via msearch, "A square in the homotopy coherent nerve of Kan complexes
  is a limiting cone exactly when its path comparison is a weak homotopy equivalence":
  eight ordinary IsPullback/Square/CommSq hits, not this enhanced statement.
* msearch grep `cartesian|homotopy.*pullback` in AlgebraicTopology: model-category
  right-homotopy and ordinary simplicial-set limit hits; no complete match.
* Direct rg in the named Mathlib, WeilConjectures and project trees for coherent
  square/cartesian/limiting-cone terminology found the exact square-cone primitives
  in SuspensionSquareComparison and the two canonical comparison maps in
  RelativeInfinityCone and InfinityHomotopyPullbackPasting. They are reused. The
  general InfinityTerminalPullbackCriterion concerns arbitrary quasicategories and
  incoming mapping spaces, not the Kan-nerve recognition of this item. The
  SpaceGeometricDescent Cartesian predicate has another indexed category interface;
  IsDescentCartesianArrow is a curried-arrow interface. We use the existing square
  cones directly, with no second cartesian predicate. SimplicialModelCoherentDiagrams
  has a different model-category interface and depends on this item. The coordinate
  helpers and recognition declaration have no existing full-name matches.

H5/H6/H8/H9: the only postponed proof is the named item theorem, ending in `sorry`.
All six coordinate/presentation helpers have real data and source/blueprint docstrings;
there is no choice from a bare existence theorem, no local notation/instance, and no
private definition. Every variable and universe is bound (`autoImplicit false`).
All lines are at most 100 characters. The node's lean.declarations lists the six
helpers and the theorem; lean.statement was extracted from the exact file by the
project's signature reader. `scompile.py` compiled the repaired file cleanly, both
as sandbox and canonical library module, with no warnings. No global build was run.
