## Worker report

The delivery states `SSet.rezk_diagonal_sharp` in
`Sheaf.AlgebraicTopology.RezkDiagonalSharp`. Its proof is `sorry`; the docstring
carries all nine proof steps from the DAG. It also supplies the genuine existing
prerequisite `lem-coef-sharp-pullback-calculus`, whose two predicates had no Lean
interface, in `Sheaf.AlgebraicTopology.SharpPullbackCalculus`. That module contains
real definitions `SSet.IsHomotopyCartesian`, `SSet.IsSharp`, and the entire
statement `SSet.sharp_pullback_calculus`, with a proof docstring and `sorry`.
There are exactly two postponed theorems, each attached to its existing DAG node.
No definition chooses data or depends on a postponed existence theorem.

The original item statement is unchanged. Its `stmt_deps` gains the existing
calculus node supplied in the same delivery, as authorized by the human update
requiring missing genuine prerequisites to be stated immediately. The calculus
node changes only in `lean`; its existing statement, proof fields and status
are preserved. No new DAG node and no statement correction are needed.

The source was opened online: [Rezk, Fibrations and Homotopy Colimits of
Simplicial Sheaves](https://rezk.web.illinois.edu/rezk-sharp-maps.pdf).
Section 2.3 (printed page 4) defines homotopy-cartesianness by factoring both
cospan legs over their original common base into weak equivalences followed by
fibrations. Proposition 2.7 gives universal homotopy-cartesianness as the sharpness
criterion. Theorem 6.1 (printed page 11) is precisely the item's diagonal result;
Section 6.7 (printed page 12) supplies the skeletal induction. This confirms the
node's source numbering; Proposition 2.2 alone concerns fibrations being sharp.

Clause-by-clause correspondence for the item:

- Small simplicial sets: `SSet.{u}`, with the arbitrary universe `u` explicitly
  declared. All diagrams and test maps remain in this universe.
- The realization weak equivalences of `def-cbc-enhanced-diagrams-cones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, used in the shared square predicate.
  This is the conjunction of bijectivity on realized path components and
  bijectivity on every positive based homotopy group, not categorical equivalence.
- The Kan--Quillen model structure: the prerequisite imports the recorded
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`; its scoped horn-defined
  `Fibration` is used in the square predicate. The model-existence theorem is
  not assumed as an additional parameter.
- A commutative homotopy-cartesian square:
  `IsHomotopyCartesian a b f g`. It existentially specifies weak-equivalence/
  fibration factorizations of both legs, followed by a weak equivalence `c`
  from the upper-left object into their strict pullback. The two equations
  `c ≫ pullback.fst = a ≫ i` and `c ≫ pullback.snd = b ≫ j` uniquely determine
  the canonical comparison. These equations imply the original square commutes.
  This is Rezk's Section 2.3 computation of the homotopy pullback, which in a
  right proper model category agrees with replacement of the whole diagram.
  It does not require the original objects or original base to be Kan.
- Sharpness: `IsSharp p` quantifies over every `T : SSet.{u}` and `t : T ⟶ B`
  and requires the strict pullback square with projections `pullback.fst p t`
  and `pullback.snd p t` to be homotopy cartesian. Testing the chosen categorical
  pullback tests every strict pullback square, since any other pullback is
  uniquely isomorphic to this one. There is no choice of an arbitrary map.
- Simplicial diagrams: `X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}`.
- The map of diagrams: `p : X ⟶ Y`, including its naturality data.
- Every row map sharp: `h_rows : ∀ m : SimplexCategoryᵒᵖ, IsSharp (p.app m)`.
  SimplexCategory objects range over precisely all finite standard ordinals.
- Every operator square homotopy cartesian:
  `h_squares : ∀ (m n : SimplexCategoryᵒᵖ) (a : m ⟶ n),
  IsHomotopyCartesian (X.map a) (p.app m) (p.app n) (Y.map a)`.
  An opposite arrow is exactly an operator in the source's stated direction;
  all faces, degeneracies, identities and composites are included.
- Actual diagonal: `Functor.uncurry.map p` is the bisimplicial map; whiskering it
  on the left by `Functor.diag SimplexCategoryᵒᵖ` applies the same operator in
  both directions. At `q` its component is `(p.app q).app q`, on objects
  `(X.obj q).obj q`. This is the formula `(diag Z)_q = (Z_q)_q`.
- Conclusion: `IsSharp (whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
  (Functor.uncurry.map p))` is precisely sharpness of that diagonal map.
- Absence of fibrancy restrictions: no `KanComplex`, `IsFibrant`, Reedy condition,
  nonemptiness, rowwise fibration, or diagram replacement is a theorem hypothesis.
  Fibrations occur only internally in the definition of homotopy pullback.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence` (including its definitions
  `componentsMap` and `homotopyGroupMap`); the recorded primary `coneCategory`
  and its docstring/signature were read. Only the realization weak-equivalence
  part of this large definition node is needed here.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` and `weakEquivalenceStructure`, with
  the scoped Kan-fibration instance from `SSet.modelCategoryQuillen`. The full
  theorem signature and docstring were read; right properness validates the
  non-fibrant homotopy-pullback computation. This dependency is publicly imported
  by the calculus module, which the main module publicly imports.
- `Sheaf.AlgebraicTopology.SharpPullbackCalculus`, supplied here:
  `SSet.IsSharp`, `SSet.IsHomotopyCartesian`, `SSet.sharp_pullback_calculus`.
- Mathlib `CategoryTheory.Functor.uncurry`, `Functor.diag`, `Functor.whiskerLeft`,
  categorical `pullback`, `pullback.map`, `pullback.lift`, `prod.map`.
- The proof-only dependency `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`
  is imported through `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`.
  Its Mathlib signatures were read: `SSet.exists_nonDegenerate`,
  `SSet.unique_nonDegenerate_dim`, `SSet.unique_nonDegenerate_simplex`,
  `SSet.unique_nonDegenerate_map`.
- The proof dependency `lem-coef-sharp-special-colimit-gluing` has neither `lean`
  nor `mathlib_match`; its full statement was read. No module can yet be imported
  for that proof-only prerequisite. Its use remains explicitly recorded in the
  nine-step proof docstring; no declaration from it is needed to type the item.

Searches (all Mathlib services used through the prescribed `msearch.py`, group Q24,
item `lem-coef-rezk-diagonal-sharp`):

- LeanFinder: `The diagonal of an equifibered bisimplicial map with sharp rows is
  sharp`: eight hits, including `SimplicialObject.diagonal` and simplex generator
  relations; none states diagonal sharpness. `SimplicialObject.diagonal` is the
  long-edge map to degree one, not the diagonal of a bisimplicial set.
- Loogle: `"SSet", "diagonal"`: five hits, involving topological diagonals and
  StrictSegal spine composition; no match.
- Mathlib grep: `sharp|bisimplicial|equifibered|homotopyCartesian` in
  `AlgebraicTopology`: zero hits.
- LeanFinder: `A sharp simplicial map universally preserves weak homotopy
  equivalences by pullback and is stable under base change`: eight hits about
  fibrations and trivial fibrations, with no sharp-map predicate or calculus.
- Loogle: `"HomotopicalAlgebra", "pullback"`: zero hits.
- LeanSearch: `Homotopy cartesian squares with sharp vertical maps compose and
  remain homotopy cartesian after taking products`: eight hits concerning
  ordinary commutative squares, products and fibrations; no match.
- `rg` of the upstream `WeilConjectures` tree and side `lean/Sheaf` for sharp-map,
  homotopy-cartesian and bisimplicial terminology, then exact `IsSharp` and
  `IsHomotopyCartesian`: no existing matching predicate or theorem. Marked
  simplicial sets' sharp marking is unrelated. Searching the item's blueprint
  identifier in upstream Lean found no existing theorem. Exact declaration-name
  searches also found no collision in `dag/lean_names_upstream.json` or Mathlib.
- The side library already uses the same uncurrying/diagonal construction in
  `SSet.BousfieldKan.diagonal` and in `bisimplicial_diagonal_equivalence`.
  The theorem uses the existing Mathlib construction directly, so introduces
  no second definition of diagonal and imports no unrelated Bousfield--Kan module.
- DAG searches found the existing calculus and special-gluing nodes; those
  notions are not replaced by invented helper nodes. A live source lookup for
  `Sheaf.AlgebraicTopology.SharpPullbackCalculus` confirmed no published module
  existed before supplying this prerequisite.

Edge cases checked before writing:

- Empty simplicial sets, empty bases and empty pullbacks are permitted; no
  `Nonempty` or inhabited-point binder occurs. Realization weak equivalence
  retains the path-component condition, so the empty object is not made
  weakly equivalent to a nonempty object by vacuous based-group conditions.
- Degree zero is included, and no horn-filling condition is mistakenly imposed
  in dimension zero. The sharpness test also includes the empty test object.
- Naturality covers every opposite simplex operator, including identity maps,
  both kinds of generators and all composites; directions in the four square
  arguments were checked against `p.naturality`.
- Neither non-Kan rows nor non-Kan diagonals are excluded. Rezk's two-leg
  replacement over the original base is valid in the right proper structure;
  there is no silent replacement of the diagonal in the conclusion.
- The two projection equations force a unique comparison by the pullback
  universal property, so the homotopy-cartesian predicate cannot be satisfied
  using a weak equivalence unrelated to the given cone. They also force
  commutativity of the original square, excluding noncommutative squares.
- All tests and replacements use `SSet.{u}`; no independent test universe can
  make universal sharpness vacuous. All variables and universes are explicit.

Both files compile cleanly through `scompile.py Q24 lem-coef-rezk-diagonal-sharp`,
separately in dependency order. No errors or non-sorry warnings remain. An initial
pullback comparison used the equality in the wrong direction; it was corrected
without changing the statement. A missing `Functor` namespace was also corrected.
No global build, direct Git operation, or edit to a read-only checkout was run.

## Dependency modules

`lem-coef-sharp-pullback-calculus`: its base `lean` and `mathlib_match` were both
absent. Its statement explicitly introduces sharp maps and homotopy-cartesian
squares, which the current item needs. Following the human's immediate-prerequisite
instruction, the delivery supplies that existing node's entire statement, rather
than a copy of its notions in the diagonal module. The dependency node changes
only in `lean`, whose `note` explains the missing interface.

The definition `IsHomotopyCartesian` and `IsSharp` render its introductory clauses
as described above. The eight conjuncts of `sharp_pullback_calculus E B p`, in order,
render every remaining clause:

1. `IsSharp p ↔ ∀ A A' a a' v w, IsWeakHomotopyEquivalence v → ...` is the
   universal weak-equivalence criterion over B; `w : v ≫ a' = a` is precisely
   the over-base condition. The output uses the canonical `pullback.map` with
   identity maps on E and B, hence is `E ×_B A → E ×_B A'`.
2. `IsSharp p → ∀ T t, IsSharp (pullback.snd p t)` is arbitrary base change.
3. `IsSharp p → ∀ K, IsSharp (prod.map p (𝟙 K))` is the product clause.
4. For a square with `w : a ≫ p = p' ≫ b` and `IsSharp p`, the equivalence
   between `IsHomotopyCartesian a p' p b` and weak equivalence of
   `pullback.lift a p' w` is the strict-pullback comparison criterion. Its
   target is E times_B B'; the node writes the canonically isomorphic order
   B' times_B E, which has the identical pair of projections after exchange.
5. With both `IsSharp p` and `IsSharp p'` and that square homotopy cartesian,
   for every `T` and `t : T ⟶ B'`, the conjunction says its canonical
   `E' ×_{B'} T → E ×_B T` comparison is a weak equivalence and the induced
   square to E over T to B is homotopy cartesian. Both formulations in the node
   are retained, including arbitrary T.
6. The quantified E'', E', E and B'', B', B, with three sharp vertical maps,
   two homotopy-cartesian input squares and the composites `a' ≫ a`, `b' ≫ b`,
   are horizontal pasting. Input predicates include their commutativity.
7. Products of the square with each arbitrary K use four `prod.map` maps,
   retaining both sharp vertical-map hypotheses as in 'such a square'.
8. For any K, L and `k : K ⟶ L`, the four specified product maps form the
   factor-changing square, and `IsSharp p` implies it is homotopy cartesian.

The calculus node has no proof steps in the DAG; its theorem docstring supplies
an explicit natural-language proof via Rezk Proposition 2.7, right properness,
strict-pullback comparison, iterated pullbacks and two-out-of-three. The theorem
itself remains entirely `sorry`, as required for stage 2.

## Second reading by Q24

I independently opened both sandbox modules, both delivered node records, the
repository versions of those nodes, all their statement dependencies and their
recorded declaration sources. There are no repair notes for either delivered
node. The mathematical source here is Rezk's paper, not a Stacks tag: I reopened
https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, Section 2 (printed pp. 3-4),
Theorem 6.1 (printed p. 11) and Section 6.7 (printed p. 12). Theorem 6.1 assumes
sharp components and homotopy-cartesian operator squares, exactly as this node
does. Its ambient simplicial-sheaf statement specializes to simplicial sets.
No standing Kan or Reedy hypothesis is present. Section 2.3 explicitly uses
weak-equivalence/fibration factorizations of both cospan legs over the original
base; Proposition 2.7 identifies universal homotopy-cartesianness with sharpness
in a right proper model category. Thus the existential two-leg computation in
this delivery also gives the node's fibrant-diagram computation, without adding
any original-corner fibrancy assumption or choosing a replacement.

The following is my object/hypothesis/conclusion checklist, with its Lean
rendering and verdict, rather than an inference from the declaration names.

1. Small simplicial sets in an arbitrary universe: `universe u`, `SSet.{u}`.
   All four corners, replacement objects, diagrams and tests use this same
   arbitrary universe. Correct; no independent smaller test universe.
2. Realization weak homotopy equivalences: the calculus uses the recorded
   `SSet.Enhanced.IsWeakHomotopyEquivalence`. I read its actual definition,
   `componentsMap`, and `homotopyGroupMap` in EnhancedDiagramsCones: bijection
   on path components of `SSet.toTop`, and bijection on the based groups for
   every positive natural degree and every source point. Correct notion.
3. Kan--Quillen fibrations and right properness: public import of the recorded
   KanQuillenRightProper module; `open scoped SSet.modelCategoryQuillen` fixes
   `Fibration` to horn lifting. I read `right_proper_kan_quillen`, including
   its equalities fixing the three model structures, its right-properness
   clause and its replacement-cone clause. No model or Kan instance is an
   extra input to the delivered theorem. Correct.
4. Commutative homotopy-cartesian squares: `IsHomotopyCartesian a b f g`
   specifies `i ≫ f' = f`, `j ≫ g' = g`, weak equivalences `i,j`, fibrations
   `f',g'`, and a weak equivalence `c` to their actual categorical pullback.
   Its projection equations `c ≫ pullback.fst = a ≫ i` and
   `c ≫ pullback.snd = b ≫ j` force the original commutativity by the pullback
   condition, and determine `c` uniquely. Correct; the existential map cannot
   ignore the given square. Rezk 2.3 is exactly this replacement criterion.
5. Sharpness: `IsSharp p` quantifies over every `T : SSet.{u}` and
   `t : T ⟶ B`, and tests the square with `pullback.fst p t` and
   `pullback.snd p t`. Correct: the chosen categorical pullback represents
   every strict pullback square up to its unique cone isomorphism.
6. Simplicial diagrams: `(X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u})`. Correct:
   no restriction on their objects or on the horizontal simplicial structure.
7. A natural transformation: `(p : X ⟶ Y)`. Correct: its naturality is data
   in this binder, not an omitted assumption or an arbitrary family of maps.
8. Every row is sharp: `h_rows : ∀ m : SimplexCategoryᵒᵖ, IsSharp (p.app m)`.
   Correct, including degree zero.
9. Every operator square is homotopy cartesian:
   `h_squares : ∀ (m n : SimplexCategoryᵒᵖ) (a : m ⟶ n),
   IsHomotopyCartesian (X.map a) (p.app m) (p.app n) (Y.map a)`.
   The corners are X_m, X_n, Y_m, Y_n, and naturality says
   `X.map a ≫ p.app n = p.app m ≫ Y.map a`. Renaming m,n identifies
   these with every source operator `[m] → [n]` in Delta. Correct direction,
   including faces, degeneracies, identities and composites.
10. Actual diagonal and its induced map: the conclusion is
    `IsSharp (whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.map p))`. I opened Mathlib's `uncurry`, `diag` and
    `whiskerLeft`: the degree-q object is `(X.obj q).obj q`, the component
    is `(p.app q).app q`, and each operator acts in both directions.
    Correct; no unrelated long-edge map or replaced diagonal.
11. Unrestricted conclusion: exactly sharpness of this map, with neither a
    Kan nor a Reedy nor a nonemptiness binder. Correct: no extra hypothesis
    or missing conclusion clause.

I separately checked the entire supplied dependency
`lem-coef-sharp-pullback-calculus` against its unchanged node, not merely the
predicates needed by the item. Its introductory square and sharp-map notions
are items 2-5 above. The eight conjuncts of `sharp_pullback_calculus E B p`
match, in order: the iff with preservation of every weak equivalence over B;
arbitrary base change; products with every K; the canonical strict-pullback
comparison iff under sharp p; both the comparison weak equivalence and induced
homotopy-cartesian square after every T-to-B' base change under both sharpness
hypotheses; horizontal pasting with three sharp vertical maps; products of such
squares; and the square induced by every factor map K-to-L. The `pullback.map`
and `pullback.lift` terms use the specified cone maps and commutation equations.
The switched order of the strict pullback's two factors is its canonical cone
isomorphism, not a change of assertion. Both base-change formulations in the
node are present. Verdict: the whole dependency statement is rendered, with
no extra corner fibrancy and no loss of the arbitrary-base-change quantifier.
The dependency's prior record and mathlib match are absent. Supplying this
existing node, rather than a new definition node or a private predicate, is
within the explicit immediate-prerequisite authorization. Its record changes
only in `lean` and explains this in `lean.note`.

Edge cases: empty diagrams of values (in particular X=Y=empty), empty bases,
empty test simplicial sets, and empty pullbacks remain allowed. The path-component
condition prevents vacuous positive homotopy groups from identifying empty and
nonempty realizations. Degree zero is included in both row and operator tests;
there is no positive-degree restriction on diagrams. All original corners may
be non-Kan. The square predicate enforces commutativity even though it does not
bind it separately. Arbitrary universe u is retained for every test and
replacement. Ring characteristic and empty-scheme cases are inapplicable here:
there are no rings or schemes among the objects or hidden instances.

Independent searches, using different wording from the worker:

- `msearch.py ... leanfinder "A universal homotopy pullback map of simplicial
  sets induces a universal homotopy pullback map on bisimplicial diagonals"`:
  eight hits, about Cech nerves, products and path objects; no sharpness theorem.
- `msearch.py ... loogle '"pullback", "WeakEquivalence"'`: zero hits.
- `msearch.py ... leansearch "Sharp maps of simplicial sets are universally
  homotopy cartesian and preserved by bisimplicial diagonals"`: eight hits,
  concerning simplicial naturality, horn fibrations and homotopy categories;
  no definition or statement matching either delivered node.
- `rg` over Mathlib, upstream WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for `IsHomotopyCartesian`, `IsSharp`,
  `homotopyCartesian`, `homotopy_cartesian`, `sharp_pullback_calculus`,
  `rezk_diagonal_sharp` and bisimplicial sharpness found no existing match.
  Broader searches for homotopy pullbacks, equifibred and bisimplicial language
  found nearby project material, which I inspected: `simplicialHomotopyPullback`
  is the unreplaced path model, and `kan_homotopy_pullback_invariance` requires
  all corners Kan. Neither defines this arbitrary-corner square predicate.
  `bisimplicial_diagonal_equivalence` asserts weak equivalence from rowwise
  weak equivalences, not universal homotopy-cartesianness from sharp rows.
  Mathlib's sharp marking and project sharp mapping objects are different
  notions. The existing uncurrying and diagonal constructions are reused.

I compared the nine proof steps in the node against the theorem docstring:
all are retained, including the degreewise skeleton pushout, the relative
cocone argument, the strengthened induction, the degeneracy/intersection
calculation, both attachment cocones, both span applications and the final
sequential union. The nondegenerate-decomposition import has the recorded four
Mathlib declarations; I opened their signatures. The special-gluing proof
prerequisite has no Lean module yet and is identified in the worker report;
no missing declaration from it is used to type this statement. There are no new
nodes. Both real predicate definitions have complete data; exactly the two
named theorems are postponed with `sorry`. Every declaration has its source
and owning blueprint id, and all Lean lines satisfy the 100-character limit.

Mismatches and changes: none found in the Lean or the node statements. I left
both modules and node signatures unchanged and appended this independent
reading only. Both `lean.statement` strings were checked literally against
their files; no unbound variable or universe occurs (`autoImplicit false`).
I recompiled both sibling files, separately through the required wrapper:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q24
lem-coef-rezk-diagonal-sharp
lean/Sheaf/AlgebraicTopology/SharpPullbackCalculus.lean
lean/Sheaf/AlgebraicTopology/RezkDiagonalSharp.lean`.
The private-overlay, preliminary, sandbox and library checks all passed, with
no errors or warnings. No direct git command or read-only-source edit was run.
