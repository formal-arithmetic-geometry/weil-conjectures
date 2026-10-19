## Worker report

The single new module `Sheaf.CategoryTheory.HammockInvertedArrowActions` states
`SSet.Hammock.hammock_inverted_arrow_actions`, with `sorry` as its entire proof.
No definitions, new nodes, dependency replacements, or statement corrections are needed.
The source read was Dwyer–Kan, *Calculating simplicial localizations*, Definition 2.1
(printed p.19) and Proposition 3.3 (printed p.21), at the node's Rochester PDF URL.
Proposition 3.3 gives exactly the two action weak equivalences for an arbitrary marked
arrow, without a free-factor or fractions hypothesis.

Hypothesis and clause correspondence:

- A small category `C` is `{C : Type u} [Category.{v} C]`, with both universes explicitly
  bound. Mapping simplicial sets live in `SSet.{max u v}`, exactly as in the recorded
  dependency, so neither objects nor morphisms are forced into a smaller universe.
- A wide subcategory is `(W : MorphismProperty C) [W.IsMultiplicative]`. In Mathlib
  `CategoryTheory/MorphismProperty/Composition.lean`, `IsMultiplicative` extends exactly
  `ContainsIdentities` and `IsStableUnderComposition`: it selects morphisms on all
  objects, contains every identity, and is closed under composition.
- The marked arrow is `{x y : C} (f : x ⟶ y) (hf : W f)`; `(z : C)` is the arbitrary
  object called `v` in the node (the name `v` is reserved for the morphism universe).
- The four mapping sets `H(z,x)`, `H(z,y)`, `H(y,z)`, `H(x,z)` are respectively
  `Pzx.H`, `Pzy.H`, `Pyz.H`, `Pxz.H`, for the four recorded `PresentationData` values.
  These parameters select models supplied by the dependency, not extra mathematical
  restrictions. The theorem works for every such choice; no existence or naturality
  hypothesis beyond that interface is added. That interface's `simplices` equivalences
  retain all reduced paths, and `rowOperators` specifies their actual simplicial operators.
- The first action is `post : Pzx.H ⟶ Pzy.H`. Its formula, for every `n` and input `s`,
  requires reduction from `(Pzx.simplices n s).val.comp (hammockActualPath W n f)`
  to the reduced path of `post.app _ s`. `Quiver.Path.comp` follows the first path
  and then the second, so this appends the forward arrow at the target endpoint.
- The second action is `pre : Pyz.H ⟶ Pxz.H`. Its formula requires reduction from
  `(hammockActualPath W n f).comp (Pyz.simplices n s).val`, so it prepends the forward
  arrow at the source endpoint. Both maps are simplicial maps, not degreewise functions.
- The conclusion is the conjunction `Enhanced.IsWeakHomotopyEquivalence post ∧
  Enhanced.IsWeakHomotopyEquivalence pre`. This existing predicate expands into the
  component bijection of geometric realization and a bijection on each based cubical
  homotopy group for every positive degree and every point. Postcomposition preserves
  the group operation, so the bijections give exactly the stated group isomorphisms.
- The existential quantifiers include full degreewise reduction formulas. They supply
  the induced maps even though the dependency exports mapping sets rather than named
  action maps. They do not replace the canonical action by an arbitrary equivalence.
  Terminal-reduct uniqueness from the dependency fixes each output path, and its
  `simplices` equivalence fixes each output simplex.
- There are no freeness, fractions, saturation, two-out-of-three, connectedness,
  nonemptiness, or local-Kan assumptions.

Declarations read and used:

- `Sheaf.CategoryTheory.HammockGraphColimitPresentation`:
  `SSet.Hammock.PresentationData`, its fields `H`, `simplices`, and `rowOperators`,
  and `hammock_graph_colimit_presentation` (existence of the specified presentations).
  Its full theorem signature is `(T : MorphismProperty C) [T.IsMultiplicative]
  (x y : C) : ∃ P : PresentationData T x y, NaturalFor T P`.
- Its public dependency `Sheaf.CategoryTheory.HammockInfinityLocalization`:
  `CategoryTheory.hammockActualPath`, `HammockReduces`, `ReducedHammock`,
  `HammockChain`, `HammockStep`, and `hammockEndpoint`. `hammockActualPath` is the
  actual constant-chain forward column in each degree, not a chosen representative.
  The downstream infinity-localization theorem is not used.
- Its public dependency `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `componentsMap`, and `homotopyGroupMap`.
  Read their signatures, quotient constructions, and realization-based docstrings.
- Proof-only imports: `Sheaf.AlgebraicTopology.RealizationCylinder`
  (`SSet.realization_cylinder`, including ordinary-product and endpoint clauses), and
  `Sheaf.CategoryTheory.HomotopyEquivalenceWeak`
  (`SSet.Enhanced.homotopy_equivalence_weak`, allowing moving basepoints and empty spaces).
  Both node records and full declaration docstrings were read. The main docstring
  carries the item's five proof steps, including both cancellation diagrams and
  the distinct orientations of the four prisms.

Edge cases checked before writing:

- `f = 𝟙 x`: `hammockActualPath` is the identity column, which reduces to the empty
  path. Both formulas therefore describe the identity action after reduction.
- `x = y` with a nonidentity marked endomorphism: no distinctness assumption is used;
  the two cancellation edges still have the required commuting squares.
- Empty input mapping sets: universal formulas are vacuous there, but existence of
  the backward-arrow actions gives the corresponding inverse implications; the weak
  equivalence predicate has the component condition even without basepoints.
- An empty category: there are no endpoint/arrow/object choices, as in the source.
- Degree zero and arbitrary repeated rows are covered by `n : ℕ`, with no positivity
  condition. Only homotopy-group degrees, inside the existing weak predicate, start at 1.
- Minimal wide marking (identities only), non-saturated wide markings, and different
  object/morphism universes are all allowed by the binders and the chosen interface.

Searches actually run for this item:

- `msearch.py ... leanfinder` with query "Composition with an inverted arrow induces
  weak homotopy equivalences of reduced hammock mapping simplicial sets": eight
  model-category homotopy-class results, including `RightHomotopyClass.whitehead`
  and `RightHomotopyClass.precomp`; none has arbitrary reduced-hammock mapping sets.
- `msearch.py ... loogle '"hammock"'`: zero hits.
- `msearch.py ... grep 'hammock|Hammock'`: zero Mathlib hits.
- `msearch.py ... leansearch` with query "Marked arrows act by weak equivalences on
  hammock localization mapping spaces": eight hits about abstract weak equivalences,
  ordinary localization, or model-category homotopies; no exact match.
- Direct `rg` of the upstream `WeilConjectures` tree and the project's category theory
  and algebraic topology modules for hammock names and weak-equivalence uses found
  the recorded path/presentation interfaces and special model-category actions, but
  no theorem for arbitrary marked categories. A narrower search for hammock action,
  pre/post, and weak declarations confirmed this.
- Direct `rg` of `dag/lean_names_upstream.json` and upstream source for this node id,
  and `grep -rn` of upstream source for the id: no match.

No statement dispute or node fault was found. Compilation and the prescribed delivery
preflight are recorded below when complete; the independent second reader supplies
its own reading before delivery.

Validation: `scompile.py N5 lem-coef-hammock-inverted-arrow-actions` on the delivered
module passed both its sandbox and library-path checks (1.3 s each), with no errors
or warnings. The file has one theorem, no data definitions and no proofs beyond
its required `sorry`; its maximum line length is 92 characters.

## Second reading by N5

Independent second reading, 2026-10-17. I opened the node, its complete five-step
proof, the delivered module, the sole statement dependency's node and source module,
and the two proof-only dependency nodes and source modules. I read Dwyer--Kan,
*Calculating simplicial localizations*, Definition 2.1 (printed p.19), the standing
small-category convention in 1.2(iv), and Proposition 3.3 (printed p.21), from
[the source PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf).
There is no Stacks source for this item. Proposition 3.3 concerns arbitrary marked
arrows in a category with a wide subcategory; the free-factor assumption of the
preceding Proposition 3.2 does not carry into it.

Object, hypothesis, and conclusion inventory, with the matching Lean and verdict:

1. A small ordinary category C: `{C : Type u} [Category.{v} C]`. Both universes are
   declared explicitly, and the mapping simplicial sets in `PresentationData` live
   in `SSet.{max u v}`. Verdict: exact, with independent object/morphism sizes.
2. A wide subcategory W: `(W : MorphismProperty C) [W.IsMultiplicative]`.
   I opened Mathlib's `MorphismProperty/Composition.lean`: `IsMultiplicative`
   extends exactly `ContainsIdentities` and `IsStableUnderComposition`. This
   describes a subcategory containing all objects, with no requirement to contain
   all isomorphisms or to satisfy saturation/two-out-of-three. Verdict: exact.
3. Objects x,y and a marked arrow u: `{x y : C} (f : x ⟶ y) (hf : W f)`.
   The arbitrary test object v is `(z : C)`. Verdict: exact; the changed variable
   names only avoid a clash with the universe name v.
4. The reduced-hammock simplicial sets from the recorded graph-colimit
   presentation: `Pzx`, `Pzy`, `Pyz`, `Pxz : PresentationData ...`, respectively
   for `(z,x)`, `(z,y)`, `(y,z)`, `(x,z)`. I read the complete structure signature,
   especially `H`, `simplices : ∀ q, H _⦋q⦌ ≃ ReducedHammock ... q`, and
   `rowOperators`. I also opened the actual `HammockChain`, `HammockStep`,
   `hammockEndpoint`, `HammockReduction`, `HammockReduces`, `ReducedHammock`,
   `hammockRows`, and `hammockActualPath` definitions in the public dependency
   `HammockInfinityLocalization`. These retain downward marked vertical arrows,
   constant identity endpoint chains, uniform column directions, marked leftward
   arrows, and exactly deletion of identity columns/composition of like directions.
   The reduced subtype is irreducibility for those operations. Verdict: the same
   objects, not ordinary-localization Hom sets or a fibrant replacement.
   The four presentation parameters allow models of the four specified mapping
   sets. They add no restriction: the dependency theorem supplies a presentation
   at each pair, and the degreewise equivalences plus reduction row operators
   identify every such model with the same reduced-hammock simplicial set.
   No `NaturalFor` hypothesis is needed for this fixed-pair action assertion.
5. Target composition H(z,x) → H(z,y): the existential simplicial map
   `post : Pzx.H ⟶ Pzy.H` and the first universally quantified reduction formula.
   It appends `hammockActualPath W n f` to the input path. I opened Mathlib's
   `Quiver.Path.comp` definition: `p.comp q` traverses p, then q. Verdict: correct
   direction and correct arrow, in every degree, with actual reduction.
6. Source composition H(y,z) → H(x,z): `pre : Pyz.H ⟶ Pxz.H` and the second
   reduction formula. It prepends `hammockActualPath W n f` to the input path.
   Verdict: correct direction and same forward marked arrow, not its reverse.
7. Both induced maps are weak homotopy equivalences: the final two conjuncts
   `Enhanced.IsWeakHomotopyEquivalence post` and
   `Enhanced.IsWeakHomotopyEquivalence pre`. I opened the predicate and its
   `componentsMap` and `homotopyGroupMap` definitions in `EnhancedDiagramsCones`.
   It requires a realization path-component bijection and, for every positive
   degree and every point of the source realization, bijectivity on based cubical
   homotopy classes. Postcomposition respects concatenation, so this is the
   specified group-isomorphism condition. Verdict: exact, including all basepoints.
8. No freeness or calculus-of-fractions assumption: no such binder, nor local Kan,
   connectedness, nonemptiness, saturation, or extra marking condition, occurs.
   Verdict: exact. All objects and hypotheses precede the existential action maps;
   the degreewise formulas specify their values, rather than permitting arbitrary
   weak equivalences with the same endpoints. Uniqueness of terminal reduction and
   the `simplices` equivalences determine these values. Existence with these formulas
   is the statement that concatenation induces the two canonical simplicial maps.

Edge cases: an empty C admits no x,y,f,z, exactly as in the source. Empty mapping
simplicial sets are permitted, and the component-bijection conjunct remains present
when there are no basepoints. The identity arrow reduces to the empty column path;
under each presentation equivalence the asserted action is the identity action.
Equal endpoints and nonidentity marked endomorphisms are allowed. Degree zero and
all repeated-row degeneracies are covered by unrestricted `n : ℕ`; only homotopy-group
degrees are positive. The minimal identity-only marking and nonsaturated
wide markings are allowed. There is no ring, characteristic, scheme, coefficient,
zero-object assumption, or independent indexing set to restrict. Both u < v and
v < u are covered by the mapping universe `max u v`.

Independent duplicate searches actually run:

- LeanFinder: "Precomposition and postcomposition by a marked morphism are weak
  homotopy equivalences of Dwyer Kan mapping spaces". Eight hits, including
  `RightHomotopyClass.precomp_bijective_of_weakEquivalence` and
  `LeftHomotopyClass.postcomp_bijective_of_weakEquivalence`. I opened these in
  Mathlib `AlgebraicTopology/ModelCategory/Homotopy.lean`: they concern bijections
  of homotopy classes under model-category and fibrancy/cofibrancy hypotheses,
  not weak equivalences of these hammock mapping simplicial sets.
- Loogle: `"hammock"`, zero hits.
- LeanSearch: "A distinguished morphism acts invertibly up to homotopy on the
  simplicial sets of reduced zigzags". Eight hits about relative simplicial
  homotopies and truncated homotopy categories; none states this result.
- Search-wrapper grep: `reduced.*zigzag|marked.*composition.*equivalence|hammock`,
  zero hits. Direct independent `rg` with these terms over the upstream
  `WeilConjectures` and Mathlib trees found no match. Direct searches of the
  project's category-theory/algebraic-topology modules and upstream-name census
  found the recorded hammock constructions and special applications, not this
  theorem. I opened `SimplicialPullbackEquivalence`: its theorem characterizes
  invertibility in a strict pullback, not the present action assertion.

No mathematical mismatch was found; no Lean, node statement, definition, dependency,
proof plan, or signature was changed. There are no new definition nodes or dependency
modules to audit. The sandbox's older node copy lacks the current base's `lean_audit`
metadata; the prescribed delivery wrapper preserves that base field and takes only
our authorized Lean record. No statement correction or citer audit is required.

The two proof-only imports were checked against their nodes: `realization_cylinder`
is the canonical ordinary-product homeomorphism with both endpoint identities;
`homotopy_equivalence_weak` allows moving basepoints and empty spaces. The theorem's
docstring reproduces all five proof steps, both cancellation grids, the endpoint
orientations of all four prisms, continuous time reversal, and the realization
conclusion. Module/declaration docstrings cite the source and blueprint id. There
is one public named theorem with `sorry` as its whole proof, no new data or private
notions, no file-local notation or instances, and no hidden `let`/`show` in its
signature. All variables/universes are bound. Maximum line width is 92. The node's
`lean.statement` equals the complete source signature with whitespace normalized.

Validation: I ran the prescribed `scompile.py N5
lem-coef-hammock-inverted-arrow-actions
lean/Sheaf/CategoryTheory/HammockInvertedArrowActions.lean`; sandbox and library-path
checks both passed (1.2 seconds each), with no warnings or errors. Second reading
changed only this report; the checked mathematical statement is retained verbatim.
