## Worker report

Item: lem-a1-space-monic-diagonal-tests. The new module
`Sheaf.AlgebraicGeometry.SpaceMonicDiagonalTests` states
`AlgebraicGeometry.AlgebraicSpace.space_monic_diagonal_tests`, with its proof `sorry`.
It also constructs the three canonical maps used in the statement:
`monicDiagonalPairMap`, `monicDiagonalTestMap`, and `diagonalTestRestriction`.
These use Mathlib's `pullback.map`; they introduce no second definition of a
fibre product, representability, algebraic space, or closed immersion. All their
data are explicit; their proof fields only check the defining commutative squares.
No new nodes, dependency repairs, or statement corrections are needed. The item
copy differs from the repository only in `lean`.

Hypotheses and clauses, with the node and Lean file read together:

- `S : Scheme.{u}` is the base scheme. `T B : Over S` are precisely the two
  schemes over S, and `b : B ⟶ T` includes the required compatibility over S.
- `X Y : AlgebraicSpace S` uses the recorded full subcategory of fppf sheaves;
  `X.obj.obj` and `Y.obj.obj` are their underlying presheaves. Natural
  transformations between these are exactly the sheaf morphisms.
- `f : X.obj.obj ⟶ yoneda.obj T` is the given map to h_T.
  `Limits.pullback f (yoneda.map b)` is X_B. Presheaf pullbacks of sheaves
  compute sheaf fibre products, so this is the same compatible-pair construction,
  without choosing a different model or imposing extra structure.
- `j : Y.obj.obj ⟶ Limits.pullback f (yoneda.map b)` is the given map.
  `hj : ∀ E : Over S, Function.Injective (j.app (op E))` is injectivity on
  sections on every S-scheme, exactly the node's monomorphism assumption.
- The two composites named g and r in the node are written explicitly as
  `j ≫ pullback.snd f (yoneda.map b)` and
  `j ≫ pullback.fst f (yoneda.map b)`. They are not extra parameters or assumptions.
- `D : Over S` and the binder `d` quantify over every specified scheme test of
  `Y ×_(h_B) Y`. The two projections of d are the node's y_1 and y_2;
  the pullback condition gives their common B-component beta.
- `monicDiagonalPairMap f b j` sends a pair `(y_1,y_2)` to `(r(y_1),r(y_2))`.
  Its defining square follows from the X_B pullback condition. Thus
  `d ≫ monicDiagonalPairMap f b j` is precisely `(x_1,x_2)`, with no independent
  choice of that right-hand test.
- `monicDiagonalTestMap f b j d` has domain
  `h_D ×_(Y ×_(h_B) Y) Y` and codomain `h_D ×_(X ×_(h_T) X) X`, using
  `pullback.diagonal` for the two relative diagonals. Its definition is
  `pullback.map` with first component the identity of h_D and second component r.
  Hence it is the canonical `(u,y) ↦ (u,r(y))` map of the node's proof.
- `IsIso (monicDiagonalTestMap f b j d)` asserts that this particular canonical
  morphism is invertible, equivalently supplying the claimed canonical isomorphism.
  The following projection equation expresses that it is over h_D, an explicit
  clause of the node. This equation is not an additional geometric conclusion.
- The quantifiers `∀ (D' : Over S) (v : D' ⟶ D)` and the following commutative
  square assert naturality in every further scheme test. Both restriction maps
  are explicitly constructed by `diagonalTestRestriction`, using `yoneda.map v`
  on the test component and the identity on the other component. Naturality of
  the inverse follows from this equation and the asserted invertibility.
- The final implication uses the existing
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` on each relative
  diagonal. Unfolding that predicate says exactly: for every scheme test there
  is a scheme representing the pullback, with its projection to the test scheme
  a closed immersion. No stronger representability or finiteness condition is used.
- The stated identity case requires no exception: the base change is an algebraic
  space by `fibreProduct_isAlgebraicSpace`, and its identity is injective at every
  test. The chosen sheaf pullback and presheaf pullback are canonically identified
  by the inclusion of sheaves, which creates limits. Specializing Y to this
  base change and j to its identity gives the included case.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`; Over packages schemes with their structure maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`. The latter has witnesses
  U, p, q, a representing `IsPullback` square, and the property of p.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`, for closure
  under the chosen sheaf pullback, including the identity case. Its recorded
  universal property and the other recorded declarations' signatures and
  docstrings were read. The other covering clauses are not extra assumptions here.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the closed embedding plus surjective
  stalk-map predicate, used on the representing scheme projection.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`;
  `Mathlib.CategoryTheory.Limits.Shapes.Diagonal`: `pullback.diagonal`.
  The signatures, defining formulas, and docstrings were read.

Source checked directly in `literature/stacks-project/spaces-morphisms.tex`:
Tag 03KL, lemma-base-change-separated, lines 272--286, identifies the base-changed
diagonal; Tag 03KQ, lemma-composition-separated, lines 365--384, factors the
composite diagonal. The node's four-step monomorphism specialization is included
in the theorem docstring, with its dependencies and the explicit inverse formula.

Edge cases checked: empty D or Y; y_1=y_2; two sections becoming equal only after
restriction; j the identity; and X=h_T with r potentially nonmonic. Only j is
assumed injective. The common B-component is retained in the pair map and is
essential to the inverse argument. No nonempty, finite-type, separatedness,
universe-equality, or closed-diagonal hypothesis is imposed on the isomorphism
clause. The closed-diagonal hypothesis occurs only as the premise of the final
implication. The arbitrary scheme universe u agrees with the recorded algebraic
space convention, and every variable is explicitly bound (`autoImplicit false`).

Searches actually run for this item:

- msearch leanfinder: "A monomorphism into a base change gives naturally
  isomorphic scheme tests of the relative diagonals, preserving closed immersion
  tests". Eight hits, including scheme diagonal immersion, diagonal affine-property
  constructors, scheme separatedness, and stability under base change; none states
  the node's canonical monomorphism comparison with naturality and scheme-test
  representability consequence.
- msearch loogle: `"pullback", "diagonal", "mono"`. Two hits:
  `pullback.instIsSplitMonoDiagonal` and `pullback.instIsIsoDiagonalOfMono`.
  They concern the diagonal of a monomorphism itself, not this comparison.
- msearch grep in CategoryTheory/Limits/Shapes:
  `pullbackDiagonalMapIso|pullback_map_diagonal_isPullback|diagonal.*[Mm]ono`.
  Five hits in Diagonal.lean, including `pullbackDiagonalMapIso` and its two
  component maps. These supply related pullback identifications, not the whole
  arbitrary monomorphism statement or its closed-immersion consequence.
- msearch leansearch: "Natural diagonal scheme test isomorphism for a monomorphism
  into a base changed algebraic space". Eight hits on diagonals of monomorphisms,
  scheme separatedness, universal injectivity, and quasi-separatedness. No exact match.
- Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib, and
  `dag/lean_names_upstream.json` for the four proposed names found no declaration.
  Searches for `monicDiagonal`, `monic_diagonal`, `diagonalTests`, `diagonal_tests`,
  and closed-immersion representability predicates found related space modules,
  whose interfaces were inspected, but no exact statement. The item-id search of
  `lean/WeilConjectures` found no upstream declaration. No repair note names this item.

Validation: scompile.py compiled the module successfully in both sandbox mode and
its intended module path. An initial compile found namespace shadowing of the bare
word `pullback` by the algebraic-space module pullback; every categorical object is
now explicitly `Limits.pullback`. No mathematical statement changed in this repair.

## Second reading by Q109

A separate rereading by this dispatched worker (no other agents were started)
compared the complete JSON statement and four proof steps to the final Lean file.
I checked the two structure maps, the common B-component, the precise right-hand
test, both relative diagonals, the over-D equation, all further-test morphisms, and
the closed-immersion implication individually as matched above. In particular the
monomorphism is j into X_B, not r into X, and the final premise is not moved onto
the whole theorem. `IsIso` is applied to the explicitly constructed comparison,
so it cannot select an unrelated isomorphism. All auxiliary definitions have real
data; only the single theorem is postponed. The only changes after this rereading
were qualifying the shadowed categorical pullbacks, retaining direct imports of
the recorded dependency modules, and correcting a mechanically altered docstring
word. No mismatch requiring a node correction was found. The maintainer's
independent mathematical review remains the independent review of this delivery.
