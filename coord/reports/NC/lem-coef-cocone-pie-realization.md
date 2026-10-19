## Worker report

The module `Sheaf.CategoryTheory.CoconePieRealization` states
`CategoryTheory.Limits.CoconePIE.cocone_pie_realization` with its sole theorem proof
`sorry`. It gives the specified natural transformations and identifies their full
equifier with Mathlib's category of cocones. The definitions in the same module
are the particular functors and canonical comparison introduced in this node;
all have explicit data. No node statement, dependency list, or proof plan changes.

All names below other than Mathlib names are in
`CategoryTheory.Limits.CoconePIE`.

| Natural-language hypothesis or clause | Lean rendering |
| --- | --- |
| A universe U | `universe w u`, with `w` representing U and the separate `u` allowing larger object collections. |
| A category A with U-small Homs | `{A : Type u} [Category.{w} A]`. |
| A U-small category J | `{J : Type w} [SmallCategory J]`; both objects and arrows are in U. |
| A diagram D : J → A | `(D : J ⥤ A)`. |
| B is the product over objects j of J | The existing pointwise product category on `J → A`, from `Mathlib.CategoryTheory.Pi.Basic`. |
| F is constant at the family D(j) | `constantFamily D := (Functor.const A).obj D.obj`. |
| G is the diagonal | `diagonal J A := Functor.pi' (fun _ : J ↦ 𝟭 A)`. |
| I is Ins(F,G) | The recorded `CategoryTheory.Inserter (constantFamily D) (diagonal J A)`. Its `obj` is the vertex and `hom j` is the leg from `D.obj j` to that vertex. |
| V is the vertex projection | The recorded `Inserter.forget (constantFamily D) (diagonal J A)`. |
| B' is the product over all arrows of J | The product category on `Arrow J → A`. An `Arrow J` is precisely a domain, codomain, and morphism; its square morphisms are not used for this product index. |
| H is constant at the domain-indexed family D(dom a) | `arrowSources D`, with value `fun a : Arrow J ↦ D.obj a.left`. |
| K is the diagonal of V | `arrowVertices D := Inserter.forget ... ⋙ diagonal (Arrow J) A`. |
| Natural transformations α, β : H ⇒ K exist | `∃ α β : arrowSources D ⟶ arrowVertices D`. Their types include naturality. |
| α at (X,u),a is u_cod(a) composed with D(a) | `α.app X a = D.map a.hom ≫ X.hom a.right`. Lean composition is written left to right. |
| β at (X,u),a is u_dom(a) | `β.app X a = X.hom a.left`. Both equalities are required for every inserter object and every arrow. |
| The equifier is the full subcategory where α_X = β_X | `ObjectProperty.FullSubcategory (fun X : Inserter ... ↦ α.app X = β.app X)`. This tests equality of the entire arrow-indexed family, not a natural isomorphism or a selection of coordinates. |
| It is canonically the category Cocone(D) | An equivalence `e : ObjectProperty.FullSubcategory ... ≌ Cocone D`. |
| Objects have precisely the given vertex and compatible family of legs | `coconeToInserter D` maps `c` to `⟨c.pt, fun j ↦ c.ι.app j⟩`; the theorem requires `e.inverse ⋙ ObjectProperty.ι ... = coconeToInserter D`. Together with the two component formulas, the equifier condition is exactly `D.map a.hom ≫ u a.right = u a.left`. |
| Morphisms are the maps commuting with all legs | The category is full inside the recorded inserter. Its equation specializes to `u j ≫ h = v j`. The comparison functor sends a cocone morphism `f` to an inserter morphism with underlying `f.hom`, and the equality of functors requires the equivalence inverse to do exactly this as well. |

The normalization uses equality of the composite inverse functor with the explicit
comparison functor, so it specifies objects and maps without adding arbitrary
comparison data. The inverse is the evident inclusion of cocones as families of
legs; the forward equivalence reconstructs their naturality from the equifier
condition. This is the canonical identification requested in the node.

Dependency declarations read and used:

- `def-coef-inserter`: `Sheaf.CategoryTheory.Inserter`, declarations
  `CategoryTheory.Inserter`, `Inserter.Hom`, `Inserter.category`, and
  `Inserter.forget`. I read the structures, their full signatures, the direction
  `F.map f ≫ Y.hom = X.hom ≫ G.map f`, the category instance, and the forgetful
  functor with their docstrings. No specialization or interface repair is needed.
- `def-weil-pbc-category-colimit`: recorded module
  `Mathlib.CategoryTheory.Limits.HasLimits`, using its public
  `CategoryTheory.Limits.Cocone`, `Cocone.category`, and `CoconeMorphism` interface
  from `Mathlib.CategoryTheory.Limits.Cones`. I read the cocone and morphism
  structures and their category, and the recorded colimit/IsColimit interfaces
  in `HasLimits` and `IsLimit`. The theorem needs cocones and does not assume
  that the original diagram has a colimit.

The other APIs are Mathlib's pointwise product category, `Functor.const`,
`Functor.pi'`, `Arrow`, `ObjectProperty.FullSubcategory` and its inclusion `ι`,
and `Equivalence`. Their source declarations and docstrings were read. All
structural laws of the explicit comparison functor follow directly from the
existing cocone morphism equation, funext, and inserter morphism extensionality.
There is no additional postponed assertion or hidden choice of construction.

Edge cases checked by unfolding the definitions:

- Empty J: both `J` and `Arrow J` are empty index sets. Inserter legs and
  equifier equations are empty families. The vertices and all maps of A survive;
  `coconeToInserter` still preserves them exactly. No `Nonempty` hypothesis occurs.
- J terminal, with only the identity: the equality is
  `D.map (𝟙 j) ≫ u j = u j`, so it adds no condition and gives the coslice category.
- A parallel pair: the two indexed equalities give exactly the usual cocone
  compatibility for both parallel arrows, with no extra commutativity condition.
- Empty A: if D exists the construction still types, and imposes no artificial
  inhabitance or chosen vertex. For a nonempty J there simply is no such diagram.
- The object universe of A is independent of w. Indexing products, arrow
  families, and the inserter creates no equality between these universes.

Searches for existing declarations (LeanFinder, Loogle, grep, and source search
preceded the module; LeanSearch and further name checks completed the search):

- `msearch.py ... leanfinder` with query “The category of cocones of a diagram
  is the equifier of two natural transformations on the inserter of constant and
  diagonal functors”: 8 hits, including `Cocone.category`, `Cocone`,
  `Functor.cocones_obj`, and the `Cofork`/`Cotrident` conversions. None gives
  this arbitrary-diagram inserter/equifier realization.
- `msearch.py ... loogle` with query `"Cocone", "Inserter"`: 0 hits.
- `msearch.py ... grep` with query
  `cocone.*[Ee]quifier|[Ee]quifier.*cocone|[Ii]nserter` in `CategoryTheory`:
  0 hits in Mathlib.
- `msearch.py ... leansearch` with query “Cocones are the equifier of two
  natural transformations on the inserter of a constant functor and a diagonal
  functor”: 8 hits for `Cocone`, the cocones functors, their constructors, and
  `coconeOfCoconeCurry`; no matching theorem.
- `rg -n` of the same inserter/equifier pattern and the item id in upstream
  `WeilConjectures` and side `lean/Sheaf`: upstream has no match; side has the
  recorded inserter, the PIE closure theorem, and explanatory mentions in
  accessibility proofs, with no cocone realization declaration.
- Name checks in `dag/lean_names_upstream.json`, Mathlib category theory,
  upstream `WeilConjectures`, and `lean/Sheaf` found no declaration in the
  `CategoryTheory.Limits.CoconePIE` namespace and no `cocone_pie_realization`
  or `coconeToInserter`. Mathlib's binary `Functor.diag` and unrelated diagonal
  constructions do not give the object-indexed functor here; this module's
  `diagonal` is just the specified instance of the existing `Functor.pi'` API.

Validation: the prescribed `scompile.py NC lem-coef-cocone-pie-realization`
compiled this file, both as a sandbox module and at its library module path,
with no errors or warnings (1.5 s each). The first compile's unnecessary-simpa
style warning was repaired before the clean compile. No disputed statement,
missing dependency, new node, or statement correction was needed.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
