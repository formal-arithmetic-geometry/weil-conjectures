## Worker report

The module `Sheaf.CategoryTheory.ReflectionInvertingLimitRestriction` states
`SSet.Enhanced.reflection_inverting_limit_restriction`. It imports the two recorded
statement dependencies and leaves the proof as `sorry`.

The Lean rendering of the statement is as follows.

- `J` and `C` are simplicial sets with `Quasicategory` instances, matching the small
  quasicategories in the node. `P : J _⦋0⦌ → Prop` and
  `fullSubcomplex J P` give the full subcategory (A\hookrightarrow J); its inclusion
  is `(fullSubcomplex J P).ι`.
- `Γ : J ⟶ C` is the coherent diagram.
- `a` chooses an object of the full subcategory for every `j : J _⦋0⦌`.
- `ua j` is the right-pinched mapping-space vertex from `j` to the chosen image
  `(fullSubcomplex J P).ι.app _ (a j)`, so it contains the endpoint equations for the
  reflection edge.
- `hpre` states that, for every `b` in the full subcategory, the map obtained by
  composing with `ua j` is a weak homotopy equivalence. Its first factor is the
  identity on `Map(ι(a j),ι(b))`, its second factor is the constant simplicial map
  at `ua j`, and the final factor is the chosen composition map
  `(Classical.choose (Classical.choose_spec (mapping_composition J)).2)`. This is the
  dependency's canonical mapping-space composition package and renders
  precomposition with the reflection edge.
- `R` is the cone restriction map from `coneCategory Γ` to the cone category of
  `((fullSubcomplex J P).ι ≫ Γ)`. `hR` pins it to the actual restriction on every
  simplicial degree and every coherent cone simplex: `(R.app n z).1.1 = z.1.1`
  fixes the apex, and `(R.app n z).1.2 = ...` precomposes the entire transformation
  (including all higher simplices) with the full-subcategory inclusion.
- The first conclusion clause is `IsFunctorEquivalence R`, i.e. a quasi-inverse and
  coherent natural equivalences in the internal functor simplicial sets.
- The second conclusion clause says for every cone `cone`,
  `IsLimiting Γ cone` iff its restricted cone `R.app _ cone` is limiting.
- The final clause is the existence equivalence for limiting cones on `J` and on
  `A`; it has no nonemptiness or target-limit hypothesis and therefore includes the
  empty-indexing case.

The statement dependencies used are:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.coneCategory`, `SSet.Enhanced.IsLimiting`,
  `SSet.Enhanced.IsFunctorEquivalence`, `SSet.Enhanced.mappingSpace`,
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, and `SSet.Enhanced.fullSubcomplex`.
- `Sheaf.CategoryTheory.InfinityMappingComposition`,
  `SSet.Enhanced.mapping_composition` and its selected composition package.

Edge cases checked against the node are: `J = ∅` (then `A = ∅`, the universal-arrow
hypothesis is vacuous, and the cone-existence equivalence is still meaningful),
`A = ∅` (the universal-arrow data force `J = ∅`), a one-object category, identity
reflection edges, and a diagram whose cone category has no limiting object. No target
limit or nonempty-indexing assumption is present.

Searches for an existing declaration were:

- `msearch.py ... leanfinder "Limits of a coherent quasicategory diagram that inverts reflection edges are computed on a full reflective subcategory"`: only ordinary reflective-category limit declarations (`CategoryTheory.hasLimit_of_reflective`, etc.); no coherent quasicategory result.
- `msearch.py ... loogle "CategoryTheory.Functor.Initial.conesEquiv_functor, CategoryTheory.Limits.IsLimit, Quasicategory"`: zero hits; `Quasicategory` is not a Loogle identifier in the ordinary-category query.
- `msearch.py ... grep "initial_of_adjunction|conesEquiv|reflective|coneCategory" CategoryTheory`: ordinary `Final.lean`/reflective-category hits only.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for the node id and the reflection-inverting cone statement: no existing declaration for this node or theorem.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

I reopened the target node, both dependency records, and the completed module. The
full-subcomplex predicate renders exactly a full subcategory and its inclusion; `ua`
has the source and target required of each reflection edge; `hpre` quantifies every
object of the reflective subcategory and uses the mapping-composition dependency in
the correct order. The `hR` equations retain the apex and the whole coherent
transformation, rather than only its vertices. The three conclusion clauses match,
respectively, equivalence of coherent cone categories, preservation/reflection of
limiting cones, and equivalence of existence of limiting cones. The empty cases are
not excluded. The file compiles cleanly with only the expected theorem `sorry`.

## Second reading by Q02

I reread the node statement, its source place, both statement dependencies, and the
complete Lean declaration. The node introduces the following data and clauses.

- `J` and `\\mathcal C` are small quasicategories in one fixed universe, `P` selects the
  full subcategory `A := fullSubcomplex J P`, and `\\iota` is its canonical inclusion.
  Lean renders these as `(J C : SSet.{u})` with quasicategory instances, `P`, and
  `(fullSubcomplex J P).ι`.
- `\\Gamma : J \\to \\mathcal C` is the coherent diagram. Lean renders it as
  `Γ : J ⟶ C`.
- Every `j` has a selected `a j : A` and an edge `u_j : j \\to \\iota(a j)`. Lean renders
  these as `a` and the degree-zero vertex `ua j` of the right-pinched
  `mappingSpace J j ((fullSubcomplex J P).ι.app _ (a j))`; its underlying edge is
  `(ua j).1`.
- The source requires that `Γ(u_j)` be an equivalence for every `j`. The original Lean
  omitted this hypothesis. I added
  `hΓ : ∀ j, IsEquivalenceEdge C (Γ.app _ (ua j).1)`, which is exactly the image edge
  under the simplicial map `Γ`.
- For every `b : A`, precomposition with `u_j` is a weak homotopy equivalence
  `Map_J(ι(a j),ι(b)) → Map_J(j,ι(b))`. Lean renders the identity/constant lift into
  the canonical mapping-composition map selected from `mapping_composition J`, under
  `hpre`; the two composition factors have the required order.
- `R` is restriction of the coherent cone category along `ι`, and `hR` states its
  apex and full transformation components. Lean renders the map between the two
  `coneCategory` simplicial sets and the two equations for every simplex degree.
- The conclusions are, in order, `IsFunctorEquivalence R`; the equivalence of
  `IsLimiting` for every cone and its restriction; and equivalence of existence of a
  limiting cone on `J` and on `A`. No target-limit or nonempty-index assumption is
  added, so the empty-index case remains included.

The only mismatch found was the missing `Γ(u_j)`-equivalence hypothesis (`H3`). I
repaired the Lean module and its node `lean.statement` by inserting `hΓ` between `ua`
and `hpre`; no other binder or conclusion changed. The added term compiles and has the
expected edge type because a degree-zero mapping-space simplex has underlying edge
`(ua j).1` and `Γ.app _` maps it into `C _⦋1⦌`.

I checked edge cases `J = ∅`, `A = ∅`, one-object and identity reflections, diagrams
with no limiting cone, and zero-dimensional/empty mapping spaces. The hypotheses do
not impose nonemptiness or a target limit; when `A` is empty, the selected `a j` data
forces `J` empty, as in the source. Universes are shared by `J`, `C`, and all mapping
spaces, so no case is excluded.

For duplicate searches I reran the LeanFinder, LeanSearch, Loogle, and `rg` searches
recorded by the worker, including ordinary reflective-category `Final.lean` results.
They find only ordinary-category limit/restriction lemmas and no coherent
quasicategory theorem or existing declaration for this node. The dependency
declarations are the recorded `SSet.Enhanced.coneCategory` family from
`Sheaf.CategoryTheory.EnhancedDiagramsCones` and
`SSet.Enhanced.mapping_composition` from
`Sheaf.CategoryTheory.InfinityMappingComposition`; both match the dependency nodes.

The repaired module compiles with `scompile.py`; only the expected theorem `sorry`
remains.
