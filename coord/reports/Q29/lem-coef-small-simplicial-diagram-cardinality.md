## Worker report

The module `Sheaf.AlgebraicTopology.SmallSimplicialDiagramCardinality` states
`SSet.Presentability.small_simplicial_diagram_cardinality`, with `sorry` as its only
proof. It introduces no new definitions. The node is unchanged outside `lean`.
There is no statement dispute or correction and no dependency repair.

Source read: [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), Lemma
the project server, successor-stage construction on printed p. 433 (PDF page 451, one-based),
and the sharpness notation in Section 5.4.2. In that application the target family
is indexed by vertices and the maps land in the corresponding slice pullbacks.
The node abstracts the cardinal estimate to an arbitrary small family of targets.
Its seven-step finite-record proof is reproduced in the theorem docstring.

Hypotheses and clauses, in the order of the node:

- The node's simplicial sets and maps are Mathlib `SSet.{u}` and categorical
  morphisms `K ⟶ B v`, i.e. natural transformations of the simplex presheaves.
  No quasicategory or fibrancy hypothesis is imposed.
- The node's `λ` is named `ρ`, since `λ` is reserved Lean syntax. Both cardinals
  have explicitly bound universe `u`. `hρ : ρ.IsRegular` and `hκ : κ.IsRegular`
  include infinitude, as specified by Mathlib's definition of regularity.
- `hρκ : ρ < κ` renders `λ < κ`; `huncountable : Cardinal.aleph0 < κ` renders
  uncountability. There is no stronger inaccessible-cardinal assumption.
- `hexp : ∀ μ ν : Cardinal.{u}, μ < κ → ν < ρ → μ ^ ν < κ` is exactly the
  stated exponent inequality, including zero and finite exponents.
- `V : Type u`, `hV : HasCardinalLT V κ`, and `B : V → SSet.{u}` give the
  target-index set, its strict cardinal bound, and its family. `hB` requires
  `IsKappaSmall κ (B v)` for every `v`, counting nondegenerate simplices only.
- Representative triples are given by `R : V → Type u`, shapes
  `A : ∀ v, R v → SSet.{u}`, and maps `φ v r : A v r ⟶ B v`.
  Their full index set is the disjoint union `Σ v : V, R v`.
  `HasCardinalLT (Σ v : V, R v) κ` is the required `|R| < κ`.
- `(∀ v r, IsKappaSmall ρ (A v r))` ensures that every representative really
  belongs to the specified class of triples.
- For every fixed `v`, arbitrary `ρ`-small shape `K`, and arbitrary map
  `f : K ⟶ B v`, the conclusion
  `∃! r : R v, ∃ e : K ≅ A v r, e.hom ≫ φ v r = f`
  supplies a representative and excludes duplicate isomorphism classes. The
  target index is fixed by its binder. The triangle equation is exactly
  `φ' h = φ` in categorical composition order. Uniqueness concerns `r`, not
  the isomorphism `e`: automorphisms are fully allowed. Conversely, applying
  this unique-index clause to a representative itself rules out two distinct
  representatives of its class. Thus this indexed formulation is equivalent
  to a set containing one representative per stipulated isomorphism class.
- The fourth conjunction is `IsKappaSmall κ (∐ fun r : Σ v, R v ↦ A r.1 r.2)`.
  The fifth applies the same predicate to the coproduct of
  `Enhanced.rightJoinCone (A r.1 r.2)`. These are exactly the two requested
  coproducts. Simplicial coproducts are computed degreewise; Mathlib's functor
  category colimit and evaluation-preservation instances provide that meaning.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read the module's simplicial
  primitive convention and its complete `coneCategory` declaration/docstring.
  Simplicial sets and maps are reused from the Mathlib primitives imported by
  this recorded module. Its coherent comma cones are not substituted for joins.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: read its join definitions and
  relative-predicate signatures; use `SSet.Enhanced.rightJoinCone`, the actual
  `orderedJoinFunctor.obj (K, Δ[0])`, with the new vertex last.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: read its definitions and
  docstrings; use `SSet.Presentability.IsKappaSmall`, namely
  `HasCardinalLT (Σ n : ℕ, S.nonDegenerate n) κ`. The unrelated accessibility
  clauses and ambient-universe constraints are not additional hypotheses here.
- Proof dependencies that are Mathlib leaves are imported through
  `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate` and
  `Mathlib.SetTheory.Cardinal.Arithmetic`. Read `SSet.exists_nonDegenerate`,
  `SSet.unique_nonDegenerate_dim`, `SSet.unique_nonDegenerate_simplex`,
  `SSet.unique_nonDegenerate_map`, and `Cardinal.mk_list_le_max`, at the lines
  recorded in their nodes. These supply the nondegenerate normal form and
  finite-record count for the postponed proof. The simplicial-set definition
  leaf's Mathlib definitions were also read.

All objects use an arbitrary explicitly bound universe `u`, with `V`, the
representative indices and the degree sets in that universe and the cardinals
in `Cardinal.{u}`. This allows every set in the fixed universe, does not bound
the dimensions, and avoids a spurious cardinal-union or coproduct instance
assumption. `set_option autoImplicit false` enforces explicit variable binding.

Edge cases checked mathematically before drafting:

- Empty `V`: the dependent total representative index is empty and both
  coproducts are the empty simplicial set. The theorem requires no inhabitants.
- Empty shape: `K` is unrestricted, and isomorphic copies of the empty shape
  map to every target; their representative is included for each target index.
  Its right join cone is the single zero-simplex.
- Empty target: only empty shapes map to it. No nonemptiness is assumed for
  any target or representative shape.
- `ρ = aleph0`: the small shapes have finitely many nondegenerate simplices,
  with no uniform dimension bound. The hypothesis uses only exponents below
  `ρ`, not exponent `aleph0`. A point target therefore permits all finite
  shapes, as intended.
- Automorphisms of shapes do not violate the unique-index clause. A simplex's
  image can be degenerate, since `φ` and the test map `f` are arbitrary.
- The cone test on the empty set, a vertex, and an edge gives respectively
  a vertex, an edge, and a two-simplex, so the right-cone orientation and size
  convention agree with the node.

Searches actually run using `msearch.py` for this item:

- LeanFinder: `Cardinal bound on isomorphism classes of lambda small simplicial
  sets mapping into kappa small simplicial sets`. Eight hits, including
  `CategoryTheory.SmallCategoryCardinalLT`,
  `CategoryTheory.ObjectProperty.HasCardinalLT`, and
  `CategoryTheory.SmallCategoryOfSet.exists_equivalence`. These concern ordinary
  category representatives or size of a supplied family, and do not state
  this simplicial-shape-and-map count.
- Loogle: `"SSet", "Cardinal"`. Three hits: the finite-presentability epi
  lemma and the two small-object-argument cardinal instances. Read the relevant
  `SimplicialSet/Presentable.lean` declarations: none bounds all small shapes
  and maps up to isomorphism.
- Grep: `cardinal|cardinality|HasCardinalLT`, restricted to
  `AlgebraicTopology/SimplicialSet`. Seventeen hits in horns, standard simplices,
  presentability and anodyne extensions; no statement matching this item.
- LeanSearch: `There are fewer than kappa isomorphism classes of lambda small
  simplicial sets with a map into a kappa small target, and their coproducts and
  join cones are kappa small`. Eight hits, mostly ordinary small-object-argument
  coproduct instances and the definition `SSet`. No matching assertion.
- Direct source search: `rg` for
  `small.*simplicial.*diagram|simplicial.*diagram.*cardinal|small_simplicial_diagram_cardinality`
  in upstream `WeilConjectures` and the project's `lean/Sheaf`, and an upstream
  `grep -rn` for the exact node id. Only unrelated small-diagram discussions
  were found; no match for the statement or exact node id.
- The proposed declaration and module names were also searched in Mathlib,
  upstream `WeilConjectures`, the project's Lean and `dag/lean_names_upstream.json`:
  no collision. There is no repair note for this item and no existing stage-2
  delivery; the delivery-log hit belongs to its stage-1 split by Q156.

Validation: `scompile.py Q29 lem-coef-small-simplicial-diagram-cardinality` compiled
this file cleanly, both the sandbox and final module-name checks. The initial
attempt found the reserved `λ` token; renaming it `ρ` repaired the sole error.
No theorem is proved; the sole postponed theorem is this DAG node.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
