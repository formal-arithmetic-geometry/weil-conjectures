## Worker report

The module `Sheaf.Algebra.Homology.GoodCoresolutionProductTotal` states Stacks Tag
09J0 exactly, on the explicitly constructed product total and its specified
augmentation. Its main declaration is
`CochainComplex.GoodCoresolution.augmentation_quasiIso`.
No statement correction, new node, or dependency repair is needed.

The earlier dispatch failure referred to the completed stage-1 split, not a
stage-2 declaration: the current node has `reviewed` by Q13, no `lean` or
`reviewed_lean`, and a stage-2 entry in `coord/queue.tsv`. No repair note exists.
This is the stage handoff described in brief-stage2 section 0.

Clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Size convention | Explicit `universe u`, arbitrary `AddCommGrpCat.{u}`; all complexes and groups live in this universe. The countable product stays in it. |
| Integer-indexed complexes of abelian groups, differential of degree one, square zero | `M : CochainComplex AddCommGrpCat.{u} ℤ`, `E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ`; these are Mathlib complexes with their actual differential and square-zero law. |
| The chain maps `u` and `f_i` | `u : M ⟶ E 0`, `f : ∀ i : ℕ, E i ⟶ E (i + 1)`; complex morphisms commute with the differentials. |
| Degreewise exact augmented row, including the initial zero | `h_inj` is injectivity of `u.f n`; `h₀` is exactness at `(E 0).X n`; `h i n` is exactness at `(E (i+1)).X n`, for every `i` and integer `n`. Together these are the whole infinite row. |
| Exact augmented differential-cokernel row, for every integer degree | `hc_inj`, `hc₀`, and `hc` are the same three conditions on `HomologicalComplex.opcyclesMap`; Mathlib's `opcycles` at `n` is the cokernel of the incoming differential, hence `V^n / d(V^{n-1})`. |
| `T^n = ∏_{i≥0} E_i^{n-i}` | `productTerm E n` is the actual dependent function group `AddCommGrpCat.of (∀ i : ℕ, (E i).X (n - (i : ℤ)))`; `productTotal` uses this very degree family in `CochainComplex.of`. |
| The first differential summand is zero at coordinate zero | `horizontalComponent E f n 0 = 0` by construction. At `i+1` it projects to coordinate `i`, applies `(f i).f (n-i)`, and transports along `n-i = n+1-(i+1)`. |
| Signed vertical differential | `productDifferential` adds `((-1 : ℤ)^i) • (projection ≫ (E i).d (n-i) (n+1-i))` to that horizontal component, then assembles the maps using `AddMonoidHom.pi`. |
| The product differential defines a complex | `productDifferential_comp`, followed by the explicit `productTotal`; the named proof obligation is the assertion of node proof step 1, not an additional assumption. |
| Augmentation `m ↦ (u(m),0,0,...)` | `augmentationCoordinate` is `u.f n` at zero, with the necessary degree equality, and zero at every successor; `augmentationComponent` uses the actual product map. |
| Augmentation is a chain map | `augmentationComponent_comm` states the second assertion of node proof step 1; `augmentation` uses `CochainComplex.ofHom` and that named theorem. |
| Quasi-isomorphism, meaning all cohomology maps are isomorphisms | `QuasiIso (augmentation M E u f h h₀)`, Mathlib's quasi-isomorphism predicate on this actual chain map. |
| No boundedness on the complexes | There are no boundedness, injectivity, projectivity, finite-support, or degree-vanishing assumptions. |

Dependency declarations and interfaces read:

- `def-weil-size-convention` is a convention node: its recorded `lean` has
  `convention: true`, with no module or declaration. Its note directs citers to
  bind their universes explicitly, as here.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex.of` and
  `CochainComplex.ofHom`, read with their signatures and documentation.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.opcycles`, `opcyclesMap`. The former is the right-homology
  cokernel of the incoming differential; the latter is the induced quotient map.
- `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`, which asserts a
  quasi-isomorphism in every degree, equivalently isomorphisms on homology.
- `Mathlib.Algebra.Category.Grp.Abelian`: `AddCommGrpCat`'s Abelian instance
  supplies homology for all these complexes without an extra assumption.
- `Mathlib.Algebra.Exact.Basic`: `Function.Exact` means the incoming image is
  the outgoing kernel. `Function.Injective` supplies exactness at the initial
  zero separately.
- `Mathlib.Algebra.Group.Pi.Lemmas`: `AddMonoidHom.pi` and
  `Pi.evalAddMonoidHom` are the actual product maps.

The sole proof dependency `lem-sfb-good-coresolution-cohomology-rows` currently
has neither a Lean record nor a Mathlib match, so there is no recorded module
to import. Its statement is read, cited in the main theorem's proof docstring,
and used only in the postponed proof, not to define an object or state the item.
The main docstring contains all six steps of the accepted DAG proof, including
the stabilization of every coordinate in the recursive boundary lift.

All ten declarations are listed in `lean.declarations`. The helpers introduce
only the product, differential, and augmentation explicitly specified by this
item. They are not separate independent notions. Every datum is an explicit
construction. Three proofs are postponed, all with this node's matching
blueprint tag and source plus a complete proof docstring:
`productDifferential_comp`, `augmentationComponent_comm`, and
`augmentation_quasiIso`. The first two are the two well-definedness assertions
of the item's accepted proof step 1. Definitions refer to these named proofs
only for their proof fields; none chooses data from an existence theorem.

Edge cases checked mathematically before writing:

- The zero coresolution gives the zero product and zero-complex isomorphism.
- If only column zero is nonzero, the differential is exactly `d` and the
  augmentation is the given degreewise isomorphism forced by exactness.
- Zero vertical differentials reduce the theorem to exact augmented rows:
  the horizontal cohomology is `M` at coordinate zero and vanishes thereafter.
- At coordinate zero there is no predecessor and no incoming horizontal map.
  At coordinate one the sign is negative, and `f_0 u=0` is precisely the
  nontrivial successor component of the chain-map identity.
- Arbitrarily negative vertical degrees occur in the dependent product;
  no finite-support condition replaces the product. Integer degrees, including
  zero and negative values, are quantified without restriction.
- The differential-cokernel row includes injectivity at `M`, not just
  exactness starting at `E_0`. No initial or tail term is omitted.

Searches for an existing statement or construction:

1. `msearch.py ... leanfinder` with query
   `An exact coresolution of unbounded cochain complexes exact on differential cokernels has a quasi-isomorphic product total complex`:
   eight hits. The closest, `CochainComplex.cm5b.instQuasiIsoIntP`, is the
   projection from a mapping-cone factorization. I read CM5b.lean, including
   its `I`, `p`, and `i`; it has neither these rows nor this product total.
2. `msearch.py ... loogle '"total", "quasiIso"'`: no hits.
3. `msearch.py ... grep 'good.*resolution|product.*total|total.*quasiIso' Algebra/Homology`:
   no hits. Mathlib `HomologicalComplex₂.total` uses coproduct totalization;
   it is not this unbounded product.
4. `msearch.py ... leansearch` with query
   `An exact augmented coresolution of unbounded cochain complexes which is exact on differential cokernels gives a quasi isomorphism to the product totalization`:
   eight hits about ordinary injective/projective resolutions, short complexes,
   augmenting a nonnegative complex, or mapping cones; no matching theorem.
5. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
   `good.*resolution|product.*total|total.*quasiIso`: read the relevant
   `WeilConjectures.AlgebraicGeometry.DerivedTotalResolutionQuasiIso` theorem;
   this is the Tag 09IZ direct-sum resolution with exact kernel rows, the dual
   construction, not Tag 09J0. The internal-Hom product totals concern Hom
   bicomplexes rather than an arbitrary sequence of complexes.
6. `grep -rn 'lem-sfb-good-coresolution-product-total' lean/WeilConjectures`:
   no hits. Searches of both project roots and Mathlib for this namespace and
   the new helper names found no collisions; other namespaces' augmentation
   names refer to different objects.

Validation: `scompile.py Q113 lem-sfb-good-coresolution-product-total` compiles
both the sandbox and its actual library module successfully, with no warning
or error (12.5 seconds and 8.0 seconds respectively). All compiles used this
wrapper. No live file was edited and no direct Git command was run.

No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q113

This is the worker's explicit rereading for the maintainer's independent review;
no separate agent was started, as the dispatch prohibits it. Reopened the node,
Stacks Tag 09J0, and the final Lean module. The exactness assumptions split into
three predicates per augmented row, preserving both initial injectivity and
all successor positions. In particular, `opcyclesMap` at `n` uses the incoming
differential, so its indexing agrees with `V^n/d(V^{n-1})` rather than the outgoing
cokernel indexed by `n+1`. The displayed total differential agrees with the
node coordinate by coordinate: `f_{i-1}` has coefficient one, `d_{E_i}` has
coefficient `(-1)^i`, and coordinate zero has only its vertical term.
The canonical augmentation has only its specified coordinate zero nonzero,
and the conclusion refers to that map, not an arbitrary quasi-isomorphism.
There is no boundedness restriction. During compiler repair I made the product
term reducible and split the dependent augmentation into its coordinate maps;
these changes only make the explicit construction elaborate. All arithmetic
casts express equal integer degrees. No node field outside `lean` changed.
