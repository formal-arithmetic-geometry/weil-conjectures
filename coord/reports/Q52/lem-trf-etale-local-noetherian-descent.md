## Worker report

The live DAG already contains the completed stage-2 statement for
`lem-trf-etale-local-noetherian-descent`, delivered by Q95. This packet records and
revalidates that declaration rather than introducing a second notion. The module is
`Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent`, and its declaration is
`AlgebraicGeometry.isLocallyNoetherian_of_etale_cover`.

The Lean theorem is:

```lean
theorem isLocallyNoetherian_of_etale_cover {T : Scheme.{u}} {A : Type v} (Tₐ : A → Scheme.{u}) (t : ∀ a, Tₐ a ⟶ T)
    [∀ a, Etale (t a)] [∀ a, IsLocallyNoetherian (Tₐ a)]
    (hcover : ∀ x : T, ∃ a : A, ∃ y : Tₐ a, t a y = x) : IsLocallyNoetherian T := by
  sorry
```

The hypothesis `T : Scheme.{u}` is rendered by Mathlib's `AlgebraicGeometry.Scheme`.
The indexing type `A : Type v` and family `Tₐ : A → Scheme.{u}` render an arbitrary
family of schemes over `T`; each map `t a : Tₐ a ⟶ T` is a `Scheme.Hom`. The instance
`[∀ a, Etale (t a)]` states that every map is etale. The instance
`[∀ a, IsLocallyNoetherian (Tₐ a)]` states that every covering scheme is locally
Noetherian. The pointwise clause
`hcover : ∀ x : T, ∃ a : A, ∃ y : Tₐ a, t a y = x` states joint surjectivity, with no
finiteness or nonemptiness hypothesis added. The conclusion is exactly
`IsLocallyNoetherian T`.

The proof is intentionally `sorry`, as required for stage 2. Its docstring records
all three source steps: restriction to affine opens and affine refinement, the
faithfully-flat finite-product ring descent, and the final affine-open-cover
criterion.

Dependencies used by the statement are:

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
* `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `AlgebraicGeometry.Scheme.Etale`.
  The node's Lean statement only needs the `Etale` morphism property represented by
  this Mathlib declaration and does not introduce a private site definition.
* `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (with its affine-open-cover
  characterization in `isLocallyNoetherian_iff_of_affine_openCover`).

I read the full recorded signatures and docstrings in the pinned Mathlib sources:
`Scheme.lean` defines schemes as locally ringed spaces with local affine charts;
`Sites/Etale.lean` defines `smallEtaleTopology` and the covering criterion
`ofArrows_mem_smallEtaleTopology_iff`; `Noetherian.lean` defines
`IsLocallyNoetherian` and its affine-cover equivalence.

Edge cases checked are an empty index type (the hypotheses then force the empty
scheme, so the implication has no hidden nonemptiness assumption), an empty target
scheme, and the identity singleton cover. The statement retains the arbitrary index
universe and all hypotheses from the node.

Searches for a duplicate declaration were made before retaining the existing module:
`msearch.py Q52 lem-trf-etale-local-noetherian-descent leanfinder "Local Noetherianity of schemes descends along surjective etale coverings"`
returned only locality results such as `IsLocallyNoetherian` and no etale-cover
descent theorem; `msearch.py ... loogle "IsLocallyNoetherian, Etale, Surjective"`
returned no hits; `msearch.py ... grep "IsLocallyNoetherian|Noetherian.*Etale|Etale.*Noetherian" Mathlib/AlgebraicGeometry`
found only the Noetherian locality file; and `rg` over `WeilConjectures` and
`lean/Sheaf` found this exact declaration only. Thus no second definition is added.

## Second reading by Q52

I opened the node and module. The scheme object, arbitrary family, morphisms,
etale instances, locally-Noetherian instances, pointwise joint-surjectivity clause,
and conclusion match the node hypothesis by hypothesis and clause by clause. The
module has one theorem, carries the source and blueprint docstrings, and has only the
expected stage-2 proof `sorry`. No statement correction or new node is needed.
