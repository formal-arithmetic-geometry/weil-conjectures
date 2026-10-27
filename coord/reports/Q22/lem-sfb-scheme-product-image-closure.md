## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeProductImageClosure` states
`AlgebraicGeometry.closure_range_pullback_map_over_field`, with its only proof
`sorry`. No definitions, helper nodes, dependency repairs, or statement changes
are needed.

Source read: `literature/stacks-project/varieties.tex`,
`lemma-closure-image-product-map` (Tag 04Q0), and its input
`lemma-closure-of-product` (Tag 047B). The first asserts precisely the equality
in this node; the second proves the density assertion using universally open
projections over a field. The module docstring gives all four proof steps of
the node, including the empty-image case.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`. The four schemes are
  `{A B X Y : Scheme.{u}}`. The universe is explicitly declared; all objects
  inhabit one category of schemes, with no extra smallness or finiteness bound.
- The four specified structure maps are `a`, `b`, `x`, and `y`, respectively,
  each with target `Spec (CommRingCat.of k)`.
- The two scheme morphisms are `(f : A ⟶ X)` and `(g : B ⟶ Y)`.
  Their compatibility with the structure maps is exactly
  `(hf : f ≫ x = a)` and `(hg : g ≫ y = b)`.
- The source product is `pullback a b`, the target product is `pullback x y`,
  and their induced morphism is `pullback.map a b x y f g (𝟙 _) ...`.
  The equality proofs use `hf.symm`, `hg.symm`, and the right identity law;
  the base map is the identity, not an arbitrary endomorphism of the spectrum.
- The closed subsets are `TopologicalSpace.Closeds.closure (Set.range f)`
  and `TopologicalSpace.Closeds.closure (Set.range g)`.
  For each, `(vanishingIdeal ...).subscheme` is the canonical reduced induced
  closed subscheme, with inclusion `(vanishingIdeal ...).subschemeι`.
  This is the construction characterized in the recorded dependency theorem;
  it does not use the scheme-theoretic image, which would require care about
  quasi-compactness or reducedness. The node's unspecified names `C_f`, `C_g`,
  `j_X`, `j_Y` are instantiated by these canonical constructions, rather than
  introducing arbitrary schemes or maps. The dependency's uniqueness clause
  identifies any other reduced induced closed subscheme over the same target
  with this one, preserving the image of the product inclusion.
- The induced structure maps on these two closed subschemes are their
  inclusions composed with `x` and `y`. The final `pullback.map` is exactly
  `j_X ×_k j_Y`, into the same `pullback x y` as the left side.
- The conclusion is an equality of point subsets: `closure (Set.range ...) =
  Set.range (...)`. `Set.range` expresses the image of the whole point space;
  `closure` uses the scheme's Zariski topology. There is no stronger equality
  of subschemes or ideals asserted.
- No quasi-compactness, finite-type, reducedness, separatedness, or nonemptiness
  hypothesis occurs.

Dependency declarations read and used:

- `def-weil-field`: `Field`,
  `Mathlib.Algebra.Field.Defs` (class signature and docstring).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (full structure signatures and docstrings).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`. The statement uses `Spec`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
  Read its complete signature and proof-plan docstring. Its construction is
  `Scheme.IdealSheafData.vanishingIdeal` followed by `.subscheme` and
  `.subschemeι`; the signature explicitly gives reducedness, closed immersion,
  range equal to the specified closed subset, and uniqueness over the target.
  These existing constructors are used directly, with no copied definition.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  `.lift`, `.map`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Read their complete signatures. `Mathlib.AlgebraicGeometry.Pullbacks`
  supplies the scheme pullback instances; its module is publicly imported.

The remaining stated proof dependencies are imported without `public`:
`Mathlib.AlgebraicGeometry.PullbackCarrier` for
`Scheme.Pullback.range_snd` and `Scheme.Pullback.range_map`;
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` for `IsClosedImmersion`;
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` for the recorded instance
of universally open morphisms to an integral one-point scheme; and
`Mathlib.AlgebraicGeometry.Fiber` for `Scheme.Hom.fiber`, `.fiberι`, and
`.fiberToSpecResidueField`. Their signatures were read. The node with the
pullback image formula and the universally-open node have Mathlib matches,
so no missing Lean record needs a replacement module.

Edge cases checked before writing:

- If either source is empty, its range and image closure are empty; the
  corresponding reduced closed subscheme and both product images are empty.
  The formula still gives equality, with no point choices required.
- Empty targets are allowed (their maps force the relevant source empty).
- If both maps are identities, the closed image subsets are the entire targets;
  the reduced closed structures may differ from the targets as schemes, but
  their product inclusion is surjective on points, as the conclusion requires.
- Nonreduced sources and targets are allowed: reducedness belongs only to the
  canonical closed subschemes on the right. No property of the original
  schemes is inferred from these reductions.
- All characteristics, imperfect fields, and non-finite-type/nonseparated
  schemes are included. The argument uses universal openness over a field,
  not a finite-presentation substitute.

Searches executed for an existing statement:

- `msearch.py leanfinder`, query: "For two scheme morphisms over a field the
  closure of the image of their product map is the image of the product of
  their reduced image closures". Eight hits included
  `Scheme.Pullback.range_map`, projection-range formulas, `Scheme.Hom.image`,
  `map_vanishingIdeal`, and `support_ker`; none states the closure equality.
  `support_ker` additionally has a quasi-compactness hypothesis.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.Scheme.Hom, CategoryTheory.Limits.pullback.map, closure`.
  Successful search, zero hits.
- `msearch.py grep`, query:
  `closure.*(prod|pullback)|(prod|pullback).*closure|IsDominant.*(prod|pullback)`,
  restricted to `AlgebraicGeometry`. Four hits in `Normalization.lean`, all
  integral-closure calculations, unrelated to this topological closure theorem.
- `msearch.py leansearch`, query: "For morphisms of schemes over a field the
  closure of the image of their fibre product map equals the product of their
  image closures". Eight hits included projection range formulas,
  `map_vanishingIdeal`, closed maps and closed immersions; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, for closure/product/pullback,
  dominant/product, the proposed declaration name, and the node id. Existing
  hits are unrelated closure calculations or the downstream proof-plan citation
  in `PerfectFieldGroupoidImageClosure.lean`; there is no statement of this
  result. The upstream name index likewise has no proposed-name collision.

Validation: `scompile.py Q22 lem-sfb-scheme-product-image-closure` compiled the
module both as a sandbox file and at its library module name, with no errors
or warnings. All variables and universes are explicitly bound. No statement
fault or dispute was found. The item node is unchanged except for `lean`.

No independent second reading was performed by this worker; as directed by the
current brief, the maintainer performs the independent delivery review.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
