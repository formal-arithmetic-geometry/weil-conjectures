## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinSmallExtensionEssential` states
`AlgebraicGeometry.ArtinDeformation.smallExtension_section_or_essential` with a
single `sorry` proof. Its docstring gives all four steps of the node's proof,
including the image/kernel argument for complete sources and why a section
precludes essentiality. The node is unchanged apart from its `lean` record.
No new nodes, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/formal-defos.tex`,
`lemma-essential-surjection` (Tag 06H0), statement and proof of (4). The source
states that a small extension fails to be essential exactly when it has a
section. The node additionally allows complete Noetherian local sources; its
explicit image/kernel proof works for these sources without a separate
factorization lemma.

Hypothesis and clause correspondence:

- The commutative Noetherian base is `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`.
- The field of finite type over R is `(k : Type u) [Field k] [Algebra R k]
  [Algebra.FiniteType R k]`. This is finite generation as an R-algebra, exactly
  the affine finite-type condition referred to by the node. It is not merely
  finite generation as a field extension.
- The marked Artinian local R-algebras are `{A B : TestCategory R k}`.
  `TestCategory` is the recorded full subcategory of augmented commutative
  R-algebras, whose augmentation is surjective with maximal kernel. This is
  equivalent to the specified residue-field R-isomorphism; its morphisms are
  R-algebra maps preserving that augmentation, hence local and inducing the
  identity on k. No new test category or arrow type is introduced here.
- The arrow and small-extension hypothesis are `(p : B ⟶ A)
  (hp : IsSmallExtension p)`. The recorded predicate includes surjectivity,
  nonzero principal kernel and annihilation by the maximal ideal of B.
  With the residue marking this is exactly a one-dimensional k-kernel.
- “Either p has a section in the test category” is the left disjunct
  `∃ s : A ⟶ B, s ≫ p = 𝟙 A`. The order of categorical composition is
  precisely p after s, so this is p s = id_A, with no additional section data.
- Essentiality is the first conjunct of the right disjunct:
  `∀ (D : TestCategory R k) (g : D ⟶ B),
  Function.Surjective ((map p).comp (map g)) → Function.Surjective (map g)`.
  The universal source and arrow are exactly those in the node, and `map`
  takes the underlying R-algebra map of the existing test-category arrow.
- The complete-source conclusion is the second conjunct:
  `∀ (D : CompleteLocalAlgebra R k) (g : LocalMap D B),
  Function.Surjective ((map p).comp g.hom) → Function.Surjective g.hom`.
  The recorded `CompleteLocalAlgebra` supplies a commutative R-algebra,
  locality, Noetherianity, maximal-ideal adic completeness and the specified
  residue-field R-isomorphism. The recorded `LocalMap` supplies an R-algebra
  homomorphism, `IsLocalHom` and pointwise preservation of that marking.
  This conjunct is inside the essential alternative, as required by “in the
  latter case.” No continuity or finite-type hypothesis on D is added.

Dependency declarations used, with their source signatures/docstrings read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the recorded
  declaration of `def-weil-pbc-noetherian-ring`.
- `Mathlib.Algebra.Field.Defs`: `Field`, the Mathlib match of `def-weil-field`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  read as the recorded geometric finite-type definition. Here the objects
  are algebras, so the actual binder is Mathlib's `Algebra.FiniteType` from
  `Mathlib.RingTheory.FiniteType`, its affine algebra formulation. No scheme
  morphism is involved in this statement.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`: `TestCategory`,
  `map`, `IsSmallExtension`, `CompleteLocalAlgebra`, and `LocalMap` in
  namespace `AlgebraicGeometry.ArtinDeformation`. Their full definitions
  and docstrings were read; these are the recorded declarations of
  `def-sfb-artin-deformation-test-category`.

The single public import of the recorded test-category module exposes the
Mathlib dependencies actually used. That module is also the sole proof
 dependency of the node, so no additional proof-only import is needed.
All variables and universe levels are explicit (`set_option autoImplicit false`).
The common universe u is the existing test-category size convention, not a
new restriction on any residue characteristic or algebraic hypothesis.

Edge cases checked before writing:

- For R = k, the projection k[epsilon] to k is a split small extension; the
  identity-on-k inclusion is an allowed section. Taking g to be that section
  shows essentiality fails, so the disjunction must retain its left branch.
- The unital Z-algebra map Z/p^2 to F_p has no section. The right alternative
  is the appropriate one; no separability or characteristic-zero condition
  was imposed.
- A zero kernel would allow an isomorphism, but is excluded by the recorded
  definition of a small extension, exactly as the source requires. The zero
  ring cannot have the marked residue field k.
- Artinian sources can themselves be complete; overlap of the two source
  clauses is allowed. Complete sources need not be Artinian, and are not
  replaced by arbitrary truncations in the statement.
- When p g is not onto, neither source clause demands surjectivity of g.
  Identity source maps and field-valued test objects remain allowed.

Searches for reuse:

- `msearch.py` LeanFinder, “A small extension of Artinian local algebras is
  split or an essential surjection”: eight results on Artinian algebras and
  quasi-finiteness; no dichotomy or essentiality result.
- `msearch.py` Loogle, `IsArtinianRing, Function.Surjective`: two results,
  `Function.Surjective.isArtinianRing` and
  `IsArtinianRing.localization_surjective`; neither is this statement.
- `msearch.py` grep,
  `[Ee]ssential[Ss]urjection|[Ss]mall[Ee]xtension|[Ss]mall extension`:
  zero Mathlib hits.
- `msearch.py` LeanSearch, “A surjective local algebra map with one
  dimensional kernel is either split or essential”: eight results on linear
  splittings, formally etale/smooth algebras and surjective local maps;
  none states the node.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `essential.surjection|small.extension|IsSmallExtension`: the relevant
  definition is the dependency's `IsSmallExtension`; other hits concern
  smoothness/lifting or unrelated categorical extensions. No existing
  theorem states this dichotomy.
- Searches of `lean/WeilConjectures` and `dag/lean_names_upstream.json` for
  the item id, and of both Lean roots for
  `smallExtension.*essential|small_extension.*essential|smallExtension.*section`,
  returned no declaration of this theorem.

Validation: the delivered module is compiled with `scompile.py`; the prescribed
`deliver2.py --no-push` preflight and per-file compilation are run before the
final delivery. Only the expected warning that the theorem uses `sorry` is
permitted. No disputed statement or node fault was found.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
