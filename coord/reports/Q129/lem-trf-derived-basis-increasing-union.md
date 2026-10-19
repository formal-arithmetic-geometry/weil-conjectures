## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion` states
`AlgebraicGeometry.derived_basis_increasing_union`, with its whole proof `sorry`.
It also constructs `moduleOpenOverMapCompIso` and `derivedOpenOverMapCompIso`:
the sectionwise identity for two restrictions, and the induced derived comparison.
These are helpers for the cocycle of this node, with real data throughout.
No new independent notion, dependency repair, or statement correction is needed.

The source read is Stacks Project, `literature/stacks-project/cohomology.tex`,
Tag 0D6B, `lemma-glueing-increasing-union`, including its proof. The node's proof
already repairs the printed comparison direction and finite-case citation; the
Lean docstring carries this corrected proof, including the tail stalk argument.

Clause-by-clause rendering:

- A scheme X is `(X : Scheme.{u})` using Mathlib's scheme definition.
- A set-sized ordinal is `(o : Ordinal.{v})`, with indices `o.ToType`. This
  is a well-ordered representative of precisely o; v is independent of u and w.
  No nonemptiness, countability, or final-limit condition is imposed.
- The open family is `W : o.ToType → X.Opens`. The increasing condition is
  `hincreasing : Monotone W`, and the covering equation is `hcover : iSup W = ⊤`.
- At every non-successor the required equality is `hcontinuous`: if
  `Order.IsSuccPrelimit α`, then `W α = ⨆ β : Set.Iio α, W β.val`.
  This predicate includes the least element, so its empty predecessor union
  forces the first open to be empty. It also includes all nonzero limit indices.
- `K α` is in `DerivedCategory (SheafOfModules.{u}
  ((moduleRings X.toRingedSpace).over (W α)))`. This is D(O_Wα) on the
  localized site of opens. `Scheme.Modules.overEquiv (W α)` identifies its
  abelian category with modules on the open subscheme; the equivalence is
  additive and exact and therefore induces the same derived category. This is
  also the encoding used by `lem-trf-derived-basis-local-hom-glue`.
- The `HasDerivedCategory.{w}` binders for X and all its opens supply the shared
  localization models. They are infrastructure, with no boundedness,
  quasi-coherence, or extra geometry assumption on the given objects.
- Negative self Hom vanishing is exactly `hnegative : ∀ α i, i < 0 →
  Subsingleton (K α ⟶ (K α)⟦i⟧)`. These Hom sets are abelian groups, so
  subsingleton says their group is zero.
- Every specified transition is an isomorphism `r β α h`, from the image of
  `K α` under `(SheafOfModules.overMap ... (homOfLE ...)).mapDerivedCategory`
  to `K β`, for every strict `h : β < α`. The inclusion is obtained from
  the supplied monotonicity, rather than independently supplied maps.
- `hcocycle` composes the inverse of `derivedOpenOverMapCompIso` with the
  restriction of `(r β α hβα).hom` and then `(r γ β hγβ).hom`, and equates
  this with `(r γ α (lt_trans hγβ hβα)).hom`. Its direction is precisely
  r_γ^α = r_γ^β composed with the restriction of r_β^α. The initial
  comparison only identifies direct with iterated restriction. Its ordinary
  components are the identity, not an unconstrained comparison.
- The conclusion quantifies `∃ (L : schemeDerivedCategory X) (s : ∀ α, ... ≅ K α)`.
  Thus it gives a global derived object and every required restriction
  isomorphism, rather than bare local existence.
- The final equation first identifies direct restriction with iterated
  restriction by `SheafOfModules.openRestrictionComparison ... .inv.app L`,
  then restricts `(s α).hom` and composes with `(r β α h).hom`, obtaining
  `(s β).hom`. This is precisely the final compatibility in the node.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  category of morphisms (def-pc-scheme).
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, with its shared module carrier
  and `HasDerivedCategory` parameters (def-pc-derived-category). This source
  was read with `scompile.py --source`, as the older local source lacks it.
- `WeilConjectures.Algebra.Homology.OpenCoverAdjunctionTriangle`:
  `SheafOfModules.openRestrictionComparison` (lem-sc-open-cover-adjunction-triangle).
  The source was read with `scompile.py --source`; the same declaration is
  recorded by that already landed node. Its id was added to stmt_deps as
  authorized for existing landed interfaces. This constructs the global
  restriction comparison without duplicating it.
- Mathlib's `SheafOfModules.overFunctor`, `SheafOfModules.overMap`,
  `SheafOfModules.fullyFaithfulForget`, and `PresheafOfModules.isoMk`;
  `Scheme.Modules.overEquiv`; `CategoryTheory.Functor.mapDerivedCategory`;
  upstream `Functor.mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`.
  Their definitions/signatures and source documentation were read before use.
- All recorded proof dependencies with statements are imported: the
  universe-general ringed-site K-injective theorem, exact open restriction,
  K-injective restriction, exact-functor derivation, normalized extension by
  zero, stalkwise isomorphism detection, K-injective Hom bijectivity, module
  colimits, filtered-colimit stalks, exact module stalks, exact filtered
  abelian colimits, and derived basis local Hom gluing. Proof imports remain
  non-public, as required; no proof dependency was omitted for a cycle.

Edge cases checked mathematically before writing and against the final signature:

- o = 0: its index type is empty; hcover forces X empty and the conclusion
  asks for the zero global object with the empty isomorphism family.
- o = 1: continuity forces the sole open empty, so again X is empty.
- The least index of any nonempty o: `IsSuccPrelimit` holds there and the
  supremum over `Set.Iio` is the empty supremum, namely bottom.
- Nonzero limits: the supremum uses every earlier index; no predecessor is
  silently selected. Successor stages impose no continuity condition.
- Successor o: there is no requirement of continuity after the last index.
- Empty X, empty opens and repeated opens are allowed. Equal open sets at
  different indices still retain their prescribed transition isomorphisms.
- Negative integers are all included; zero and positive shifts are not required
  to vanish. The zero objects satisfy the hypothesis.
- No Nonempty index assumption or extra cohomological bounds occur. Independent
  universe v permits every set-sized ordinal, including a very large indexing
  family of repeated opens.

Searches for an existing statement (no exact match):

- msearch LeanFinder: "Glue compatible derived category objects along a continuous
  increasing ordinal open cover with vanishing negative self extensions":
  eight hits, all derived-category boundedness or complex representatives.
- msearch LeanSearch: "Transfinite gluing of compatible derived objects on
  increasing opens": eight hits, ordinary sheaf or topological gluing only.
- msearch Loogle: `"DerivedCategory", "glue"`: zero hits.
- msearch Mathlib grep, `BBD|[Dd]erived.*[Gg]lu|[Gg]lu.*[Dd]erived|transfinite`
  under `Mathlib/Algebra/Homology`: zero hits.
- Direct rg in upstream WeilConjectures, project Sheaf, and the upstream name
  inventory for `derived_basis_increasing_union|moduleOpenOverMapCompIso|
  derivedOpenOverMapCompIso|glueing.increasing.union`: no existing declaration.
  Searching the upstream source for this blueprint id also gave no hit.
- Searches of existing open-restriction comparisons found and reused
  `openRestrictionComparison`; `overFunctorMap` supplies its ordinary input.
  No composition comparison for two `overMap` functors was present, so the
  two small canonical helper definitions are supplied in this owning module.

No STATEMENT-DISPUTED flag or natural-language node fault remains.

Validation: the prescribed `scompile.py Q129 lem-trf-derived-basis-increasing-union`
compiled both the sandbox check and final library-path module cleanly within the
60-second per-file limit. The first parse check caught that Lean reserves the
symbol lambda as syntax; the ordinal binder is now named `o`. There are no
non-sorry warnings. The deliver2.py --no-push dry run also passed the server preflight and fresh
per-file compilation (OK, dry-run commit ed62427f4e).

## Second reading by Q129

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
