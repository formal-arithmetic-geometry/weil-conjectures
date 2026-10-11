## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction` renders the
whole node with one data definition and two unproved named theorems. No node
statement was corrected, no dependency was replaced, and no new notion was needed.
The node itself explicitly introduces the base change map, so its definition belongs
in this module. The two theorem proofs are `sorry`; all definition data are explicit.

Hypothesis and clause correspondence:

- The preliminary arbitrary commutative square has schemes `X S T X₁`, maps
  `f f₁ u₁ v`, and relation `h : v ≫ f = f₁ ≫ u₁` in `moduleBaseChangeMap`.
  `F : X.Modules` is an arbitrary sheaf of O_X-modules, not restricted to
  quasi-coherent sheaves. Its source and target are respectively
  `(tensorPullback u₁).obj ((pushforward f).obj F)` and
  `(pushforward f₁).obj ((tensorPullback v).obj F)`.
- The specified adjoint map is the pushforward of
  `(Classical.choose (exists_tensorPullbackAdjunction v)).unit.app F`, followed
  by `pushforwardComp v f`, `pushforwardCongr h`, and the inverse of
  `pushforwardComp f₁ u₁`. Applying the inverse `homEquiv` for `u₁` gives precisely
  beta. Composite pushforwards have identity maps on sections; the equality
  transport identifies the equal inverse-image opens. Thus this is the node's
  sectionwise identification, not an arbitrary isomorphism.
- Naturality for every module morphism `φ : F ⟶ G` is the equality in
  `moduleBaseChangeMap_naturality`, with the two functors acting on φ.
- The restriction theorem binds all eight schemes `X S X' S' U V XU X'V`,
  the original maps `f f' g g'`, and original commutativity `h`.
- Each of `jU jV jX jX'` has exactly an `IsOpenImmersion` instance.
  The four restricted morphisms are `fU fV' gV gV'`.
- The four compatibility equations are `hf hf' hg hg'`, in exactly the order
  given in the node; the restricted square equation is `hV`.
- The full inverse-image conditions are exactly `hX : Set.range jX =
  f ⁻¹' Set.range jU` and `hX' : Set.range jX' = f' ⁻¹' Set.range jV`.
- `rho` and `rho'` are applications of the same defined base change map to
  the respective open squares, using `hf` and `hf'`. Clause (1) is the first
  two conjuncts, each quantified over every module of the appropriate scheme.
- `c` is the canonical isomorphism from pullback of a composite to successive
  pullback: it is the mate of `pushforwardComp`, under the canonical adjunctions.
  Its inverse is the node's arrow from successive to composite pullback.
  This avoids choosing an arbitrary witness of `nonempty_tensorPullbackComp`.
- `a` is exactly the node's first displayed composite: `(c jV g).inv.app`,
  transport by `hg`, `(c gV jU).hom.app`, and pullback of `rho F`.
  `b` is its second displayed composite: `rho'` on the pullback of F by g',
  pushforward of `(c jX' g').inv.app`, transport by `hg'`, and pushforward
  of `(c gV' jX).hom.app`.
- `IsIso a ∧ IsIso b` expresses the statement's assertion that these comparison
  maps are isomorphisms. With `≫` denoting first the left arrow, clause (2) is
  `(tensorPullback jV).map beta ≫ b = a ≫ betaV`.
- The final conjunct is the exact iff between `IsIso` of the restricted beta
  and `IsIso betaV`, at `(tensorPullback jX).obj F`.

Dependencies used:

- `def-pc-scheme`: Mathlib's `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  in `Mathlib.AlgebraicGeometry.Scheme`; signatures and docstrings read.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, used through `Scheme.Modules`
  (`Mathlib.AlgebraicGeometry.Modules.Sheaf`). Both declarations were read.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`; read its locally ringed space definition.
- `def-pc-module-pullback`: `Scheme.Modules.tensorPullback`, in
  `Sheaf.AlgebraicGeometry.TensorPullback`; the whole module was read.
- Added the already landed `lem-pc-module-pullback-adjunction` to stmt_deps,
  under brief-stage2 §5's rule allowing landed nodes: its
  `Scheme.Modules.exists_tensorPullbackAdjunction`, in
  `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, pins the chosen adjunction
  to the tensor/inverse-image unit. The whole node and module were read.
- Mathlib `Scheme.Modules.pushforward`, `pushforwardComp`, `pushforwardCongr`
  and `CategoryTheory.conjugateIsoEquiv` supply the sectionwise direct image,
  its canonical coherence maps and their mates. Their signatures were read.

Edge cases checked before writing: empty schemes and empty open images are allowed;
zero module sheaves are included in the universal module quantifiers; identity or
isomorphic open immersions are allowed; the original square need only commute, not
be cartesian. The two open squares must have the full inverse-image images, exactly
as required by the node. There is no affine, finite, proper, flat, noetherian or
quasi-coherence hypothesis. Universe u is explicit and arbitrary, matching the
recorded Scheme.Modules and tensorPullback universes. All variables are bound and
`autoImplicit` is disabled. The maps a and b are canonical mates, so twisting an
adjunction arbitrarily is not an implicit extra choice in the statement.

Searches (2026-10-11):

- `msearch.py ... leansearch "base change map modules restriction open immersion"`:
  service unavailable, Internal Server Error; no verdict drawn from this search.
- `msearch.py ... leanfinder "base change map of sheaves of modules commutes with
  restriction to open subschemes"`: eight hits on `Scheme.Hom.appLE`, naturality,
  module scalar restriction, and pushforward sections; none states this theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Modules.pushforwardComp"`:
  six hits including the composition isomorphism and its section formulas,
  abstract pullback conjugation and pseudofunctor formulas; no exact statement.
- `msearch.py ... grep "baseChange|base_change" AlgebraicGeometry/Modules`:
  no Mathlib hits.
- `rg` over `WeilConjectures` and `lean/Sheaf` for module base change and the item
  id: no exact statement. The source's Etale base change statements concern a
  different site and coefficient category. Landed `moduleBaseChange` in
  `BaseChangeConventions.lean` is a pullback functor, not the exchange morphism.
- Exact declaration-name search in Mathlib, upstream source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no conflicts for any of the three new names.

Sources read from the official Stacks pages because literature/stacks-project is
not present on this machine: https://stacks.math.columbia.edu/tag/02KG (locality),
https://stacks.math.columbia.edu/tag/00A0 (module restriction), and
https://stacks.math.columbia.edu/tag/0ATL and
https://stacks.math.columbia.edu/tag/0ATM (pasting). The module docstring carries the
node's four proof steps and their dependency node names. No statement dispute.

Validation: server single-file compile passed without errors or warnings after
correcting the orientation of the canonical composition mate. Final delivery dry
run is required below; the independent second reading is reserved for the next worker.

`deliver2.py C1 lem-weil-pbc-module-base-change-map-open-restriction --no-push`
printed OK: compile and preflight passed except for the independent second reading,
which the tool explicitly reserves for the second reader. Nothing was pushed.

## Second reading by C1

The node introduces the commutative square schemes and maps `f f' g g'` with `h`; the Lean binds these as `X S X' S'`, the four morphisms, and `h : g' ≫ f = f' ≫ g`. It then introduces four open immersions and four restricted morphisms; the Lean has `jU jV jX jX'`, four `[IsOpenImmersion]` instances, and `fU fV' gV gV'`. The four compatibility equations are rendered by `hf hf' hg hg'`, and the restricted square by `hV`; the image hypotheses are exactly `hX` and `hX'` using `Set.range` and preimages.

The preliminary base-change map is rendered by `moduleBaseChangeMap`, with source `(tensorPullback u₁).obj ((pushforward f).obj F)`, target `(pushforward f₁).obj ((tensorPullback v).obj F)`, and its adjoint-defined formula using `exists_tensorPullbackAdjunction`; the naturality clause is `moduleBaseChangeMap_naturality` for every `φ`. The node's `rho` and `rho'` are the two corresponding `moduleBaseChangeMap`s. The conclusion's first clause is rendered by the first two universal `IsIso` conjuncts. The displayed comparison maps are rendered by the `let c`, `let a`, and `let b` expressions with the canonical composition mates and the stated equality transports. The second clause is exactly `(tensorPullback jV).map beta ≫ b = a ≫ betaV`, and the final iff is exactly the two `IsIso` propositions. Quantifier order and all module universes match.

Edge cases remain covered: empty schemes and empty open images, zero modules, identity open immersions, arbitrary (including non-quasi-coherent) modules, and no finiteness, separatedness, affine, or characteristic assumptions. The single universe `u` is bound and `autoImplicit` is disabled.

Searches were independently checked with `rg` over `WeilConjectures`, `lean/Sheaf`, and DAG declaration names, and with the recorded LeanSearch/LeanFinder/Loogle/grep queries. No existing declaration states this base-change restriction theorem or conflicts with the three declarations in the module.

One mismatch was found: the module imports and uses the landed `exists_tensorPullbackAdjunction`, but the node's `stmt_deps` omitted `lem-pc-module-pullback-adjunction`. I added that existing dependency id to `stmt_deps`; no Lean statement or definition required alteration. The module compiles cleanly with `scompile.py`.
