## Worker report

The module `Sheaf.AlgebraicGeometry.SheafExt` defines sheaf Ext in all integer degrees
for derived objects on a scheme, together with its bifunctor and its specialization to
modules in degree zero. There are four real definitions and no theorem or `sorry`.
The node copy changes only `lean`; no new or replacement dependency modules are needed.

Clause-by-clause correspondence:

- A scheme X is `(X : Scheme.{u})`, without assumptions of affineness, finiteness,
  separatedness, nonemptiness, or a base field.
- Its ringed site is `Opens.grothendieckTopology X.toRingedSpace` with commutative ring
  sheaf `X.toRingedSpace.sheaf`. The module category is
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`. The existing `moduleRings` abbreviation
  is exactly this structure sheaf composed with `forget₂ CommRingCat RingCat`.
  This is the shared category instance required by the project's derived-module
  convention; `X.Modules` has the same underlying objects but a separately defined
  category instance, so the shared carrier is used throughout.
- D(O_X) is `DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
  The explicit `HasDerivedCategory.{w}` binder specifies the chosen localization and
  morphism universe. It is a choice of derived-category realization, not a geometric
  hypothesis: `HasDerivedCategory.standard` always supplies the standard realization.
- K and L are arbitrary objects of that category; i is `(i : ℤ)`, including negative
  degrees, with no boundedness or perfectness condition.
- R internal Hom is the dependency `CategoryTheory.derivedInternalHom` on that ringed
  site. Its definition uses the functorial K-injective replacement of the second
  argument and the Hom complex, then descends by localization. Its existing comparison
  statements encode the computation with any representatives and K-injective target;
  this module does not redefine that construction or add extra choices.
- H^i is `DerivedCategory.homologyFunctor` on the same module category, as recorded by
  `def-weil-derived-cohomology-sheaves`. The body of `sheafExtFunctor` is precisely
  `derivedInternalHom ... ⋙ DerivedCategory.homologyFunctor ... i`.
- The displayed sheaf Ext object is `sheafExt X i K L`, the value of this composite at
  `(op K, L)`. Its codomain is O_X-module sheaves, not an Ext group or a presheaf.
- For modules F and G, `moduleSheafExtFunctor` precomposes that composite with the
  product of `DerivedCategory.singleFunctor ... 0` in both variables (opposite in the
  first). `moduleSheafExt X i F G` is its value at `(op F, G)`, definitionally the sheaf
  Ext of F[0] and G[0]. Mathlib's single functor places the module in degree 0 and zero
  elsewhere.
- Functoriality is part of the two actual bifunctors: their source is the product of
  the opposite first category with the second category. Their maps are induced by the
  composite functors, giving contravariance in the first variable, covariance in the
  second, and O_X-linear maps; identity and composition laws come from functor composition.

Dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`,
  `Mathlib.AlgebraicGeometry.Scheme` (imported through Modules.Sheaf).
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` and
  `AlgebraicGeometry.Scheme.Modules`, `Mathlib.AlgebraicGeometry.Modules.Sheaf`
  and `Mathlib.Algebra.Category.ModuleCat.Sheaf`. Read the general `mathlib_match` as
  well as the scheme record; the shared carrier is the general recorded notion.
- `def-weil-abstract-derived-category`: `DerivedCategory` and `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` (available via the imports).
- `def-pur-derived-internal-hom`: `CategoryTheory.derivedInternalHom`,
  `Sheaf.Algebra.Homology.DerivedInternalHom`; read its full definition and comparison
  signatures and docstrings.
- `def-weil-derived-cohomology-sheaves`: `DerivedCategory.homologyFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- Existing supporting declarations: `AlgebraicGeometry.moduleRings`,
  `Sheaf.Paper.DerivedHomMayerVietoris`, and `DerivedCategory.singleFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.

Source checked: the local literature files are not present on this machine, so read the
original Stacks pages https://stacks.math.columbia.edu/tag/0BQP and
https://stacks.math.columbia.edu/tag/08DH. The former defines sheaf Ext by H^n(R internal
Hom); the latter constructs the derived bifunctor using a K-injective second argument.
No correction or statement dispute was found.

Edge cases checked before writing: empty schemes and zero modules/derived objects are
not excluded; every integer degree is allowed. For modules the negative Ext sheaves
should vanish, and degree zero should recover the internal Hom sheaf, as the shared
RHom/H^i construction specifies. These are checks of the intended mathematical meaning,
not newly asserted or proved lemmas. Unbounded complexes are permitted. The universe u
of the ringed site and modules matches the existing RHom declaration and the shared
scheme-module carrier; w explicitly records the localization morphism universe.

Searches for an existing declaration:

- `msearch.py ... leanfinder "sheaf Ext as the cohomology sheaf of derived internal Hom"`:
  eight hits including Sheaf.H, cohomologyPresheaf, cohomologyPresheafFunctor, Abelian.Ext,
  and injective/projective resolution Ext equivalences. These are global Ext/cohomology
  groups or presheaves of such groups, not H^i of the derived internal Hom of O_X-modules.
- `msearch.py ... loogle "sheafExt, derivedInternalHom, DerivedCategory.homologyFunctor"`:
  zero hits, unknown identifier sheafExt.
- `msearch.py ... grep "sheafExt|SheafExt|extSheaf|ExtSheaf|derivedInternalHom"`:
  five hits, all unrelated lanPresheafExt in Mathlib/Condensed/Discrete/Colimit.lean.
- `rg` on the same sheaf-Ext names and the node id in the source WeilConjectures tree
  and the project's lean/Sheaf tree: no sheaf Ext declaration. Searching derivedInternalHom
  in the project found only the dependency and its comparisons.
- `rg "sheafExt|moduleSheafExt" dag/lean_names_upstream.json`: no upstream names.

Validation: `scompile.py E1 def-weil-pbc-sheaf-ext` on the delivered module compiled in
2.8 seconds, exit 0, without errors or warnings. The required delivery dry run follows.

## Second reading by E1

I independently read the node statement, its Stacks source (Tags 0BQP and 08DH),
all five statement dependencies, and `Sheaf/AlgebraicGeometry/SheafExt.lean`.
The item-by-item correspondence is:

- The scheme `X` is rendered by `(X : Scheme.{u})`; no geometric hypotheses are
  added. Verdict: exact, including empty schemes.
- The structure sheaf and open site are rendered by
  `X.toRingedSpace.sheaf` and `Opens.grothendieckTopology X.toRingedSpace`.
  The module category is `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
  Verdict: this is the dependency's shared sheaf-of-modules category, with no
  replacement or extra structure.
- The derived category is the explicit
  `DerivedCategory (SheafOfModules ... )` with only the implementation-choice
  instance `[HasDerivedCategory.{w} ...]`; this is not a geometric hypothesis.
  Verdict: exact universes and assumptions.
- Arbitrary derived objects `K L` and every `i : ℤ` are accepted by
  `sheafExtFunctor` and `sheafExt`; no boundedness, positivity, or
  perfectness is imposed. Verdict: exact, including negative degrees and `i=0`.
- The derived internal Hom is used directly through the dependency declaration
  `derivedInternalHom (Opens.grothendieckTopology ...) X.toRingedSpace.sheaf`;
  it is not privately redefined. Verdict: exact `R\mathcal Hom` and its
  contravariant/covariant source.
- The cohomology sheaf is rendered by composition with
  `DerivedCategory.homologyFunctor ... i`. Verdict: exact `\mathcal H^i`.
- The displayed value is `(sheafExtFunctor X i).obj (op K, L)`, giving an
  `O_X`-module sheaf. Verdict: exact object and codomain.
- The module specialization is rendered by the product of two
  `DerivedCategory.singleFunctor ... 0` functors in
  `moduleSheafExtFunctor`, and its value by `moduleSheafExt`. Verdict: exact
  `F[0],G[0]` specialization, with contravariance in `F` and covariance in `G`.
  Functoriality is inherited from these actual bifunctors, as required by the
  node's final clause.

I checked edge cases explicitly: empty schemes, zero modules and zero derived
objects remain admissible; all integer degrees remain admissible (negative Ext
is not excluded); and no nonempty-index, characteristic, Noetherian,
separatedness, or finiteness assumption is introduced. Universes `u` and `w`
are bound and match the dependency declarations.

Searches were repeated with LeanFinder/Loogle and grep over Mathlib,
`WeilConjectures`, and `lean/Sheaf` for `sheafExt`, `SheafExt`, `extSheaf`,
and `derivedInternalHom`. They found only unrelated presheaf Ext/cohomology
or the already-recorded derived-internal-Hom dependency; no existing sheaf-Ext
notion matches the node. No mismatch was found and no source or Lean change was
needed. The module compiles cleanly with `scompile.py` (exit 0, no warnings).
