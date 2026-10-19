## Worker report

The module `lean/Sheaf/Paper/SfHomTriangulated.lean` states
`AlgebraicGeometry.Etale.sf_internalHom_triangulated`, with `sorry` as its entire proof.
It specializes the existing ringed-site internal Hom to the constant commutative ring
sheaf on the small etale site. There are no new definitions or additional nodes.

The source was checked at https://stacks.math.columbia.edu/tag/08JC (Lemma 21.35.4)
and https://stacks.math.columbia.edu/tag/08J7 (Section 21.35). These give exactness in
both variables and the same K-injective computation. The generic proof dependency's
`ringedInternalHom_exact` uses the same `CommShift`/`IsTriangulated` interface as this
statement; the specialization is not an exact existing declaration, since that theorem
also quantifies over the ringed site and uses the earlier small-category implementation
of internal Hom.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| A commutative ring A | `(A : Type (u + 1)) [CommRing A]` |
| A scheme X | `(X : Scheme.{u})`, with no geometric assumptions |
| Small etale site | `X.smallEtaleTopology` on Mathlib's `X.Etale` |
| Size convention | Explicit universes `u w`; site objects have level `u + 1`, morphisms `u`; coefficients and module sections have level `u + 1` |
| Constant commutative ring sheaf A_X | `(constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)` |
| Mod(A_X) and its derived category | `SheafOfModules.{u + 1}` after `sheafCompose ... (forget₂ CommRingCat RingCat)`, then `DerivedCategory` |
| Chosen localization in the larger universe | The structural `[HasDerivedCategory.{w} ...]` binder, as in the recorded internal-Hom definition; it specifies the localization rather than restricting the schemes or complexes |
| Derived internal Hom computed by K-injectives | `derivedInternalHomOfUniverses.{u + 1, u, u + 1, w}` applied to precisely that topology and constant ring sheaf |
| Fix M and vary K | The curried bifunctor's `.flip.obj M`, the first conjunct |
| K', K, K'' and their distinguished triangle | Quantification over all triangles in the opposite derived category in `Functor.IsTriangulated` for `.flip.obj M` |
| Reversed distinguished Hom triangle | The first `IsTriangulated`: the opposite distinguished triangle has vertices `op K''`, `op K`, `op K'`; mapping it yields H(K'',M), H(K,M), H(K',M) in that order |
| Fix K and vary M', M, M'' | The second conjunct's curried `.obj (op K)` and its `IsTriangulated`, quantifying over all distinguished triangles in D(Mod(A_X)) |
| Distinguished covariant Hom triangle | Its mapped triangle has vertices H(K,M'), H(K,M), H(K,M'') |
| Shift and sign identifications in the arrows | Each conjunct supplies `CommShift ℤ` for its actual internal-Hom functor. `Functor.mapTriangle` maps the first two arrows by that functor and composes the mapped boundary with `commShiftIso 1`. `CategoryTheory.Pretriangulated.Opposite` supplies the negative shift and the standard reversed-triangle signs in the first conjunct |
| No boundedness or finite-generation conditions | Both conjuncts quantify over all derived objects; there are no boundedness, constructibility, flatness, projectivity, or finite-generation binders |

`Functor.IsTriangulated` is used instead of writing six vertices and two triples of
arrows: its defining field is preservation of **every** distinguished triangle under
`Functor.mapTriangle`. Thus the two conjuncts express exactly the two displayed
triangle conclusions. Neither conclusion is merely an existential choice of a boundary
map: the whole triangle is the functor's image under its shift-compatible structure.
The shift structures are outputs of the exactness assertion, as in the already recorded
generic theorem, rather than new assumptions on the input triangles.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `AlgebraicGeometry.Scheme.smallEtaleTopology`,
  with `AlgebraicGeometry.Scheme.Etale` read in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-size-convention` is recorded as a metatheoretic convention with no module;
  the statement renders it with explicit universes and the localization structure.
- `Sheaf.AlgebraicGeometry.DerivedCategories` publicly reexports the node's existing
  derived-category notions, including Mathlib `DerivedCategory`. Here the node's
  literal formula `D(Mod(A_X))` is used, since the ringed-site internal Hom acts on
  that category. No second derived-category construction is introduced. The module's
  `DerivedCategoryModule` abbreviation instead uses module-valued sheaves, the equivalent
  encoding explained in its documentation; the present statement concerns the ringed-site
  encoding explicitly specified in the item's statement.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, including its documented localization
  through the Hom complex and functorial K-injective replacement. Its full signature,
  body, representative comparisons and docstrings were read. `scompile.py --source`
  confirmed that this is also the current published source.
- Proof import `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`:
  `CategoryTheory.ringedInternalHom_exact`, whose two exactness clauses and full cone
  proof docstring were read. The proof plan describes transport through a small model
  when applying its equal-universe version to the actual etale site. No site universe
  equality is imposed in the delivered statement.
- `Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated` supplies the actual
  opposite pretriangulated structure. Its scope is opened to activate Mathlib's scoped
  instance. This introduces neither notation nor a file-local instance definition.

Edge cases checked: the empty scheme is admitted; the zero ring is admitted (no
`Nontrivial A`); any of the six complexes can be zero; split and nonsplit triangles
are both included; all complexes may be unbounded in either direction; negative as
well as positive shifts are included by `CommShift ℤ`. No product-index finiteness
condition occurs. The site object and morphism universes remain distinct. The
structural localization binder allows any chosen derived-category universe w, as
in the existing internal-Hom declaration. No disputed statement or correction was found.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "derived internal Hom on etale sheaves triangulated each variable"`:
  8 hits, including sheaf cohomology, light condensed closed structures, and the
  scheme-module pseudofunctor. None states the two etale-derived Hom exactness clauses.
- `msearch.py ... loogle "DerivedCategory, IsTriangulated, Hom"`: 0 hits; the service
  reported unknown identifier `IsTriangulated`.
- `msearch.py ... grep "internalHom|derivedInternalHom" AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch "derived internal Hom of sheaves preserves distinguished triangles in both variables"`:
  service unavailable, Internal Server Error; no mathematical conclusion drawn from it.
- `rg` in Mathlib's triangulated files and upstream `WeilConjectures` found no exact
  etale specialization. Upstream `WeilConjectures.SixFunctors.Etale.Derived.Hom` defines
  `AlgebraicGeometry.Etale.derivedHom` as the monoidal closed right adjoint and supplies
  tensor-Hom adjunctions, but no exactness declaration for these two variables.
- `rg` in `lean/Sheaf` found `CategoryTheory.ringedInternalHom_exact`, the generic
  proof dependency, but no theorem for this constant ring sheaf and the recorded
  universe-general internal Hom. The shift comparison modules were read too.
- `rg` for the item id and proposed declaration in upstream sources and
  `dag/lean_names_upstream.json` found no collision. No private copy of an operation
  has been defined.

Verification: `scompile.py N2 lem-sf-hom-triangulated
lean/Sheaf/Paper/SfHomTriangulated.lean` passed the sandbox and library-module
checks, with no errors or warnings (31.0 s and 9.3 s). Initial elaboration failures
were repaired by specifying the existing operation's universe arguments and opening
Mathlib's scoped opposite pretriangulated structure. Only the permitted `sorry` remains.

## Second reading by N2

I read the node `lem-sf-hom-triangulated` and its source place (the blueprint node at
order 2081), and checked the cited Stacks source, Tag 08JC (Lemma 21.35.4), together
with Tag 08J7 (Section 21.35). The source states that the derived internal-Hom
bifunctor on a ringed site sends distinguished triangles to distinguished triangles in
each variable. The node specializes this to the following list.

* The coefficient object is a commutative ring `A`; Lean renders this as
  `(A : Type (u + 1)) [CommRing A]`, with no `Nontrivial` or characteristic
  assumption.
* The geometric object is an arbitrary scheme `X : Scheme.{u}`. The small étale site
  is `X.smallEtaleTopology`, using the recorded Mathlib `X.Etale` site; no separated,
  finite-type, noetherian, or nonempty hypothesis is added.
* The coefficient ring sheaf is exactly
  `(constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
  (CommRingCat.of A)`, and the module category is the sheaf-of-modules category over
  its underlying ring sheaf. The displayed `HasDerivedCategory.{w}` binder supplies
  the chosen localization universe required by the existing derived-category API;
  it is structural and adds no finiteness condition.
* The derived internal Hom is precisely
  `derivedInternalHomOfUniverses.{u + 1, u, u + 1, w}` on that topology and ring
  sheaf, the recorded K-injective construction. Thus all six objects in the node are
  objects of the same derived module category, with no boundedness, constructibility,
  flatness, projectivity, or finite-generation hypothesis.
* For the first displayed sequence, Lean's first conjunct quantifies every target
  `M`, equips the curried functor in the first (contravariant) variable with its
  `CommShift ℤ`, and asserts `Functor.IsTriangulated`. This is the reversed triangle
  `RHom(K'',M) → RHom(K,M) → RHom(K',M) → RHom(K'',M)[1]`, including the opposite
  shift and signs.
* For the second displayed sequence, Lean's second conjunct quantifies every source
  `K`, equips the covariant second-variable functor with `CommShift ℤ`, and asserts
  `Functor.IsTriangulated`. This is exactly the triangle
  `RHom(K,M') → RHom(K,M) → RHom(K,M'') → RHom(K,M')[1]`.

The quantification through `Functor.IsTriangulated` is the library formulation of
the node's “for every distinguished triangle” clauses: its field maps every
distinguished triangle to a distinguished triangle, while the existential
`CommShift` records the node's usual shift and sign identifications. No additional
objects or hypotheses occur, and no conclusion is weakened. The empty scheme and
zero objects are admitted; the zero ring is admitted; split and nonsplit triangles,
unbounded complexes, and all integer shifts are covered. Site object and morphism
universes remain distinct (`u + 1` and `u`).

I opened the declarations of all statement dependencies. `smallEtaleTopology` is
Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`; the size convention is
metatheoretic and is represented by explicit universe parameters; the derived
category dependency supplies the sheaf-module derived category; and
`derivedInternalHomOfUniverses` has the same independent site/coefficient universe
parameters and K-injective construction used by the module. The proof tool
`CategoryTheory.ringedInternalHom_exact` was read at its full signature: it has the
same two `CommShift`/`IsTriangulated` clauses, with first-variable opposite
variance and second-variable covariance.

I searched Mathlib, the project `lean/Sheaf` tree, and the upstream
`WeilConjectures` tree using LeanFinder, Loogle, LeanSearch (unavailable), and
targeted `rg` searches for `derivedInternalHom`, `internalHom`, `RHom`, and
`IsTriangulated`. The results contain only generic derived-category/Hom-complex
APIs and the ringed-site theorem; no exact constant-sheaf étale specialization or
colliding declaration exists. No definition or dependency module was missing, and
no statement mismatch was found, so no files or node fields were changed in this
second reading.

The mandated compile was rerun after this reading:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N2 lem-sf-hom-triangulated
lean/Sheaf/Paper/SfHomTriangulated.lean`; both sandbox and library checks passed with
only the permitted theorem `sorry`.
