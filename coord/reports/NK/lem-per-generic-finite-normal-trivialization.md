## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFiniteNormalTrivialization` states
`AlgebraicGeometry.Scheme.exists_generic_finite_normal_trivialization`.
Its entire proof is `sorry`; no definitions or additional theorem statements are introduced.
Only the item's `lean` record changes. No statement correction, new node, or dependency
repair is needed. The previous response concerned an already completed stage-1 split;
this delivery carries out the separately dispatched stage-2 statement.

Sources read: ILO, Expose XVII, proof of Lemma 3.5.7, printed p.276 (PDF page 282),
including the sentence asserting the finite surjective normal integral cover and its
finite etale dense-open restriction. The node abstracts this technical cover construction
from the source's strictly henselian setting; its seven-step proof supplies the construction
for every excellent integral Noetherian scheme. Also read Stacks `etale-cohomology.tex`,
`lemma-locally-constant-on-connected` (Tag 0DV5), especially (3), and `morphisms.tex`,
`lemma-nagata-normalization-finite-general` (Tag 0AVK). These support finite-module
monodromy and finiteness of normalization; no field base or characteristic restriction
is needed for this technical cover statement.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| X is a scheme | `X : Scheme.{u}` |
| X is Noetherian | `[IsNoetherian X]` |
| X is integral | `[IsIntegral X]`, the recorded Mathlib predicate, including nonemptiness |
| X is excellent | `hExcellent : ∀ V : X.affineOpens, IsExcellent Γ(X, V)` |
| A is a finite commutative ring | `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` |
| F is a sheaf of A_X-modules on the ordinary small etale site | `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` |
| F is constructible | `hF : IsConstructibleEtaleModuleSheaf F`, using the recorded finite-value stratification predicate |
| There is a scheme Y and a morphism f to X | `∃ (Y : Scheme.{u}) (f : Y ⟶ X)` |
| f is finite and surjective | `IsFinite f ∧ Surjective f` |
| A nonempty open subscheme U of X | `U : X.Opens` with `Nonempty U`; its scheme is `U.toScheme` |
| A finite A-module N | `N : ModuleCat.{u + 1} A` with `Finite N` (finite underlying set) |
| Y is integral | `IsIntegral Y` |
| Y is normal, meaning all local rings are integrally closed domains | `∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)` |
| f inverse U to U is finite etale | `IsFinite (f ∣_ U) ∧ Etale (f ∣_ U)` |
| Ordinary inverse image f-star F | `(Etale.upperStar (ModuleCat.{u + 1} A) f).obj F` |
| Restriction of that sheaf to f inverse U | apply `Etale.upperStar (ModuleCat.{u + 1} A) (f ⁻¹ᵁ U).ι` |
| Constant module sheaf with value N on f inverse U | `(constantSheaf (f ⁻¹ᵁ U).toScheme.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N` |
| Isomorphism as A-module sheaves | `Nonempty` of the isomorphism between these two objects in the same `ModuleCat`-valued sheaf category |
| No finite-type-over-a-field hypothesis | no base field, base morphism, finite-type instance, or dimension hypothesis occurs |

The coefficient universe is exactly that of the recorded constructibility and ordinary
inverse-image interfaces. It places coefficients and section modules in `u + 1` for
schemes in `u`, as required by the small etale site. Every universe and variable is bound
explicitly; the statement uses no let, hidden have, file-local notation, or local instance.

Recorded statement-dependency declarations read and used:

- `def-exc-excellent-ring`: `IsExcellent` in `Sheaf.RingTheory.ExcellentRing`; its real
  definition is quasi-excellence and universal catenarity. Applied to every affine
  coordinate ring, rather than only global sections.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`; its fields give nonemptiness and domain
  coordinate rings for every nonempty open.
- `def-weil-pbc-etale-constructible-sheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` in
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`; the definition uses a
  finite locally closed stratification with constructible parts and finite module values.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf` in
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, sheafification of the constant presheaf,
  here specialized to `ModuleCat A`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, affine with finite coordinate-ring maps.
- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed` in
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, together with `IsDomain`,
  applied directly to local rings as stipulated by the item's parenthesis and this
  dependency's inline-form convention.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, etale affine-locally on coordinate rings.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, left Kan extension followed
  by sheafification and left adjoint to ordinary direct image. It is used twice,
  first for f and then for the open inclusion.

The canonical scheme restriction is `AlgebraicGeometry.morphismRestrict`, from
`Mathlib.AlgebraicGeometry.Restrict`; its source is `(f ⁻¹ᵁ U).toScheme` and its target
is `U.toScheme`. `IsNoetherian` is from `Mathlib.AlgebraicGeometry.Noetherian`.
All modules of already stated proof dependencies (including Mathlib leaves) are imported
without `public`, except those also needed by the statement. The docstring follows all
seven proof steps with their dependency names: generic lisse open, regular-locus shrinking,
finite monodromy torsor and finite stalk value, normal integral cover over the open,
finite normalization and surjectivity, affine identification, and A-linear composition.

Edge cases checked:

- Empty X is excluded by the node's integral hypothesis itself. Nonempty U is explicit,
  so neither the empty open nor the empty cover can witness the conclusion.
- A may be the zero ring; N may be the zero module. There is no nontriviality or positive
  rank condition. A zero sheaf is handled by a normal finite cover with constant zero value.
- A constructible sheaf may have nontrivial generic monodromy. The cover is existential
  and need not be an isomorphism, so such monodromy is allowed.
- X need not be normal or regular. Normality is required only of Y; etaleness is required
  only over U, so ramification over the complement is allowed.
- Dimension zero and all characteristics are included. For a field base the open can be
  the whole scheme and the cover a finite separable splitting extension.
- Normality is stated at every local ring, and finiteness of N means finite as a set,
  not freeness or any fixed cardinality.

Searches actually run with `msearch.py`:

- LeanFinder: "A constructible etale module sheaf on an excellent integral scheme becomes
  constant on a dense open after a finite surjective normal integral cover". Eight hits,
  including `ModuleCat.Tilde.exists_const`, normalization-diagram constructions, etale
  loci, and locally constant module ranks. None asserts the requested cover theorem.
- Loogle: `"IsIntegral", "IsFinite", "Sheaf"`. Zero hits.
- grep on Mathlib/AlgebraicGeometry:
  `trivializ.*[Ee]tale|[Ee]tale.*trivializ|normalization.*[Ff]inite`.
  Three hits in `ZariskisMainTheorem.lean`, about the quasi-finite locus of normalization;
  no module-sheaf generic trivialization theorem.
- LeanSearch: "A constructible sheaf of modules over a finite ring becomes constant on
  a nonempty open after a finite surjective cover by a normal integral scheme".
  Eight hits, including `Sheaf.IsConstant`, `Scheme.Modules` and `SheafOfModules`;
  no exact cover statement.
- `rg` of the proposed declaration name in Mathlib, upstream `WeilConjectures`,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hit.
- `grep -rn` of the node id in upstream `WeilConjectures`: no hit.
- `rg` of generic trivialization and normal-cover phrases in upstream and project Lean:
  related normalized-generic-data statements found. Read
  `ConstructibleModuleNormalizedGenericData.lean`, `NormalizedGenericDataCore.lean`, and
  `NormalizedGenericDataWithFactorization.lean`. They give an integral morphism and a
  constant comparison at a generic field, explicitly without finiteness of normalization;
  their signatures do not give a finite surjection or a finite etale open restriction.
  Thus none is an exact existing match for this node.

Validation: `scompile.py NK lem-per-generic-finite-normal-trivialization` compiled the
one delivered file in sandbox form (2.8 seconds) and library form (2.9 seconds), with no
errors or warnings. No global build was run. No data definitions, auxiliary sorries,
statement disputes, or other node faults were introduced.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
