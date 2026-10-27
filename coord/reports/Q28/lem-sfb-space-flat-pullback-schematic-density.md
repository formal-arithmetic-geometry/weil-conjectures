## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFlatPullbackSchematicDensity` states
`AlgebraicGeometry.AlgebraicSpace.flat_pullback_schematicDensity`, with its proof
`by sorry`. No definitions or further nodes are needed. The source read was
`literature/stacks-project/spaces-morphisms.tex`, Tag 089D,
`lemma-flat-morphism-scheme-theoretically-dense-open` (lines 6045–6062).
It assumes only flatness, a quasi-compact open immersion, and schematic density.
The module docstring and declaration docstring explain the section formulation;
the latter carries all five steps of the node's proof.

Hypotheses and conclusions, clause by clause:

- The scheme `S : Scheme.{u}` and `X Y V XV : AlgebraicSpace S` use the existing
  fppf-sheaf definition. The single explicit universe `u` is the universe of the
  existing scheme and space interfaces. Test schemes also have this universe.
  The size-convention dependency is metatheoretic and has no module to import.
- `f : X ⟶ Y`, `j : V ⟶ Y`, `jX : XV ⟶ X`, `g : XV ⟶ V` and
  `hcart : IsPullback g.hom jX.hom j.hom f.hom` specify the actual sheaf fibre
  product, using its universal property. Quantifying over an arbitrary cartesian
  representative introduces no mathematical assumption: the recorded fibre-product
  theorem gives such a representative, and all representatives are uniquely
  isomorphic over both factors. No arbitrary replacement map is substituted.
- `hf : MapIsFlat f` is exactly flatness in every compatible pair of representable
  étale scheme charts, using the dependency's definition without duplication.
- `hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`
  is exactly representability by open immersions. This is the predicate in the
  recorded `OpenSubspace` definition; the morphism form retains the node's `V`.
- `hqc` quantifies over `T : Y.EtaleSite` with `IsAffine T.obj.left.left`.
  Its scheme `U` and `IsPullback r (yoneda.map p) j.hom.hom T.obj.hom`
  represent the inverse image; `CompactSpace U.left` says it is quasi-compact.
  Thus it tests every affine étale scheme chart, exactly as the node requests.
- `hdense` quantifies over every small étale chart `T` and every pair of regular
  functions `a b` on it. Equality after pullback along every compatible chart
  `U : V.EtaleSite` forces `a = b`. The restrictions are the actual maps
  `(Scheme.Γ.map p.left.op).hom`. Sections of `j_*𝒪_V` on `T` are compatible
  families on the étale charts of `T ×_Y V`: every such chart is exactly a pair
  `(U,p)` satisfying the displayed triangle, because `j` is open. Equality of
  these families is equality on all those charts. This is precisely componentwise
  injectivity of `𝒪_Y → j_*𝒪_V`, hence sheaf injectivity. This inline formulation
  already occurs in the project's `exists_qcOpen_schematicClosure`; no second
  density definition or extra structural map is introduced.
- The first conclusion is the same open-immersion predicate for `jX`.
  The second is the same affine-étale quasi-compactness condition for `jX`.
  The third is exactly the same sheaf-injection condition with `X,XV,jX` in
  place of `Y,V,j`. These give all three claimed properties of the pullback.
  The last phrase “thus schematically dense” is this injection, not an extra
  topological-density assertion.

Recorded dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `EtaleSite`, `structurePresheaf`,
  `structureSheaf`. Their definitions give precisely the chart objects and
  global functions used in the formula.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat` (compatible étale charts, with `Flat` on scheme morphisms).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` (the
  representability predicate is used directly for a given map).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `LocallyOfFiniteType`,
  `QuasiCompact`; quasi-compact inverse images of affine charts are rendered by
  compactness of their representing scheme, just as the node defines them.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. The main theorem's `IsPullback` is in this
  same category of sheaves, rather than a different fibre-product construction.

All modules of the recorded proof dependencies are imported without `public`,
including the space chart tests, chartwise permanence, quasi-compact/separated
étale locality, étale module pushforward restriction, scheme images and flat
scheme-density base change. Statement dependency modules are public imports.
There is no import-cycle omission and no dependency interface repair.

Edge cases checked before writing: empty `X` and the empty open subspace; an
empty open can satisfy `hdense` only over an empty ambient space, since otherwise
restriction would fail to distinguish zero and one on a nonempty affine chart.
Identity open immersions and identity flat maps are included. No nonemptiness,
Noetherian, separatedness, finite type, or quasi-compactness of `f`, `X`, or `Y`
is assumed. Nilpotents are retained because the hypothesis detects actual regular
functions, not just underlying topological points. All affine étale charts, and
all their inverse-image charts, are quantified over in the existing universe.

Searches actually run:

- `msearch.py leanfinder`: “Flat pullback of a quasi compact schematically dense
  open subspace of an algebraic space is schematically dense”. Eight results,
  including scheme dominance, rational-map dense domains, flat generalizing maps,
  and open-immersion descent; none states the algebraic-space theorem.
- `msearch.py loogle`: `AlgebraicGeometry.IsSchemeTheoreticallyDominant,
  AlgebraicGeometry.Flat`. Three hits: `pullbackFst`, `pullbackSnd`,
  `of_isPullback`; each applies to schemes only.
- `msearch.py grep`: `schematic|SchemeTheoreticallyDominant` in
  `AlgebraicGeometry`. Nine hits, all on scheme density or geometrically reduced
  schemes; no algebraic-space statement.
- `msearch.py leansearch`: “Schematic density of a quasi compact open immersion
  of algebraic spaces is preserved by flat base change”. Eight results on
  stability under base change of scheme properties; no algebraic-space result.
- `rg` in `lean/WeilConjectures` for schematic/dominant terminology and for the
  node id; the results are about schemes, including the existing scheme-level
  flat-pullback input. No matching algebraic-space statement was found.
- `rg` in `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/TraceFormula` for
  schematic density found `AlgebraicSpaceQcOpenSchematicClosure.lean`, whose
  regular-function detection formula is reused inline here. The existing
  `SchematicallyDenseOpen` definition is for open subschemes of schemes.
- `rg` in `dag/lean_names_upstream.json` and both source roots for the intended
  declaration name and node id found no duplicate declaration.

No statement correction and no STATEMENT-DISPUTED issue. The pre-existing
`SpaceQCSeparatedEtaleLocal` covering predicate is stronger than the usual
joint-surjectivity notion; this theorem's statement does not use that predicate.
The stage-3 proof should use the existing all-scheme representability/base-change
calculus for its quasi-compactness clause if that proof dependency is still
unrepaired then. The mathematical statement itself needs no stronger hypothesis.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
