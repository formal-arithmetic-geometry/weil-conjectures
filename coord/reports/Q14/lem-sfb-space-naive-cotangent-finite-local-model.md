## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentFiniteLocalModel` states
`AlgebraicGeometry.AlgebraicSpace.naiveCotangent_finite_local_model`, with proof `sorry`.
No definition, extra hypothesis, statement correction, new node, or dependency repair is needed.
The source is Stacks, spaces-more-morphisms.tex, Tag 0D0Z, lemma-netherlander-fp,
read together with the existing small-site constructions. The latest blueprint unit's
proper/open direct-image proof provides the inherited context; this is its supporting
local cotangent lemma, not the unit statement.

Clause-by-clause rendering:

- The base scheme is `{S : Scheme.{u}}`; the two algebraic spaces over that same base
  are `{X Y : AlgebraicSpace S}` and their morphism is `(f : X ⟶ Y)`.
- Local finite presentation on étale scheme charts is
  `(hfp : MapIsLocallyOfFinitePresentation f)`. Its definition expands to the
  recorded scheme predicate `LocallyOfFinitePresentation` for every compatible
  pair of representable étale charts, with their commuting triangle.
- The family is `∃ (I : Type u) (U : I → Over S)
  (a : ∀ i : I, schemeSpace (U i) ⟶ X)`. Each U i is an actual S-scheme,
  represented in the algebraic-space category by the existing `schemeSpace`.
  The index can be empty and no finiteness of the atlas or quasi-compactness is assumed.
- Its representable étaleness is `∀ i, IsEtale (a i).hom.hom`.
  Its joint surjectivity is `IsJointlySurjective (fun i ↦ (a i).hom.hom)`, using
  the existing field-extension lift condition on point classes, not surjectivity
  of sections on each test scheme.
- On each chart, the complex is
  `K : CochainComplex (schemeSpace (U i)).SmallModules ℤ`.
  Its two terms are `K.X (-1)` and `K.X 0`, and its differential is `K.d (-1) 0`.
  The condition `∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (K.X n)` makes all other
  terms zero. The complex structure supplies the differentials and d squared zero.
  Zero objects here are categorical zero modules, as appropriate in a module category.
- Both terms are quasi-coherent: the two `.IsQuasicoherent` conjuncts apply to
  `smallModuleEquivalence.inverse.obj (K.X (-1))` and the same expression at 0.
  This is Mathlib's existing local-presentation predicate on the actual small
  étale module topos, transported through the recorded affine-basis equivalence.
- Finite type in degree -1 is `.IsFiniteType` on the same inverse-transported term.
  Mathlib `LocalGeneratorsData` is a covering of the terminal sheaf with generating
  sections; `IsFiniteType` makes each family finite, and `GeneratingSections.epi`
  is the epimorphism from the corresponding free module.
- Finite presentation in degree 0 is `.IsFinitePresentation` on its transported term.
  Mathlib's `QuasicoherentData.IsFinitePresentation` gives finite generators and
  finite relations on a cover. `Presentation.isColimit` identifies the resulting
  free-module sequence as a cokernel sequence. These are exactly the two local
  finiteness explanations in the node, with no Noetherian assumption.
- The derived isomorphism is
  `Nonempty ((smallTensorPullbackComplex (a i)).obj (naiveCotangentComplex f) ≅
  DerivedCategory.Q.obj K)`. This is one isomorphism of derived objects, including
  the differential, rather than separate cohomology isomorphisms. The existing
  `smallTensorPullbackComplex` applies the canonical ordinary tensor pullback
  termwise and then Q. Along an étale chart this is precisely restriction:
  `moduleTensorPullback_etale_restriction` identifies ordinary tensor pullback
  with restriction, by multiplication on chart sections. Conjugating through
  the existing small-module equivalences gives the same assertion on the basis.
  Exactness of restriction means Q of this termwise pullback is the derived
  restriction of Q of the given complex. No new arbitrary map or functor is supplied.
- The chart localization universe is arbitrary `w`, with
  `[HasDerivedCategory.{w} (schemeSpace (U i)).SmallModules]` quantified for each
  chart. The source is passed as its actual complex, so no source derived-category
  instance or artificial equality of source/target universes is needed. The
  module-section universe remains u throughout, including transport back to the
  original site. Standard localization gives the usual available instance.

Dependency declarations used (read signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `Modules`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex`:
  `naiveCotangentComplex`, built from the explicit conormal and differential.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: its slice
  sheafification instances and Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallModules`, `smallModuleEquivalence`, retaining the actual regular-functions ring.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`:
  `smallModuleTensorPullback`, `smallTensorPullbackComplex`.
- Mathlib module-sheaf `Generators` and `Quasicoherent`: `IsFiniteType`,
  `IsFinitePresentation`, `IsQuasicoherent`, with the finite free local presentations.

The last three owning definition nodes are added to `stmt_deps`; each already has a
usable landed Lean record. All pre-existing dependencies and the natural-language
statement are preserved. The public imports provide the statement dependencies;
plain imports retain every already stated proof dependency. The two proof-only nodes
`lem-sfb-space-naive-cotangent-etale-localization` and
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` currently have no Lean
records, so there is no module of either to import. Their role remains in the proof
docstring. The affine presentation theorem's recorded module is imported as a proof
dependency, with the original conormal differential and arbitrary generator set.

Edge cases checked before writing: empty X permits an empty atlas; no `Nonempty I`
binder occurs. Identity and étale maps admit the zero complex. For a polynomial
algebra with no relations, the degree -1 term is zero and degree 0 is finite free.
Zero variables and zero relations are permitted by Mathlib finite presentation.
For k[x]/(x²) in characteristic 2, the differential can vanish while the degree -1
term remains nonzero: the statement imposes neither injectivity nor vanishing of
H^-1. Over a non-Noetherian base the conormal is only finite type, exactly as stated;
no finite presentation of that term or finiteness of its kernel is asserted.
The derived morphism universe is independent of the ring/section universe, and
restriction stays on the small étale site rather than replacing it by Zariski restriction.

Searches made:

- `msearch.py leanfinder`, query “For a locally finitely presented morphism of
  algebraic spaces the naive cotangent complex etale locally has a two term quasi
  coherent model of finite type”, and the shorter query “Algebraic space naive
  cotangent complex finite two term etale local model”: ring-level cotangent H1
  finiteness and étale-algebra results, no sheaf or algebraic-space local-model theorem.
- `msearch.py leansearch`, query “An algebraic space morphism locally of finite
  presentation has an etale local finite two term naive cotangent model”: eight
  scheme/algebra local-finite-presentation and étale results; no match.
- `msearch.py loogle`, query `"H1Cotangent", "FinitePresentation"`: one hit,
  `Algebra.instFiniteH1CotangentOfFinitePresentationOfProjectiveKaehlerDifferential`.
  This is ring H1 finiteness under projectivity of differentials, not this statement.
- `msearch.py grep`, query `naiveCotangent|naive_cotangent|netherlander` in Mathlib
  AlgebraicGeometry: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `naiveCotangent.*finite|naive_cotangent.*finite|netherlander` and the exact item id:
  no existing target declaration. Separate `rg` for the proposed declaration name
  in both libraries and `dag/lean_names_upstream.json`: no collision.
- Concept searches in project Lean found the existing small-ringed-model,
  joint-surjectivity, local-finite-presentation and tensor-pullback declarations
  listed above. Mathlib sources for local generators and presentations were read;
  no duplicate notion is introduced.

Validation: `scompile.py Q14 lem-sfb-space-naive-cotangent-finite-local-model`
compiled the delivered file in module mode on the server, cleanly (sandbox 27.4 s,
library 10.6 s). No diagnostic commands, auto-bound implicits, new definitions,
or theorem proofs other than the expected `sorry` are present. No statement is disputed.
The delivery dry run and final push follow this validation.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
