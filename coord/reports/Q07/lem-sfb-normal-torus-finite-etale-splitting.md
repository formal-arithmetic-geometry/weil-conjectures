## Worker report

The module `Sheaf.AlgebraicGeometry.NormalTorusFiniteEtaleSplitting` states
`AlgebraicGeometry.normal_torus_finite_etale_splitting`. It has one theorem,
with proof `sorry`, and no new definitions. The node's mathematical statement and
accepted proof are unchanged. Its statement dependencies gain the already landed
`def-sfb-relative-torus`, whose actual module and definitions are reused.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Scheme S | `S : Scheme.{u}` |
| Affine | `[IsAffine S]` |
| Locally Noetherian | `[IsLocallyNoetherian S]` |
| Quasi-compact, hence Noetherian with the preceding condition | Affineness implies `CompactSpace S`; no additional assumption is required. |
| Every local ring is a normal domain | `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| An S-group scheme with multiplication, unit, inverse and their identities | `T : Over S` with `[GrpObj T]` |
| Fppf locally a finite product of G_m, with locally varying rank | `hT : IsRelativeTorus T`, whose definition quantifies over fppf covering families and finite ranks `r i : ℕ` |
| T → S affine | `IsAffineHom T.hom` |
| Smooth | `Smooth T.hom` |
| Of finite presentation | `LocallyOfFinitePresentation T.hom ∧ QuasiCompact T.hom ∧ QuasiSeparated T.hom`, exactly the recorded convention |
| A covering scheme and morphism | `∃ (S' : Scheme.{u}) (f : S' ⟶ S)` |
| Finite, etale, surjective | `IsFinite f ∧ Etale f ∧ Surjective f` |
| Hence finite flat locally finitely presented surjection | `f.IsFiniteLocallyFree`, together with `Surjective f`; this is the upstream class extending IsFinite, Flat and LocallyOfFinitePresentation |
| Finite disjoint union of components | `∃ (n : ℕ) (U : Fin n → S'.Opens) ...`, with closedness of every U, pairwise disjointness and `⨆ j, U j = ⊤` |
| Components normal | Domain and integral closedness of every stalk of `(U j).toScheme` |
| Integral and affine | `IsIntegral (U j).toScheme ∧ IsAffine (U j).toScheme` |
| Noetherian | `IsLocallyNoetherian (U j).toScheme ∧ CompactSpace (U j).toScheme` |
| Split on every component with rank r_j | `r : Fin n → ℕ`, and `Nonempty ((Over.map ((U j).ι ≫ f)).op ⋙ yonedaGrpObj T ≅ relativeSplitTorusFunctor (U j).toScheme (r j))` |

The last clause is an isomorphism of group-valued functors of points, exactly as in
the already reviewed relative-torus definition. For an S'_j-scheme V, its left side
is Hom_S(V,T), canonically Hom_{S'_j}(V,T ×_S S'_j). Its right side is the product
of r_j copies of Γ(V,O_V)^×. The local Laurent construction in the item has exactly
this functor of points: sending the Laurent coordinate to a unit and its inverse
is a bijection, restriction glues these bijections, and t ↦ t⊗t, 1, t⁻¹ give
multiplication, unit and inverse on units. Group-valued Yoneda therefore identifies
this natural isomorphism with precisely an isomorphism of the asserted group
schemes. It imposes no chosen basis, no arbitrary map and no extra structure on T.
There is no second definition of G_m or its split powers.

Likewise the finite clopen open decomposition is precisely a finite disjoint
union presentation: the canonical map from the coproduct of these open
subschemes to S' is an isomorphism. No extra connectedness, Galois condition,
componentwise surjectivity onto all of S, or fixed global rank is asserted.

Dependency declarations read and reused (names are in namespace AlgebraicGeometry
except the explicitly qualified general declarations):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme`, `Scheme.Hom`.
  Affineness is Mathlib `IsAffine` in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with `IsDomain`, in the prescribed inline stalk form.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `Scheme.fppfPrecoverage`, used by `IsRelativeTorus`.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `IsAffineHom`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `LocallyOfFinitePresentation`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- `def-weil-pbc-scheme-conventions`: convention record, no own declaration;
  finite presentation is the exact three predicates displayed above.
- `def-pc-finite-locally-free`: `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `Scheme.Hom.IsFiniteLocallyFree` (current source line 899, not its old recorded line 778).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`;
  its role in the Laurent model is represented by the existing units functor as explained above.
- `def-weil-laurent-polynomial-ring`: no lean record, but the usable `mathlib_match`
  is `LaurentPolynomial` in `Mathlib.Algebra.Polynomial.Laurent` (finite-support sums
  on integer exponents, defined for any semiring). No field assumption from the
  standalone Laurent discussion is imposed on this item's base rings.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `IsFinite`.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `Surjective`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; the actual restriction is
  expressed on functors of points by `Over.map`, so no auxiliary pullback group
  structure is chosen. `Over.pullback` uses `pullback.snd` as structure map.
- Added landed node `def-sfb-relative-torus`: `Sheaf.AlgebraicGeometry.RelativeTorus`,
  `IsRelativeTorus`, `relativeSplitTorusFunctor`; its full source and node record
  were read. These use Mathlib `CategoryTheory.GrpObj` and `yonedaGrpObj`.

All currently stated proof dependencies are imported. In particular these include
`FppfAffineRefinement`, `ProEtaleSiteComparison`, `ConstantSheafSectionsLocallyConstant`,
`NormalLocallyConstantFiniteSection`, `ProEtaleClassicalSheavesUnit`, and
`FiniteEtaleNormalGenericComponents`, whose current statements were read. Mathlib
Noetherian, Fpqc, Proetale, Limits and Prime.Topology supply the recorded Mathlib
proof matches. `lem-sfb-normal-locally-finite-components` and
`lem-sfb-relative-torus-character-reconstruction` currently have no usable Lean
record; their proof steps remain fully described in the docstring rather than
inventing prerequisites solely for a postponed proof. Neither is needed to type
the statement. No import cycle was introduced.

Edge cases checked before writing:

- Empty S: take S' = S and its identity; n = 0 gives an empty family of components.
  The coverage equality is then bottom = top on the empty scheme. There is no
  Nonempty S hypothesis. Integral components are only required at actual indices.
- Rank zero: both fppf-local ranks and the conclusion ranks use ℕ, allowing 0.
  `relativeSplitTorusFunctor S 0` is the empty product, hence the trivial group.
- Disconnected base: fppf covering ranks and the ranks of distinct output components
  may differ. Neither S nor S' is required connected or integral.
- Normality includes domain as well as integral closedness at each stalk.
- Finite presentation includes quasi-separatedness, as required by the convention.
- Every scheme and every test scheme uses the same arbitrary universe u; the finite
  index Fin n excludes no finite decomposition. The existing relative-torus covering
  uses Type u, which suffices by affine quasi-compact refinement on this base.

Searches made, using the required msearch wrapper:

- LeanFinder: `A torus over an affine normal Noetherian scheme splits over a finite etale surjective cover`.
  Eight hits (affine-space surjectivity and finite-presentation instances, Scheme.Etale,
  etale algebra descent, and general approximation); none is this theorem.
- Loogle: `"AlgebraicGeometry", "torus"`: zero hits.
- Mathlib grep: `torus|isotrivial|multiplicativeType`, AlgebraicGeometry: zero hits.
- LeanSearch: `A torus over a normal Noetherian affine scheme becomes a split torus after a finite etale surjective base change`.
  Eight hits on etale base change, Scheme.Etale, and algebraic descent; no torus theorem.
- Project `rg`: torus/group scheme definitions located `RelativeTorus.lean`, the
  field-only `ToriMultiplicativeType.lean`, and `GroupScheme/SplitTorusOverRing.lean`.
  The last is over Spec R; the arbitrary-base RelativeTorus interface is the one needed.
- `rg` of DAG definition nodes found the existing `def-sfb-relative-torus`; no new
  definition node is created. Exact item ID in WeilConjectures: no match. Exact new
  declaration name in Mathlib, WeilConjectures and Sheaf: no match before this delivery.
- The requested CompactObject example was opened: the current file is withdrawn and
  contains no declarations. The active FppfAffineRefinement module supplies the header
  conventions; the submitted module has source/blueprint and a six-step proof docstring.

Source verification: [Cesnavicius, arXiv:2201.06424v4, Appendix A.1](https://arxiv.org/html/2201.06424v4).
A.1.2 describes tori, A.1.8 gives finite etale splitting over locally Noetherian
geometrically unibranch schemes and explicitly lists normal schemes as examples.
The node's A.1.3 reference is a source-numbering imprecision, not a statement fault.
Its stronger component refinement is the explicitly specified affine Noetherian
specialization, proved by the accepted Stacks steps. No statement correction or
disputed statement is needed.

Validation: prescribed `scompile.py` compiled both its private sandbox check and the
actual library module without errors or warnings (2.7 s and 1.7 s respectively).
The only postponed proof is the named theorem above. All universes and variables
are explicit; autoImplicit and relaxedAutoImplicit are disabled.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
