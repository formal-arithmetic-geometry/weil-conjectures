## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceSurjectiveFlatClosedImmersion`
states `AlgebraicGeometry.AlgebraicSpace.isIso_of_surjective_of_flat_of_closedImmersion`.
Its sole proof is `sorry`; it introduces no definitions. The node is unchanged except
for its `lean` field. No new nodes, dependency repairs, or statement correction are needed.

I read Stacks `spaces-more-morphisms.tex`, `lemma-where-isomorphism`, Tag 05XD,
especially the final proof paragraph, and `morphisms.tex`,
`lemma-characterize-flat-closed-immersions`, Tag 04PW. The former reduces the claim
to representable surjective flat closed immersions of schemes; the latter supplies
the scheme input without finite presentation. The Lean docstring carries all four
DAG proof steps, including the local lift, singleton fibre, injectivity, gluing,
and naturality arguments.

The hypothesis and conclusion correspondence is:

- The scheme S is `{S : Scheme.{u}}`; `universe u` is explicit.
- X and Y are `{X Y : AlgebraicSpace S}`, the existing full subcategory of
  fppf sheaves with representable diagonal and representable surjective étale atlas.
  The morphism is `(i : X ⟶ Y)`, hence a natural transformation of these sheaves.
- Chartwise flatness is exactly `(hf : MapIsFlat i)`. Its definition applies
  `MapIsLocally (@Flat)` to every compatible pair of representable étale charts.
- Surjectivity on the field-valued point sets is
  `(hs : Function.Surjective (mapPoint i.hom.hom))`. The canonical `mapPoint`
  applies the natural transformation to field-valued representatives and descends
  to the existing common-field quotient, so this is the specified point map.
- Closed immersion is
  `(hc : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)`.
  Expanding the dependency definition: for every S-scheme T and h_T → Y there
  exist a representing S-scheme U, projection p : U → T, and a pullback square
  with X, with `IsClosedImmersion p.left`. This includes representability; no
  separate hypothesis or arbitrary replacement projection is used. Any other
  representative is uniquely isomorphic over T, so this states closed immersion
  on every scheme base change, as in the node.
- `IsIso i` says that this particular morphism admits a two-sided inverse in
  the category of algebraic spaces over S.
- Fibre products are the dependency's actual categorical sheaf pullbacks;
  `IsRepresentableWith` uses the equivalent Yoneda-presheaf pullback squares.
  No different fibre product or atlas choice is introduced in the statement.
- No finite-presentation, reducedness, Noetherian, or nonemptiness binder occurs.
  The size-convention node is metatheoretic: the explicit universe u uses the same
  scheme, fppf-sheaf and point universes as its recorded dependency interfaces.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`,
  `IsSurjective`, `IsAlgebraicSpace`. Their full signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally` and `MapIsFlat`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.PointRepresentative.map`, `pointImage`, `pointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: the canonical
  `AlgebraicSpace.mapPoint`, publicly available through the morphism-properties
  dependency. Its quotient construction was read and is reused, not restated.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. Imported publicly as a statement dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`:
  `AlgebraicSpace.point_open_calculus`, especially its representable-surjectivity
  equivalence, imported privately as a proof dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`:
  `AlgebraicGeometry.Flat.isIso_of_surjective_of_mono`, with Flat,
  QuasiCompact, Surjective and Mono hypotheses; closed immersion supplies the
  last required properties in the scheme application. Imported privately.
- `Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting`:
  `AlgebraicSpace.representable_etale_fppf_local_lifting`, imported privately.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, and the retained Mathlib sheaf
  interfaces specified by the dependency; imported privately for the sheaf-gluing
  steps. All recorded proof-dependency modules are included.

Edge cases checked mathematically before writing:

- Empty target: a morphism to it forces an empty source, and it is an isomorphism;
  the statement imposes no nonemptiness restriction.
- Empty source with nonempty target: point-surjectivity fails.
- Identity and isomorphism morphisms satisfy all three conditions, including
  over nonreduced or non-Noetherian bases.
- Spec k → Spec k[ε]/(ε²) is a surjective closed immersion but is not flat, so
  point-surjectivity does not silently erase the flatness requirement.
- A nonempty proper open immersion can be flat but is not point-surjective;
  a general surjective flat map is not necessarily a closed immersion. All
  hypotheses retain their intended mathematical content.

Searches actually run with `batch2/msearch.py`, group Q98 and this item:

- LeanFinder: `A surjective flat closed immersion of algebraic spaces is an isomorphism`:
  8 hits, headed by scheme-only `AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`
  (requires reduced target) and `AlgebraicGeometry.Flat.isIso_of_surjective_of_mono`.
  No matching algebraic-space theorem.
- Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.IsClosedImmersion`: 0 hits.
- LeanSearch: `A flat surjective representable closed immersion of algebraic spaces is an isomorphism`:
  8 hits, all relevant results concern schemes, not algebraic spaces.
- Mathlib grep through msearch, subdirectory AlgebraicGeometry:
  `isIso.*[Ff]lat|[Ff]lat.*[Cc]losedImmersion|[Cc]losedImmersion.*[Ff]lat|AlgebraicSpace`:
  11 hits, including `FlatMono.lean:25`; none states the algebraic-space result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `surjective.*flat.*closed|isIso_of.*[Ff]lat|[Ff]lat.*[Cc]losedImmersion|[Cc]losedImmersion.*[Ff]lat`:
  scheme and unrelated tensor results; the algebraic-space universal-isomorphism
  theorem's docstring mentions this missing input but does not state it.
- `rg` for the item id in `lean/WeilConjectures`: no match.
- `rg` for the proposed declaration name (and its `isClosedImmersion` variant) in
  Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration.

No statement dispute or node fault was found. Independent review is performed by
maintainer after direct worker delivery, as specified in the dispatcher brief.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Review fix (maintainer reviewer, 2026-10-24)

The surjectivity hypothesis `hs : Function.Surjective (mapPoint i.hom.hom)` used
`AlgebraicSpace.mapPoint`, owned by def-sfb-proper-curve-moduli, which is not a
stmt_dep of the item. The node says "surjective on the point sets of
[def-a1-space-point-topology]". The hypothesis is now `hs : pointImage i.hom.hom = Set.univ`,
with `pointImage` from that stmt_dep. The two forms are equivalent, since `pointImage f` is
the set of classes of `f(x)` for field representatives `x`, i.e. the range of `mapPoint f`.
The module docstring and proof step 1 were adjusted; nothing else changed. The fixed file
compiles cleanly with nt_compile (4.1 s).
