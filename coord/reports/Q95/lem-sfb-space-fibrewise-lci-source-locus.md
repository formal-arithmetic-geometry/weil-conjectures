## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFibrewiseLciSourceLocus` states the node in
`AlgebraicGeometry.AlgebraicSpace.exists_fibrewiseLci_open_baseChange`. Its only theorem
has proof `sorry`. The helper `HasCompleteIntersectionFibresToScheme` has actual data:
it universally tests the existing scheme `Scheme.Hom.HasCompleteIntersectionFibres`
on representable etale charts. There is no chosen atlas, arbitrary replacement map,
new algebraic-space definition, or postponed construction.

Hypothesis and clause correspondence:

- The node's scheme S is `T.left`, with `T : Over B`; `B : Scheme.{u}` is the ambient
  base for the presheaf presentation. `X : AlgebraicSpace B` and
  `f : X.obj.obj ⟶ yoneda.obj T` are precisely the algebraic space and its specified
  morphism to that scheme. This adds no geometric condition: the original situation
  can always be presented with `B = S`, `T = Over.mk (𝟙 S)`. Allowing an arbitrary
  ambient base just permits the same situation to retain an existing presentation.
- Flatness is `hflat : MapToSchemeIsLocally (@Flat) X T f`. Local finite presentation
  is `hfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f`. These are
  the existing universal representable etale chart tests, with the canonical scheme
  morphism recovered by `yoneda.preimage (a ≫ f)`.
- The universes are explicitly `u`, `Scheme.{u}`, `Type u` and `Over B`; no implicit
  universe or variable is auto-bound. Test schemes and residue fields are in the
  same universe as the original algebraic-space interface.
- `∃ A : OpenSubspace X` supplies the source open. Its fibre condition is
  `HasCompleteIntersectionFibresToScheme T (A.val.ι ≫ f)`. Expanded, this requires
  each local ring of every fibre of every representable etale scheme chart of A
  to be the recorded complete-intersection local algebra over that residue field.
  Since chart maps are locally of finite presentation and hence locally of finite
  type, `lci_pointwise_criterion` identifies this condition with precisely the
  node's affine open cover by spectra of finitely generated local-complete-
  intersection algebras. The etale-invariance proof dependency identifies testing
  one covering family with testing every chart. This is the local-ring rendering
  already used by the recorded scheme locus, not a different lci notion.
- Largestness is `∀ C : OpenSubspace X, HasCompleteIntersectionFibresToScheme T
  (C.val.ι ≫ f) → C ≤ A`. There are no extra flatness or finiteness hypotheses on C.
- For every representable etale chart `a : yoneda.obj V ⟶ X.obj.obj`, the equation
  `schemePointMap a ⁻¹' pointImage A.val.ι =
  (yoneda.preimage (a ≫ f)).left.fiberCompleteIntersectionLocus` is exactly the
  underlying-open equality in the chart. An open subspace's inverse image is an
  open subscheme by its defining scheme test; open subschemes are determined by
  their point subsets with the restricted structure sheaf. Thus this is equality
  of the specified opens, not merely an isomorphism of abstract schemes.
- A scheme morphism `g : T' ⟶ T` in `Over B` is an arbitrary scheme base change:
  any scheme map to `T.left` acquires its map to B by composition. The presheaf
  `Limits.pullback f (yoneda.map g)` is exactly X ×_S T', using the recorded fibre
  product, and `Limits.pullback.snd` is the base-changed structure morphism.
- The first base-change conjunct says, for every etale scheme chart of that actual
  pullback, both `Flat` and `LocallyOfFinitePresentation` of the canonical chart map.
  This is the same chartwise meaning as the hypotheses, including every chart.
- The next conjunct says that the literal subfunctor preimage
  `A.val.preimage (Limits.pullback.fst f (yoneda.map g))` is representable by open
  immersions. The following conjunct gives its fibre condition and the final
  universal implication gives its largestness among all open subfunctors of X_T.
  Consequently it is U_(f_T), and the asserted equality U_(f_T) = U_f ×_S T is
  rendered without choosing an otherwise arbitrary name for the unique largest
  open. Largestness determines it uniquely by antisymmetry of subfunctor inclusion.
- The final equivalence `A.val = ⊤ ↔ HasCompleteIntersectionFibresToScheme T f`
  is exactly U_f = X iff every fibre is a local complete intersection.
- No properness, closedness, quasi-compactness, separation, nonemptiness, global
  finite presentation, or field perfection hypothesis occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsRepresentableWith` and the representable-diagonal/atlas definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, including its stalkwise meaning.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` and its base-change permanence.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; actual presheaf `Limits.pullback` is used.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` and its order.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`, with the
  existing `schemePointMap` from its point-classes dependency.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection`, `Algebra.IsLocalCompleteIntersection`.
- `Sheaf.TraceFormula.SyntomicLocusBaseChange`:
  `Scheme.Hom.IsCompleteIntersectionAtFiberPoint`, `fiberCompleteIntersectionLocus`,
  `HasCompleteIntersectionFibres`, and `syntomic_locus_base_change`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsLocally`. Its already
  landed owning node `def-sfb-proper-curve-moduli` was added to `stmt_deps` solely
  to cite this existing canonical chart test. None of the curve/properness notions
  in that module enters the statement. No dependency module or new node is needed.
- Proof imports also retain `point_open_calculus`, `lci_etale_pointwise_invariance`,
  `local_properties_chart_test`, `etale_open_chart_morphism_descent`,
  `lci_pointwise_criterion`, and the Mathlib scheme permanence module, as requested
  by the node's proof plan. The size-convention node is rendered by the explicit
  universes; it has no declaration to import.

Edge cases checked before and after writing:

- Empty X: its unique open is greatest; chart and fibre tests are vacuous, including
  empty scheme charts, and base change remains empty.
- Empty individual fibres: `∀ y : f.fiber s` imposes no condition on an empty fibre.
- Entire lci family: the final equivalence makes A the full subfunctor; restriction
  to an arbitrary open does not introduce a properness assumption.
- A family with a non-lci fibre point: the chart equality excludes that point and
  does not silently replace a mixed fibre by an all-or-nothing base locus.
- Identity base change, open restrictions, arbitrary nonflat base changes and maps
  from field spectra are all included by `∀ T' g`; no flatness is imposed on g.
- The zero algebra and empty affine spectra are permitted by the recorded algebra
  definitions, which explicitly include the zero ring convention.

Searches (all through the prescribed tools or read-only paths):

- msearch LeanFinder: “For a flat locally finitely presented algebraic space over a
  scheme the fibrewise complete intersection locus is open and commutes with base
  change”. Eight hits: scheme universal openness and flatness/pullback properties;
  none states this algebraic-space lci source locus.
- msearch Loogle: `AlgebraicGeometry.AlgebraicSpace,
  Algebra.IsLocalCompleteIntersection, AlgebraicGeometry.syntomic_locus_base_change`.
  Zero hits; Mathlib does not know the project AlgebraicSpace identifier.
- msearch LeanSearch: “Complete intersection fibres for an algebraic space tested
  on etale scheme charts with largest open locus”. Eight hits, about etale loci,
  scheme etale sites and Jacobson/quasi-separated spaces; no matching statement.
- msearch Mathlib grep: `syntomic|fiberCompleteIntersection|FibrewiseLci` in
  AlgebraicGeometry: zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: syntomic and complete-intersection
  searches find the existing ring lemmas and scheme locus. The space nodal locus
  is a different statement and predicate. No space complete-intersection-fibres
  predicate or theorem matching this node was found.
- Exact item-id grep in `lean/WeilConjectures`: no hits. Exact searches for the two
  proposed declaration names in both libraries and `dag/lean_names_upstream.json`:
  no hits. The stage-2 example module has been withdrawn; its recorded upstream
  `WeilConjectures.CategoryTheory.CompactObject` was read for the current header.

Sources read locally: spaces-more-morphisms.tex, lemma-base-change-lci-fibres
(Tag 06CA) and lemma-flat-lci (Tag 06C9), plus the recorded full dependency
signatures and docstrings, including the local-ring/affine-cover equivalence.
There is no statement correction or disputed mathematical clause.

Validation: scompile.py compiled the delivered module on the server in both its
sandbox and library positions, 1.9 seconds each, with no errors or unexpected warnings.

## Second reading by Q95

I reread the node and final file in a separate pass in this single-worker session;
the maintainer's independent delivery review remains the independent review.
The two input hypotheses are the original chartwise flatness and local finite
presentation. The conclusion supplies the open's fibre property, its largestness,
the inverse-image chart equality, base-change flatness/lfp, the literal pulled-back
open's largestness, and the full-source equivalence. I checked that largestness
quantifies over all source opens, not just already syntomic ones, and that g has no
extra hypothesis. The use of local rings instead of writing the affine covers
inline is justified by the existing pointwise criterion and the chartwise lfp
hypothesis; it does not drop finite generation. Point equality specifies the
actual restricted open subscheme. The ambient base B is separate from the target
scheme T.left, so arbitrary base changes remain present. No mismatch or correction
was found on this rereading. No other agent was started, as instructed.
