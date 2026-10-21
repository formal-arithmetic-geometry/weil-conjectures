## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison` states
`AlgebraicGeometry.Etale.ChartAdjointComparison.exists_homEquiv`. Its sole postponed proof
is `sorry`. The six preceding definitions contain real data: they assemble the canonical
compact-support normalizations, the bounded-below left comparison, its ambient value,
and the specified forward Hom chain. They are helpers belonging to this node's comparison,
listed in `lean.declarations`; they introduce no independent notion requiring a new node.
The natural-language statement, dependencies and proof plan are unchanged.

Hypothesis and clause correspondence:

- A finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The coefficient category is always `ModuleCat.{u + 1} A`; all five scheme sites use
  the standard ordinary-etale encoding. Any finite coefficient ring can be lifted to
  this size convention; there is no characteristic or nonzero-ring restriction.
- Five Noetherian schemes: `{X Y U V P : Scheme.{u}}` and the theorem's five
  `[IsNoetherian ...]` binders. Mathlib's `IsNoetherian` is local Noetherianity plus
  compactness, equivalent to a finite affine cover with Noetherian coordinate rings.
- Displayed maps: `f : X ⟶ Y`, `s : U ⟶ X`, `v : V ⟶ Y`, `i : U ⟶ P`,
  `p : P ⟶ V`; `[IsOpenImmersion s]`, `[IsOpenImmersion v]`, `[IsClosedImmersion i]`.
- Equality of factorizations: `w : s ≫ f = i ≫ p ≫ v` is exactly `fs=vpi`.
- Separated finite type: the explicit `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact` instances for `f,p`, and `QuasiCompact` for `s,v`. Open immersions
  are separated and locally of finite type. Closed immersions are finite, hence
  proper, separated and of finite type. Composition preserves these properties,
  so every displayed composite has the required properties without an extra
  hypothesis or a restriction on the choice of factorization.
- Compactifiability: the `HasCompactification` binders cover `f,s,v,i,p`, `s ≫ f`,
  `i ≫ p`, and both parenthesizations of `i ≫ p ≫ v` used by the canonical compositors.
  These are the source's compactifiable displayed maps and composites. Other
  subcomposites are compactifiable by Nagata under the stated finite-type,
  separated, Noetherian hypotheses. The duplicate parenthesizations simply provide
  the typeclass transports required by the existing API.
- The ordinary unbounded derived categories are `DerivedCategoryModule A T`,
  definitionally `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat A))`.
  `R(f)_!`, `R(p)_!` and `R(i)_!` are the existing chosen-compactification functors.
- Right adjoints are the chosen functors `F`, `G`, `I`, with `adjF`, `adjP`, `adjI`
  the actual ambient adjunctions. These render the node's stipulated right adjoints
  `f^times`, `p^times`, `i^times`; they are not arbitrary maps or extra existence
  assumptions. The existing exceptional-adjoint theorem supplies such choices.
  Quantifying over these data retains their actual Hom bijections, rather than
  choosing a new incompatible adjunction by uniqueness.
- K is completely arbitrary: `K : DerivedCategoryModule A Y`.
- B is written explicitly as `I.obj (G.obj (D((v)^*[ModuleCat A]).obj K))`.
  No extra object, identification, or boundedness hypothesis is substituted for B.
- H is any object of `DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat A))`.
  This is the full subcategory of all ambient objects with cohomology bounded below;
  `H.obj` is its ambient object. All morphisms between these tests are retained.
- The asserted bijections are the family `e H K` from `Hom(H,B)` to
  `Hom(H,D(s^*)(F K))`. The equality `(e H K).symm = homChain ... H K` says exactly
  that they are the inverse of the specified chain. As equivalences they include
  both inverse identities, without requiring separate tautological conjuncts.
- Naturality in H is the second conjunct: for every `a : H' ⟶ H`, applying `e`
  commutes with precomposition by `DerivedCategory.Plus.ι.map a`.
- Naturality in K is the third conjunct: for every `a : K ⟶ K'`, applying `e`
  commutes with postcomposition by `I.map (G.map (D(v^*).map a))` on B and
  `D(s^*).map (F.map a)` on the other target.
- Neither target is assumed bounded below: F, G and I have unbounded codomains,
  and only the test H has the Plus type. No Plus-valued exceptional functor is used.

The chain and its normalization are explicit, not an arbitrary isomorphism:

1. `openNormalization` compares the chosen compactification of j with `(j,id)`
   using `derivedPlusFormalism.shriekIso`, then removes the identity direct image
   with `pfId`. It has direction `Rj_!+ ≅ D+(j_!)`.
2. `closedNormalization` compares the chosen compactification of i with `(id,i)`,
   removes the identity open extension with `shId`, and uses the canonical
   `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` for the exact i_*.
3. `leftComparisonPlus` first inverts the s normalization, applies alpha(f,s),
   transports along w, inverts alpha(v,pi), then inverts alpha(p,i), and finally
   normalizes i and v. Thus its direction is exactly
   `Rf_! s_! H ≅ v_! Rp_! i_* H`, with the prescribed canonical alpha maps.
   The associativity transport of the scheme morphisms is explicit.
4. `leftComparison` passes this D+ comparison through Plus.ι using
   `rightDerivedLowerShriekPlusCompatibility` at f and p. Exact-functor Plus
   compatibility is definitionally the identity, so the open extensions and i_*
   retain their ambient degreewise meanings. No unbounded compact-support
   compositor or arbitrary Nonempty isomorphism is substituted.
5. `homChain` composes, in order: the inverse open s transpose; the inverse adjF
   transpose; precomposition by `leftComparison.inv` via `Iso.homCongr`; the
   forward open v transpose; the forward adjP transpose; precomposition with
   `closedNormalizationAmbient.hom`; and the forward adjI transpose. The last
   two arrows are precisely the normalized `Hom(i_*H,p^times v^*K) ≅ Hom(H,B)`.
6. `exists_homEquiv` specifies the inverse of this chain and its naturality.
   Its docstring contains all six natural-language proof steps, with the DAG
   dependencies and source places, for stage 3.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus`
  and `DerivedCategory.Plus.ι` for the recorded derived-category dependency.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, `rightDerivedLowerShriek`,
  `rightDerivedLowerShriekPlus`, `rightDerivedLowerShriekPlusCompatibility`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `rightDerivedLowerShriekPlusCompIso`, `rightDerivedLowerShriekPlusCongr`;
  `derivedPlusFormalism` and its `shriekIso`, `pfId`, `shId` identify exactly the
  canonical compositors and normalizations, not another copy.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`, the recorded
  ambient exceptional-adjoint theorem. The current source proves this more
  generally without Noetherianity; the stipulated adjunction data are used here.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `upperStar`, `lowerStar`, and their coefficient-general signatures, specialized
  to ModuleCat A, for the recorded inverse/direct images.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek` and its exactness/adjunction API.
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction` on the whole ambient categories.
- `WeilConjectures.SixFunctors.Finite.Exact`:
  `preservesFiniteColimits_lowerStar_of_isFinite`, the recorded finite exactness
  interface, specialized to ModuleCat A. The induced exactness enables the canonical
  `CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`.
- Mathlib's `Scheme`, `IsOpenImmersion`, `IsClosedImmersion`, `IsProper`,
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsNoetherianRing` and
  `IsNoetherian`: the recorded geometric definitions; no private replacement.
- Proof-only imports retain the recorded
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`,
  `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` and
  `Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement`.
  These supply the prescribed alpha normalization, ordinary-etale unbounded open
  adjunction, and agreement with the specified sum adjunction. Closed properness,
  finite-ness and open-etaleness are Mathlib instances available through these imports.

Edge cases checked before writing: H=0; K=0; the zero coefficient ring; empty U
(and empty charts elsewhere when the displayed maps exist); all morphisms identities;
nontrivial open/closed charts; arbitrary negative lower bounds for H; K and the two
representing objects not bounded below. All have exactly the same types in the statement.
For identity charts the canonical compositors specialize to their unit laws and the Hom
chain specializes to the ordinary adjunction identities. No assertion about an isomorphism
of representing objects is inferred from the bounded-below tests.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query: "Natural Hom bijections for exceptional inverse image
  on a factored open chart using compact support composition on bounded below complexes".
  Eight hits, all `ComplexShape.Embedding` Hom/lift-extend results; no match.
- `msearch.py loogle`, query: `"Adjunction", "homEquiv"`.
  Twelve hits, including `CategoryTheory.Adjunction.homEquiv`, `homEquiv'`,
  `mkOfHomEquiv`, and the core Hom equivalence structures. These supply categorical
  vocabulary, not the chart statement or its canonical compact-support normalization.
- `msearch.py grep`, query: `upperShriek|exceptional.*[Aa]djoint|compactSupport`,
  subdirectory `CategoryTheory`: zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `etaleChartAdjoint` and `chartAdjointComparison`: no match.
  A broader chart/comparison search found unrelated affine-coordinate and section-arrow
  comparisons. Searching `dag/lean_names_upstream.json` for the node id found none.
- Read the actual source/docstrings of the recorded dependency declarations, the
  canonical LowerShriekComposition and normalization APIs, the blueprint source,
  and the withdrawn CompactObject example plus its current upstream replacement.
  No repair note exists for this item. No exact existing statement was found.

Validation: `scompile.py N0 lem-sf-etale-chart-adjoint-comparison` compiled this module
in both sandbox and its actual library module namespace, with no warnings or errors
(7.8 s and 9.2 s). An initial diagnostic required explicitly supplying
`HasCompactification ((i ≫ p) ≫ v)` as well as the right-associated spelling;
this was repaired within the existing compactifiable-composites hypothesis.
There is no statement dispute, correction, dependency repair, or new DAG node.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
