## Worker report

The module `Sheaf.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase` states
`AlgebraicGeometry.Etale.sfEtaleUnitTensorArbitraryBase`, with three real-data helper
maps belonging to this node. Its only postponed theorem is the named main theorem,
whose proof is `sorry`; its docstring contains all five proof steps of the DAG node.
The node is unchanged outside `lean`. No statement correction, disputed statement,
new node, dependency repair, or arbitrary choice of a comparison is needed.

Hypothesis-by-hypothesis correspondence:

- A finite commutative ring is `A : Type (u + 1)` with `[CommRing A] [Finite A]`.
  No nontriviality or characteristic assumption is imposed.
- Arbitrary schemes are `{V W : Scheme.{u}}`; the morphism is `e : V ⟶ W`.
  `[Etale e]` is the recorded Mathlib notion of etale, and `[IsSeparated e]`
  is the recorded closed-diagonal definition of separatedness.
- The supplied open-then-proper factorization is `c : Compactification e`.
  Its `i`, `g`, `comm`, `isOpenImmersion`, and `isProper` are the specified data.
  In particular `Compactification` imposes no quasi-compactness on `i`.
- The ordinary unbounded categories are `DerivedCategoryModule A W` and
  `DerivedCategoryModule A V`, namely derived categories of small-etale sheaves
  valued in `ModuleCat.{u + 1} A`. Neither a plus nor a bounded subcategory occurs.
- `F_e` is `rightDerivedLowerShriekOfCompactification (ModuleCat A) c`.
  `G` and `adj : F_e ⊣ G` select any right adjoint furnished by
  `sfEtaleAmbientAdjointProjection A c`. These arguments name the adjunction already
  specified in the node; they impose no new geometric hypothesis or existence demand.
  Its actual counit is `adj.counit`.
- `A_W` and `A_V` are `constantComplex A W` and `constantComplex A V`;
  omega is the explicit expression `G.obj (constantComplex A W)`.

Conclusion-by-conclusion correspondence:

- `sfEtaleRightAdjointComparison` is rho, a natural transformation `G ⟶ E`, where
  `E = (upperStar (ModuleCat A) e).mapDerivedCategory`. It is constructed by
  `conjugateEquiv adj (derivedEtaleLowerShriekMapAdjunction (ModuleCat A) e)`
  applied to the upstream `compactificationEtaleComparison A e c`. This comparison
  is the specified clopen-graph construction, not an arbitrary map or an existence
  choice. The first conjunct `IsIso rho` makes it the required natural isomorphism.
- The next conjunct, for every K, is exactly
  `S.map (rho.app K) ≫ ev.app K = a.app (G.obj K) ≫ adj.counit.app K`, with
  `S = (etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory`,
  `ev = (derivedEtaleLowerShriekMapAdjunction (ModuleCat A) e).counit`, and
  `a = compactificationEtaleComparison A e c`.
  This is the requested evaluation-counit normalization, in Lean's composition order.
- `sfEtaleRightAdjointUnit` is precisely `rho.app A_W ≫ u_e.hom`, using
  the existing `etaleSumPullbackUnitIso A e` for `u_e`. No replacement unit is chosen.
- The third conjunct ranges over every unbounded K and states
  `sfEtaleExactAmbientTensorMap ... K ≫ rho.app K =
    ((derivedTensor ... V).map eta).app (E.obj K) ≫
      (derivedTensorLeftUnitor ... V (E.obj K)).hom`.
  This is the displayed identity rho_K theta_K = lambda_(E K) (eta tensor 1).
  Mapping eta by the curried tensor functor leaves the second tensor factor unchanged.
- The helper `sfEtaleExactAmbientTensorMap` is the original recorded
  `sfEtaleAmbientTensorMap A c G adj K` precomposed with tensoring the inverse of
  `leftDerivedUpperStarIsoMapDerivedCategory` at K. Thus its domain is omega tensor
  E K. The original theta uses omega tensor L(e*) K. The transport inserts exactly
  their canonical identification, and preserves the actual counit-defined theta.
- `IsIso (sfEtaleRightAdjointUnit ...)` says the specified eta identifies omega with
  A_V. It gives the node's particular conclusion omega is isomorphic to A_V via
  `asIso eta`, rather than just some unspecified isomorphism.
- The last conjunct asserts `IsIso (sfEtaleAmbientTensorMap A c G adj K)` for every K,
  retaining invertibility of the original map defined in the ambient dependency.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separatedness import:
  `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`.
- `Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection`:
  `AlgebraicGeometry.Etale.sfEtaleAmbientAdjointProjection` and
  `AlgebraicGeometry.Etale.sfEtaleAmbientTensorMap` (the actual transpose).
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek`, its exactness and evaluation adjunction.
- `WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange`:
  `AlgebraicGeometry.Etale.derivedEtaleLowerShriekMapAdjunction`, the exact
  sum/evaluation adjunction, as distinguished from its transported left-derived form.
- `WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification`:
  `AlgebraicGeometry.Etale.compactificationEtaleComparison`, whose full construction
  uses `compactificationEtaleGraphMap`, `compactificationEtaleUnit`, the clopen graph,
  proper base change, and the adjunction transpose. Its signature has no
  quasi-compactness or Noetherian restriction.
- `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence`:
  `AlgebraicGeometry.Etale.etaleSumPullbackUnitIso`. Only this unrestricted unit
  comparison is used; its older quasi-compact support/right-adjoint isomorphisms
  are not used.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`; and the canonical
  `leftDerivedUpperStarIsoMapDerivedCategory` exposed by the dependencies.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.conjugateEquiv`.
- The additional plain proof imports retain the stated DAG proof interfaces:
  termwise homotopy adjunction, exact derived factorization, localization,
  the canonical ringed-topos tensor comparison, ringed monoidal comparisons,
  and `CategoryTheory.Adjunction.unitAdjunctTensorAction`.
  The graph/projection proof node `lem-sf-etale-graph-projection-arbitrary-base`
  has no recorded declaration, so there is no corresponding module to import.
  The map itself is already constructed upstream, so no missing statement object
  needs to be supplied for this delivery. Its graph/projection compatibility remains
  a proof obligation for that proof node, named explicitly in the docstring.
  The upstream graph-comparison-isomorphism module is also imported for the proof.

Edge cases checked before writing and in the final reading:

- The zero ring remains admitted: no `[Nontrivial A]` or invertible exponent binder.
- Empty schemes, identity maps, and the zero derived object remain admitted.
- Unbounded complexes in both directions are allowed by the category itself.
- An arbitrary open immersion e has the factorization e followed by identity;
  neither e nor c.i carries a quasi-compactness assumption.
- Non-Noetherian and non-quasi-separated bases are not excluded.
- Independent selected right adjoints are allowed, with the comparison determined
  by their actual adjunction counits. No arbitrary equivalence data are assumed.
- The tensor and unitor use upstream `derivedTensor` and `derivedTensorLeftUnitor`,
  avoiding a second concrete monoidal-instance definition.
- Every universe and variable is explicit, with `set_option autoImplicit false`.

Searches made (2026-10-22):

- msearch LeanFinder: “For separated etale morphisms of arbitrary schemes the
  exceptional inverse image is canonically ordinary pullback compatibly with
  evaluation counit and the dualizing tensor unit”. Eight hits on scheme module
  pseudofunctor unit laws and scheme pullback formulas; no statement match.
- msearch Loogle: `"Adjunction", "conjugate"`. Eight hits on general adjunction
  mates, including `conjugateEquiv_adjunction_id`; these support the construction
  but do not state the geometric normalized tensor identity.
- msearch grep of Mathlib: `etaleLowerShriek|EtaleSmoothDuality|sfEtaleUnitTensor`.
  Zero hits.
- msearch LeanSearch: “The canonical tensor morphism for the etale exceptional
  inverse image is the unitor after the coefficient unit isomorphism”. Eight hits
  on abstract monoidal unit laws; no statement match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for etale right-adjoint/unit and
  `sfEtale` names found the ambient statement and the older
  `EtaleSumRightAdjointCoherence` interfaces, whose support and rho isomorphisms
  impose quasi-compactness. Those cannot replace this node's arbitrary-open case.
- rg of upstream found `EtaleSmoothDuality` in `Derived/SmoothDuality/Charts.lean`:
  it is a predicate concerning a chosen global exceptional inverse image and
  lacks the present evaluation normalization equation. It is not this theorem.
- rg of upstream graph declarations found `compactificationEtaleComparison` and
  `isIso_compactificationEtaleComparison`; these give the canonical graph map and
  its invertibility without quasi-compactness, but not the tensor identity.
- rg of all four proposed full declaration names in both source roots returned
  no pre-existing declarations. rg of the item id under `WeilConjectures` found
  no existing attachment.

Validation: scompile.py compiled the module as both sandbox and library module,
cleanly (19.3 s and 20.7 s). The only theorem proof is `sorry` as required.

## Second reading by Q86

A separate pass reread the complete node statement, its five proof steps, the
ambient theta signature and body, the sum-extension definition and exact adjunction,
the upstream graph-map construction, the unit comparison, and the final Lean file.
This was a self-review; the dispatcher prohibits starting other agents and the
maintainer performs the independent delivery review.

The finite commutative ring, arbitrary schemes, separated etale morphism, supplied
open/proper compactification, ordinary unbounded categories and selected actual
adjunction all have the matching binders described above. Every conclusion is
present: natural invertible rho, the evaluation-counit equation, eta with the
canonical pullback unit, the normalized tensor equality for all K, invertibility
of eta, and invertibility of the original ambient theta. The explicit exact/derived
domain transport is necessary because the ambient dependency states theta using
left-derived pullback; it does not change theta or introduce another comparison.
The rho definition uses the canonical upstream graph map and the exact evaluation
adjunction, so no mere existence of endpoint isomorphisms substitutes for the
normalization. No mismatch requiring a statement correction was found. No
hypothesis, definition, or conclusion was changed during this reading.
