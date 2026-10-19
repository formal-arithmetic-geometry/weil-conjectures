## Worker report

The delivery states `lem-sf-normalized-derived-comparison-common-resolution` in
`Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution`. Its two theorems are
`CategoryTheory.Functor.normalizedDerivedComparison_commonResolution` and
`CategoryTheory.Functor.normalizedDerivedComparison_commonResolution_transition`.
Both proofs are `sorry`. Three helpers contain actual composites of existing canonical
isomorphisms and maps; none chooses an arbitrary comparison or contains postponed data.
The node changes only in `lean`. There are no new nodes, dependency repairs, or statement
corrections, and no statement dispute.

The source is `literature/stacks-project/derived.tex`, Tag 070Y,
`lemma-K-injective-defined` (read together with the following enough-K-injectives lemma).
As the node explicitly says, its normalized-comparison formula is an agent-written
naturality consequence, rather than a verbatim statement of Stacks. The docstrings carry
all four steps of the node's proof, including the transition calculation.

Hypotheses and clauses, in the order of the node:

- The four abelian categories are `A`, `A'`, `B`, `B'`, each with its own explicitly bound
  object, morphism, and derived-localization universe and its own `Category`, `Abelian`,
  and `HasDerivedCategory` instances. No universes are equated.
- Existence of arbitrary K-injective resolutions in A and A' is exactly `enoughA` and
  `enoughA'`: for every integer-indexed cochain complex, a quasi-isomorphism to some
  `I` with `I.IsKInjective`. The maps are not required to be monomorphisms. There are no
  enough-injectives or enough-K-injectives hypotheses on B or B'.
- Exact additive r and s are `r : A' ⥤ A`, `s : B' ⥤ B`, their `Additive` instances,
  and preservation of finite limits and finite colimits. Degreewise application is
  `mapHomologicalComplex (.up ℤ)` and their exact descents are `mapDerivedCategory`.
- The additive functors are `F : A ⥤ B`, `G : A' ⥤ B'` with `F.Additive` and
  `G.Additive`. No left exactness is imposed on F or G. Equality on objects and maps
  is `e : r ⋙ F = G ⋙ s`; equality of the functor-law proofs adds nothing by proof
  irrelevance. Lean writes composition in the order of application.
- RF and RG are precisely `rightDerivedFunctorOfQuasiIsoResolutions` applied to F,
  G and the respective enough-resolution hypotheses. Their units and resolution
  comparisons are those of the recorded dependency, not new choices.
- The supplied natural isomorphism is `β : r.mapDerivedCategory ⋙ RF ≅
  RG ⋙ s.mapDerivedCategory`. It is arbitrary subject to the stated normalization.
- `hFv` quantifies over every K-injective J, every K-injective T, and every
  quasi-isomorphism `v : r(J) ⟶ T`, and asserts `IsIso (Q.map (F.map v))`.
  This is exactly the invertibility clause in the normalization, not preservation
  of all quasi-isomorphisms by F.
- `hnormalized` has the same universal quantifiers. Its left side is `c_v.inv`,
  the comparison at J, s applied to `c_(identity J).hom`, and the canonical endpoint
  identification. The recorded definition gives `c_(identity J) = eta_J inverse`,
  with the Q versus quotient-followed-by-Qh presentation isomorphisms. Thus this is
  exactly `(s eta_J)^(-1) beta_J (c_v)^(-1) = Q(Fv)^(-1)`, with all of the
  node's understood localization identifications inserted. The inverse on the
  right is `@CategoryTheory.inv ... (hFv J T v)`, so its instance is precisely
  the supplied invertibility proof. `include hnormalized` retains normalization
  in both theorem signatures; temporary `#check @...` probes verified this.
- Arbitrary N and the successive resolutions are `u : N ⟶ J`, `v : r(J) ⟶ T`,
  with `[J.IsKInjective]`, `[T.IsKInjective]`, `[QuasiIso u]`, `[QuasiIso v]`.
  The composite w is literally `(r.mapHomologicalComplex (.up ℤ)).map u ≫ v`.
  Mathlib infers its quasi-isomorphism from exactness of r and composition.
- The main conclusion is equality of `normalizedDerivedComparisonResolutionMap ... u v`
  with `Q(Fv)^(-1)`. Unfolding that helper gives `c_w.inv ≫ beta_N ≫ s(c_u).hom`,
  inserting the canonical r and s localization identifications. Its domain is Q(FT)
  and its codomain is Q(F(rJ)), identified with Q(s(GJ)) by e. These are the node's
  exact endpoints.
- `normalizedDerivedComparisonComplexIso` transports beta along the inverse of
  `r.mapDerivedCategoryFactors.app N` under RF. This is the canonical identification
  of RF(r_D(QN)) with RF(Q(rN)).
- `normalizedDerivedComparisonTargetIso` first applies Q to the complex isomorphism
  induced by `eqToIso e`, then uses the inverse of
  `s.mapDerivedCategoryFactors.app (G(J))`. It identifies Q(F(rJ)) with s_D(Q(GJ)).
- The final compatibility clause is the transition theorem, for two completely
  arbitrary pairs `(u₁,v₁)` and `(u₂,v₂)` resolving the same N. It asserts
  `Q(Fv₂)^(-1) = d_F.inv ≫ Q(Fv₁)^(-1) ≫ d_G.hom`.
  Here d_F is exactly `F.kInjectiveDerivedResolutionTransition enoughA w₁ w₂`,
  and d_G is `s.mapDerivedCategory.map` of the recorded G transition, conjugated
  by the canonical endpoint identifications. In the node's functional composition
  notation this is `L₂ = d_G L₁ d_F^(-1)`. The existing transition-laws theorem
  supplies inverses and the cocycle, so this is compatible with three or more choices.
- There is no `IsKInjective` hypothesis on r(J) anywhere. All complexes are unbounded.

Dependencies used, after reading their recorded declarations and docstrings:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (through the imports).
- `def-sp-left-exact-additive`: its recorded component `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`; the node uses only additivity.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-sfb-right-derived-functor`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and
  `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`,
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- `lem-weil-pbc-exact-functor-derived-factorization`:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `lem-sf-kinjective-derived-map-computation`:
  `CategoryTheory.Functor.kInjectiveDerivedResolutionTransition` and its computation,
  laws and naturality statements,
  `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`. This module is imported
  publicly since the compatibility signature itself uses the transition.

Edge cases checked by reading the composites and their types:

- `u = identity` on a K-injective J reduces the formula to the supplied normalization,
  since w = v and the identity-resolution comparison is the inverse derived unit.
- `v = identity` when r(J) happens to be K-injective gives the identity map after
  transporting the endpoint by e. The general statement never assumes this case.
- `r = s = identity`, `F = G`, and beta the identity recover the usual resolution
  computation and the transition naturality square.
- Coincident resolution choices give identity source and target transitions; the
  compatibility equation becomes reflexivity.
- Zero complexes, zero additive functors, and zero abelian categories are allowed.
  A zero object has an invertible identity, so no nonzero assumption enters.
- Acyclic N and a non-monic quasi-isomorphism into the zero complex are allowed.
  There are no boundedness, monomorphism, or termwise-injectivity restrictions.
- Different object, morphism and localization universes remain independent in the
  elaborated signatures, confirmed by temporary `#check` probes (removed from delivery).

Searches made before writing:

- `msearch.py` LeanFinder: "A natural comparison of total right derived functors
  normalized on K-injectives is computed on successive K-injective resolutions".
  Eight hits, including `InjectiveResolution.rightDerived_app_eq`,
  `NatTrans.rightDerived`, `Functor.rightDerived_map_eq`, and
  `InjectiveResolution.isoRightDerivedToHomotopyCategoryObj`. These concern ordinary
  object resolutions or a derived transformation, not the supplied normalized
  unbounded comparison with two successive resolutions.
- `msearch.py` Loogle: `"rightDerivedFunctorComparison_fac_app"`. Two hits,
  `LocalizerMorphism.rightDerivedFunctorComparison_fac_app` and its reassociation.
  Read `Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseRightDerived`
  lines 35--83: this is a canonical comparison with a fixed target and universal
  property, not the arbitrary supplied beta and normalization of this node.
- `msearch.py` LeanSearch: "Normalized comparison between derived functors evaluated
  on successive K-injective resolutions". Eight ordinary injective-resolution hits,
  including `isoRightDerivedObj_hom_naturality_assoc` and `rightDerived_map_eq`;
  no exact match.
- `msearch.py` grep, CategoryTheory:
  `rightDerivedFunctorComparison_fac_app|normalizedDerivedComparison`.
  Only the two lines of PointwiseRightDerived described above.
- `rg` on the upstream `WeilConjectures` tree for
  `normalized.*[Cc]omparison|commonResolution|common_resolution`, followed by
  `lem-sf-normalized-derived-comparison-common-resolution|normalizedDerivedComparison`:
  no matching declaration. The broad search gives unrelated purity comments.
  A further `rightDerived` search in its CategoryTheory tree gives objectwise,
  bounded-below, and endofunctor comparisons, not this statement.
- `rg` on project `lean/Sheaf` for the same broad normalized/common-resolution pattern:
  unrelated geometric and scalar comparisons; no exact statement. The recorded
  K-injective computation and arbitrary-resolution right-derived modules are reused.
- `rg` on `dag/lean_names_upstream.json`, upstream sources, and project CategoryTheory
  for the item id and `normalizedDerivedComparison`: no existing binding for this item
  or collision for the new declaration names before writing.

Validation: file-only compilation through `scompile.py` passed cleanly, with both sandbox
and library-path checks. Temporary signature probes confirmed every hypothesis, especially
normalization, in both theorem types. They have been removed. The delivery dry run and
final delivery recompile the final module and run the maintainer's preflight.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
