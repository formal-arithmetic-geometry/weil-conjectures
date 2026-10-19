## Worker report

The module `Sheaf.Paper.StandingExceptionalComposition` defines
`AlgebraicGeometry.ProEtale.standingExceptionalComposition`, the specified morphism
c_{g,f,L}. Its helper `standingExceptionalHomEquiv` exposes the exact normalized Hom
bijection needed to calculate the mate. Both declarations have real definitions;
there are no theorems, axioms or sorry terms in the delivered module. The node is
unchanged except for `lean`; there are no new nodes or dependency repairs.

Clause-by-clause correspondence:

- The finite-field, algebraic-closure, prime, coefficient subextension, uniformizer
  and positive-level conventions are the single input
  `P : WeilConjectures.PurityFiniteSetting.{u}`. `P.Ring` is the existing quotient
  `Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`;
  `P.Coefficient` is its standard ULift to the module-value universe. No unramified
  assumption and no divisibility condition on `P.level` is added. Finiteness is
  obtained inside the definition from `Padic.finite_coefficientExtensionRing` and
  `P.level_pos`, rather than required as another input.
- The three finite-type k-schemes are `X Y S : Scheme.{u}` with their `Over`
  structures and `LocallyOfFiniteType` plus `QuasiCompact` instances on all three
  structure morphisms. The maps are `f : X ⟶ Y` and `g : Y ⟶ S`, each `IsOver`
  the same `Spec (.of P.field.k)`, separated, locally of finite type and
  quasi-compact. No separatedness of their structure morphisms is assumed.
- Nagata supplies `HasCompactification f`, `HasCompactification g` and the
  corresponding instance for `f ≫ g`. Compactness and local Noetherianness of Y
  and S are derived inside the definition from their finite-type structure maps.
  They are not extra hypotheses or arbitrary chosen compactifications.
- `L` is the lambda argument `DerivedCategoryBoundedConstructible A S`, where
  `A := ModuleCat.{u + 1} P.Coefficient`. This is the published full subcategory
  of bounded constructible complexes on the small pro-etale site. Its origin
  presentation agrees with the intrinsic class by
  `lem-sf-proetale-constructible-origin` (ii). The object and module values retain
  the site's object universe u+1 and morphism universe u; no universe equality is
  imposed. The result type is inferred after the internal coefficient/geometry
  instances have been installed; L and the morphism endpoints occur in that type.
- `K := (sfFiniteExceptionalAt P.Coefficient cfg).obj L.obj`, for
  `cfg := HasCompactification.compactification (f ≫ g)`, is exactly the recorded
  exceptional inverse image. At this compactification it is definitionally equal
  to `rightDerivedUpperShriek A (f ≫ g)`, namely Rnu_* followed by the ordinary
  etale compact-support right adjoint followed by nu^*. Its ordinary adjoint
  existence is supplied by the existing finite-coefficient instance; it is not a
  pro-etale ambient adjoint assumption. The two target functors are the same
  definitionally equal `rightDerivedUpperShriek A f` and `... A g` constructions.
- `hL := L.property.plusEtaleOrigin.plus` supplies boundedness below.
  `hK := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hL` supplies the
  etale-origin domain of alpha. This existing result supplies more directly the
  witness whose availability the node explains using constructible preservation.
  `(hK.rightDerivedLowerShriek_obj f)` supplies the origin witness for Rf_!K.
  `plus_rightDerivedUpperShriek_obj g hL` supplies the target-domain condition
  for the second Hom bijection. No origin or preservation premise is added.
- `alpha := (originCompositionAmbient P.Coefficient f g).hom.app ⟨K,hK⟩` is
  precisely the forward canonical compositor Rg_!Rf_!K to R(gf)_!K, with the
  direction required in the node. No isomorphism is chosen by Nonempty.some.
- The helper uses `fixedCompactSupportComparisonIso`, the actual normalized
  comparison in `thm-sf-ambient-adjoint-class`. It first conjugates by an
  etale-origin representative, uses that comparison, applies
  `derivedComparisonAdjunction.homEquiv`, then
  `Etale.rightDerivedUpperShriekAdjunction.homEquiv`, then the bijective map of
  fully faithful nu^*, and conjugates back. A representative is selected from
  the existing origin predicate only to compute the transpose determined by
  these adjunctions. There is no choice of an arbitrary functor, comparison or
  natural isomorphism from an existence theorem. This is exactly the normalized
  chain in the dependency's `FixedComparisonClassAdjunction.homEquiv_normalized`.
  The helper is part of evaluating this node's mate, not a new exceptional
  inverse image or new notion of adjunction.
- `counit := (standingExceptionalHomEquiv ... (f ≫ g) hK hL).symm (𝟙 K)` is the
  standing counit epsilon_{gf,L}. It is fixed by the normalized Hom bijection.
- The output applies `(standingExceptionalHomEquiv ... g ...).trans
  (standingExceptionalHomEquiv ... f ...)` to `alpha ≫ counit`. Thus its source
  is R(gf)^!L and target Rf^!Rg^!L, and it is the exact composite Hom bijection
  in the node. This is the `Equiv.trans` order in
  `CategoryTheory.Adjunction.comp` / `comp_homEquiv`, not the reverse order.

Dependency declarations read and used:

- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originCompositionAmbient` and `originComposition`;
  the ambient version is the canonical compositor before the full inclusion.
- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Ring`, `Coefficient`, and their coefficient structures.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction.comp`
  and `comp_homEquiv`; the latter's definition supplies exactly the composite
  bijection order used in the real definition.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`.
  The former is the recorded dependency and the latter specializes it to the
  standing chosen compactification. Current source was read using
  `scompile.py --source` because this finite-coefficient module is absent from
  the older local source tree.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`.
  Its full formula was compared with the finite-coefficient upstream
  `rightDerivedUpperShriek`; their expressions agree definitionally at the
  chosen compactification, as the successful compile checks.
- `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `fixedCompactSupportComparisonIso`, `FixedComparisonClassAdjunction`, and
  `exists_fixedComparisonClassAdjunction`. In particular the helper uses the
  named fixed comparison of this repaired interface, rather than the older
  upstream comparison containing a freely chosen proper comparison.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`: the intrinsic/origin comparison
  statement `constructible_proEtale_origin` and its `ConstructibleOriginComparison`
  interface were read. The main input uses the existing origin presentation of
  the bounded constructible category and its `plusEtaleOrigin` lemma; it needs
  no scalar-presentation copy of the intrinsic predicate.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and its topology, used throughout the actual derived categories.

Additional existing interfaces used are the finite-coefficient
`DerivedCategoryBoundedConstructible`,
`DerivedCategory.boundedConstructible.plusEtaleOrigin`,
`DerivedCategory.plusEtaleOrigin.rightDerivedLowerShriek_obj`,
`plusEtaleOrigin_rightDerivedUpperShriek_obj`,
`plus_rightDerivedUpperShriek_obj`,
`bijective_comparisonUpperStar_mapDerivedCategory_map`, and the ordinary etale
exceptional adjunction. Their defining source was read, including the current
finite-coefficient UpperShriek and UpperShriekComposition modules through
`scompile.py --source`.

Edge cases checked: f an identity, g an identity, both identities, zero L,
empty schemes, level n=1, and arbitrary ramification of E. There is no smoothness,
positive-dimensional, nonempty or finite-Tor hypothesis. For identities the
formula is still the transpose of alpha followed by the standing counit and
therefore has the specified canonical unit interpretation; no extra unit-law
assertion is introduced here. For zero L all displayed maps remain well-typed.
All positive levels are retained even when the ramification index does not
 divide the level. The two primes remain distinct by the stored coefficient
conventions. No statement fault or STATEMENT-DISPUTED flag was found.

Searches made (full service responses are summarized in searches.jsonl):

- LeanFinder: `exceptional inverse image composition comparison defined by
  adjunction counit compact support composition`; eight results about condensed
  adjunctions, sheaf composition and pullback composition, no matching map.
- LeanSearch: `composition of exceptional inverse images as the mate of the
  compact support composition isomorphism`; eight generic category/sheaf
  composition results, no matching pro-etale exceptional compositor.
- Loogle: `CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.homEquiv`;
  found `CategoryTheory.Adjunction.comp_homEquiv`, reused for its precise order.
- msearch grep: `upperShriekComp|rightDerivedUpperShriekCounit` in Mathlib's
  CategoryTheory directory; no hits.
- rg of upstream WeilConjectures and lean/Sheaf for
  `upperShriek.*[Cc]omp|[Cc]omp.*[Uu]pperShriek|pur9-def-upper-shriek-composition|standing.*[Cc]omposition`:
  found existing Hom/counit APIs, existential mate isomorphisms, and
  `GeometricOperations.upperShriekComp` on supplied operation data; none is the
  requested definition for the canonical standing comparison on every bounded
  constructible L. `boundaryProCompositionIsoApp` acts on an etale representative
  and has a different, inverse-orientation composite expression, not this map.
- rg for the item id in upstream WeilConjectures: no match. rg for the two
  proposed declaration names in the upstream name index, upstream sources and
  lean/Sheaf: no match.

Validation: scompile.py passed both the scratch-file compile and final module-name
compile without errors or warnings (10.0 s and 11.5 s respectively). The dry-run
and delivery wrapper outcomes are recorded below when completed.

## Second reading by N9

This is the worker's self-reading; the maintainer performs the independent review.
I reread the node and completed file against the normalized dependency signatures.
The finite-level setting is reused, all three finite-type structure maps and both
separated finite-type k-morphisms are present, and L is bounded constructible with
no finite-Tor restriction. I checked each arrow: changeSource precomposes with the
origin isomorphism, the fixed comparison bijection precomposes with its inverse,
the two adjunctions and fully faithful pullback have the required forward direction,
and the final source change precomposes with the inverse origin isomorphism. Hence
the inverse bijection at identity is the specified counit. Alpha points from the
two-step left functor to the composite left functor; the final Hom equivalence
first transposes through g, then f. The endpoints agree definitionally with the
recorded sfFiniteExceptionalAt construction. Initial explicit adjunction-data
parameters were removed before delivery: the final code constructs the normalized
bijection, so the caller supplies only the stated coefficient/geometric data and L.
No new node, dependency module or statement correction is needed.

Delivery validation: `deliver2.py N9 pur9-def-upper-shriek-composition --no-push`
printed `OK (dry run)` for fd09132407: the server preflight and both file-only
compilation checks passed. The final push uses the same Lean source and node record.
