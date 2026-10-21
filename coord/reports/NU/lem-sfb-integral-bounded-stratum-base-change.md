## Worker report

The module `Sheaf.Paper.IntegralBoundedStratumBaseChange` states the node in two
named theorems, `integral_bounded_open_closed_base_change` and
`integral_bounded_locally_closed_base_change`. Both proofs are `sorry` and their
docstrings give respectively proof steps 1--6 and step 7. The real-data map helpers
`pullbackSquare`, `openMate`, and `closedMate` belong to this node's canonical-map
construction, and are all listed in `lean.declarations`. Five additional real-data helpers name the existing termwise functors and actual
localized adjunctions once, sharing their structural arguments in the signature.
They are direct applications of the published APIs, not new mathematical notions.
No new definition nodes or dependency repairs are needed. The statement and proof fields of the node are unchanged.
The already landed `def-sfb-integral-derived-coefficient-data` is added to `stmt_deps`
to cite its canonical continuous integral coefficient ring, not a new construction.

Hypothesis and clause correspondence:

- The prime ell is `(l : ℕ) [Fact l.Prime]`. The extension is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Its actual valuation topology
  and ring of integers enter `CondensedRing.integralCoefficientRing l E`, the canonical
  alias of `DerivedNakayama.integerRing`. This is continuous functions on profinite
  sets with values in `Padic.coefficientExtensionIntegers`, not discrete coefficients.
- The field and characteristic setting is `(k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]`. For a field positive
  characteristic is prime; these binders render p > 0 and p ≠ ell.
- Every scheme is an object of `Over (Spec (.of k))`, with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`.
  These give exactly separated finite type over k. Every arrow is an Over morphism;
  `.left` is the underlying scheme arrow. All six schemes in each theorem carry
  these binders, including the base changes.
- The open and closed immersions are `[IsOpenImmersion j.left]`,
  `[IsClosedImmersion i.left]`, and the analogous primed binders. Their complement
  relation is `hcomp : Set.range j.left = (Set.range i.left)ᶜ`. The specified fibre
  products are `sqU : IsPullback hU.left jp.left j.left h.left` and the analogous
  `sqZ`; these are the universal-property form of the fibre products and include
  their projections and commutativity. No special reduction of the closed scheme
  is required.
- `condensedRingObj (integralCoefficientRing l E) X.left` is R_X on the small
  pro-etale site, with sheaves of abelian groups in universe u+1. Module objects
  are Mathlib `Mod`, and `DerivedCategory.Bounded` is the ordinary full bounded
  subcategory. `Bounded.ι` is its full inclusion into the ordinary unbounded category.
  The conclusions additionally state `TStructure.t.bounded` for both ends, so the
  comparisons are genuinely between bounded objects with the same ambient morphisms.
- `pullbackSquare` localizes the actual `CondensedRing.upperStarComp` around the
  square. It uses `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso`, with
  no arbitrary comparison choice. `upperStar.mapDerivedCategory` is the termwise
  pullback allowed by the node, not a replacement coefficient or functor.
- Beta is `openMate`, defined by `Adjunction.exchangeLeft` of the actual localized
  open adjunctions and `pullbackSquare`. Thus its component is j'_! applied to
  h_U^*(eta_j) followed by the square comparison, then the actual primed counit.
  Equivalently its transpose is the t_N of proof step 4. The existential natural
  isomorphism `beta` has its hom *equal* to this map, restricted along `Bounded.ι`.
- Gamma is `closedMate`, defined by `Adjunction.exchangeRight` of the termwise
  localized `upperStarLowerStarAdjunction` and the inverse pullback square. Its
  component is precisely closed unit insertion, the square, and the pulled-back
  original closed counit. The natural isomorphism `gamma` has its hom equal to this
  fixed map on the whole bounded category.
- The two `Exists fun [_hi : PreservesFiniteColimits ...]` binders are conclusions,
  not hypotheses. They expose the exactness of closed direct image supplied by
  the node's termwise bounded operations and proof steps 1--3. Left exactness is
  already the published instance. The witnesses only type the prescribed termwise
  direct image and actual localized adjunction; they do not add a geometric or
  coefficient restriction. These are Prop-valued witnesses, with no choice of a
  new module or arbitrary comparison.
- The open normalization is the equation eta_j' followed by j'^* beta equals
  h_U^* eta_j followed by the square comparison. The two `IsIso` clauses on the
  actual units ensure these are the canonical identifications with h_U^*N; the
  equation says the induced endomorphism is the identity, without identifying
  differently presented objects by an arbitrary equality.
- The closed normalization is the equation i'^* gamma followed by epsilon_i'
  equals the square comparison followed by h_Z^* epsilon_i. The actual counits are
  explicitly invertible on these inputs. This is identity under their canonical
  identifications with h_Z^*N.
- For i'^* beta and j'^* gamma, the source and target are each `IsZero` and the
  restriction map is `= 0`. Thus the statement asserts maps *between zero objects*,
  as requested, rather than merely equality to zero on potentially nonzero objects.
- For a = i after u, the second theorem uses the two specified Cartesian squares
  for u and i. Its source composite is h_S^*, u'_!, i'_*, in diagrammatic order;
  its target is u_!, i_*, h^*. Its natural iso e satisfies
  `e.hom.app M ≫ gamma.app (u_!.obj M.obj) = i'_*.map (beta.app M.obj)`.
  Since gamma is the fixed invertible closed mate from the first clause (applied
  with the complementary open), this cancellation equation specifies exactly
  gamma inverse after i'_* beta. It avoids imposing an `IsIso` hypothesis merely
  to use `inv` in the signature. Both ends are explicitly bounded. No independence
  of factorization is asserted.
- The only input condition on N and M is membership in `DerivedCategory.Bounded`.
  No constructibility, finite Tor amplitude or derived completeness is imposed.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension`: `Padic.coefficientExtensionAbsoluteValue`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `finite_coefficientExtensionRing`.
- `Sheaf.Paper.IntegralDerivedCoefficientData`:
  `AlgebraicGeometry.ProEtale.CondensedRing.integralCoefficientRing`, delegating to
  the continuous ring `DerivedNakayama.integerRing` in `DerivedNakayamaResolution`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing` and `condensedRingObj` for pulled-back ring objects.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, `lowerStar`, `upperStarComp`,
  `upperStarLowerStarAdjunction`, with exact pullback and left-exact direct image.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek` and `openImmersionLowerShriekUpperStarAdjunction`.
  Its `Derived.OpenImmersionLowerShriek` module gives the actual termwise derived
  `derivedOpenImmersionLowerShriekUpperStarAdjunction` used in the signature.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: the full-composite total derived
  functors `moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`.
  The present node specifies their exact termwise forms, not their constructible
  restrictions. The imported exact-functor APIs give those forms directly.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the standing Over-field convention and `compactificationOverField`; only that
  setting convention is used, never its `BoundedConstructible` input restriction.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  general derived-category convention. The concrete categories and bounded
  inclusion here are Mathlib `DerivedCategory` and `DerivedCategory.Bounded.ι`.
- Mathlib `pullback` and `IsPullback`, `AlgebraicGeometry.IsOpenImmersion`, and
  `AlgebraicGeometry.IsClosedImmersion`: the three geometric dependency notions.

All recorded proof-dependency modules that are stated are imported without `public`.
The Mathlib proof leaves are also imported (open/closed stability and image via the
geometric modules, homology via `ShortComplex.PreservesHomology`, and natural-iso
localization via `Localization.Predicate`). Proof docstrings retain the full plan:
Noetherian retrocompactness; exact module transport and actual units/counits;
exact-derived localization and joint reflection; normalized mates; complementary
restriction; and the locally closed composite.

Edge cases checked before writing: U empty or Z empty gives zero restrictions;
identity h recovers the adjunction-normalized identity; h factoring through U or Z
still has one vanishing restriction; zero bounded input is allowed; the closed
scheme can be nonreduced; the locally closed open can be empty or the identity.
The locally closed statement uses no complementary-open hypothesis because every
closed immersion of the stated finite-type scheme has its retrocompact open
complement; it does not require another structure choice in its input. Every
bounded degree interval is allowed. No node fault or STATEMENT-DISPUTED remains.

Searches for existing statements:

- `msearch.py` LeanFinder: “For bounded complexes of integral proetale module
  sheaves, inverse image commutes with open extension by zero and closed pushforward
  via canonical adjunction mates”. Eight hits concerned sheaf pullback/pushforward
  adjunctions, scheme module restriction, or functorial composition. None has the
  bounded pro-etale statement with both normalized maps and the stratum composite.
- `msearch.py` Loogle: `"extensionByZero", "pullback"`: zero hits.
- `msearch.py` LeanSearch: “canonical base change open extension by zero closed
  immersion bounded proetale module derived category”. Hits were linear/submodule
  base-change-zero and geometric stability declarations; no matching theorem.
- `msearch.py` grep in Mathlib CategoryTheory:
  `closed.*baseChange|extensionByZero|extension_by_zero`: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `integral.*[Bb]ase[Cc]hange|[Bb]oundedStratum`: no exact statement. Existing
  `ringSheaf_baseChange_mates` is underived with transported ring coefficients,
  and the upstream `boundedConstructibleOpenImmersionLowerShriekBaseChange'`
  is restricted to constructible inputs and supplies only the open part. Their
  full source signatures were read; neither can own this node by an existing match.
- Declaration-name search in `dag/lean_names_upstream.json`, Mathlib/source and
  `lean/Sheaf` found no collision for the namespace or either theorem name.

## Second reading by NU

This is the author's separate second reading; independent review is the maintainer's.
I reopened the node and the complete module. The first theorem covers both maps and
all four restrictions, the second covers the fixed locally closed factorization.
I checked the directions: `pullbackSquare` goes h_S^* a^* to a'^* h^*, beta uses its
forward map, and gamma uses its inverse. The open equation therefore uses `.hom`
and the closed equation `.inv`. The stratum cancellation has e then gamma, hence
e is gamma inverse after i'_* beta, as in step 7. I checked that every geometric
object has the Over-field finite-type/separated instances and that the exactness
binders are existential conclusions. No constructible or completion predicate occurs.
During compilation I qualified the module functors to avoid resolving the unrelated
abelian-sheaf functors. During this reading I switched to the existing canonical
`integralCoefficientRing` alias and cited its landed node. No statement correction,
new definition node, or dependency repair was necessary.

The final computational helpers are `pullback` (exact upperStar.mapDerivedCategory),
`openExtension` (openImmersionLowerShriek.mapDerivedCategory), `closedDirectImage`
(lowerStar.mapDerivedCategory under the returned exactness witness), `openAdjunction`
(the published derived open adjunction) and `closedAdjunction` (the actual underived
adjunction's mapDerivedCategoryAdjunction). Each has real data and its source docstring;
all are listed in lean.declarations. Naming the specializations shares structural
arguments instead of expanding the same large internal module terms repeatedly.
The first direct signature exceeded the artifact compilation limit; this representation
repairs that elaboration cost while keeping exactly the same functors, maps and clauses.
