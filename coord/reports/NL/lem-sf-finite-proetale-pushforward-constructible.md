## Worker report

The delivery states `AlgebraicGeometry.ProEtale.finite_proetale_pushforward_constructible`
in `Sheaf.Paper.FiniteProEtalePushforwardConstructible`. Its only theorem has proof
`sorry`; both accompanying definitions have actual data. The item JSON changes only `lean`.
No statement correction, new node, or dependency repair is needed.

The statement uses the fixed-coefficient module-sheaf presentation already supplied by
`def-weil-pbc-proetale-modules` and explicitly used by the current recorded declaration of
`def-weil-proetale-constructible-sheaf`. The coefficient ring is in `Type (u + 1)` and
module values in `ModuleCat.{u + 1} B`, for schemes in `Scheme.{u}`. The site retains its
object universe `u + 1` and morphism universe `u`; no site universes are identified.
No separate topology on B is required: the fixed constant-coefficient presentation is
the discrete one. This is neither the structure sheaf nor a condensed/complete category.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| Schemes X and Y over k | `{X Y : Scheme.{u}}`, `aX : X ⟶ Spec (.of k)`, `aY : Y ⟶ Spec (.of k)` |
| X and Y finite type | `[LocallyOfFiniteType aX] [QuasiCompact aX]`, and the corresponding instances for aY |
| A k-morphism f | `(f : X ⟶ Y) (hf : f ≫ aY = aX)` |
| No separatedness assumed | There is no separatedness, properness, affine, or extra qcqs binder on f |
| A finite commutative ring B | `(B : Type (u + 1)) [CommRing B] [Finite B]` |
| An integer m ≥ 1 | `(m : ℕ) (hm : 0 < m)`; every positive integer is represented |
| mB = 0 | `(hB : (m : B) = 0)`; multiplication by this equality kills every element, and annihilation of 1 gives the converse |
| m invertible in k | `(hk : IsUnit (m : k))` |
| C in the ordinary pro-etale derived category | `C : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))` |
| Each cohomology sheaf intrinsically constructible | `hC : ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X B ((DerivedCategory.homologyFunctor ... i).obj C)` |
| Finite partition into locally closed constructible subschemes, locally constant with finite stalks | Exactly the recorded fixed-module predicate: a `Stratification`, constructible strata, the canonical restriction by `ProEtale.upperStar`, local constancy, and finite geometric module stalks |
| Only finitely many nonzero cohomology sheaves | `hCb : ∃ a b : ℤ, a ≤ b ∧ ∀ i, (i < a ∨ b < i) → IsZero (H^i C)`; a finite subset of ℤ is bounded, and each such interval is finite |
| A bounded constructible etale realization L | `∃ L : Etale.DerivedCategoryModule B X, Etale.DerivedCategory.isBoundedConstructible B X L ∧ ...` |
| An isomorphism ν_X^* L ≅ C | `∃ α : (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L ≅ C, ...` |
| Canonical comparison is an isomorphism | `IsIso ((finitePushforwardDerivedComparison B f).app L ≫ (lowerStar ... f).rightDerivedFunctor.map α.hom)` |
| Comparison has source ν_Y^* Rf_et,* L | The source of `finitePushforwardDerivedComparison` is `Etale.rightDerivedLowerStar ... f ⋙ (comparisonUpperStar ... Y).mapDerivedCategory` |
| Comparison has target Rf_proet,* C | Its first factor ends in `Rf_proet,* (ν_X^* L)` and its second is `Rf_proet,*(α.hom)` |
| Output cohomology intrinsically constructible | The first output universal quantifier applies the same recorded predicate at Y to `H^i ((lowerStar ... f).rightDerivedFunctor.obj C)` |
| Output has finitely many nonzero cohomology sheaves | The final existential interval and `IsZero` condition apply to this same ordinary direct-image object |
| No finite Tor amplitude | No Tor predicate, flatness, perfectness, chosen resolution, or coefficient-DVR condition occurs |

Canonical map data:

`finitePushforwardDerivedPullbackComparison` is the exact derived comparison
`Dν_Y^* ⋙ Df_proet^* ≅ Df_et^* ⋙ Dν_X^*`. It is assembled from the two canonical
`mapDerivedCategoryCompIso`s and `mapDerivedCategoryNatIso` applied to the published
`comparisonUpperStarCompUpperStarIso`. Its direction agrees with the inverse of a_f
in proof step 4 of the node. `finitePushforwardDerivedComparison` is `mateEquiv` of this
actual map under the published etale and pro-etale unbounded derived adjunctions.
`ofNatIsoLeft` uses the canonical identification of the left derived exact pullback
with its termwise derived functor. Thus it is precisely the transpose of
ν_X^*(the etale counit) after the inverse pullback comparison. It requires neither a
chosen arbitrary morphism nor a bare existence assertion for an isomorphism. The
bounded-below canonical-mate proof dependency proves invertibility after restriction;
the definitions here supply its component on the ordinary ambient derived categories.
Both definitions belong to the canonical comparison clause of this item's own notion
and are listed in `lean.declarations`; they introduce no independent notion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-scheme-morphism-properties` is a convention record. The relevant named
  properties are `LocallyOfFiniteType` and `QuasiCompact`, from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `ProEtale.FiniteCoefficientModules`,
  `FiniteCoefficientEtaleDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientEtaleRealization`, `finiteCoefficientComparison` and their derived
  constructions. These explicitly identify fixed scalar module sheaves with the
  recorded constant coefficient ring-sheaf modules; no new category is defined here.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`; their canonical coefficient functor is the
  published `ProEtale.comparisonUpperStar`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`;
  the ordinary unbounded `Etale.rightDerivedLowerStar` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports ordinary
  pro-etale operations; in fixed-module coordinates the ordinary direct image is
  `ProEtale.lowerStar` and its `Functor.rightDerivedFunctor`, as documented in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, the exact current recorded predicate;
  its module also reexports the intrinsic ring-sheaf predicate.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, `Etale.BoundedConstructibleDerivedCategory`.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`:
  `ProEtale.comparisonUpperStarCompUpperStarIso`; the two derived upper-star/lower-star
  adjunctions are from the etale and finite-coefficient pro-etale derived modules.

All already stated proof-dependency modules are imported. The proof docstring follows
all five DAG steps, including the no-separatedness qcqs argument, etale origin, finite-type
etale constructibility, the canonical mate, and transport of bounds and intrinsic
constructibility. The finite-ring origin theorem is currently in the intrinsic
constant-ring/ULift presentation; its published realization equivalence transports it
to the fixed-module presentation used by the recorded constructibility dependency.
This is a proof-level presentation change, not a replacement predicate or extra hypothesis.

Sources inspected: `literature/stacks-project/proetale.tex`,
`lemma-morphism-comparison` (09A6), `lemma-compare-constructible` (09AK), and
`lemma-compare-constructible-derived` (09AL), including their proofs;
Bhatt--Scholze, local PDF p. 55, Theorem 6.7.1 and Lemma 6.7.2, and the recorded
nonseparated finite-type etale theorem. The source comparison is canonical and needs
qcqs, not a closed diagonal. Finiteness over a field supplies the qcqs conditions in the
proof rather than additional theorem binders.

Edge cases checked before drafting and on the final signature:

- X or Y empty is allowed; there is no nonempty-scheme or nonempty-index binder.
  The existing constructibility predicate permits a positive stratification with empty
  strata, consistent with the empty scheme.
- Zero complexes have an interval `[0,0]`; no nonvanishing of a cohomology sheaf is demanded.
- The zero ring is included. If m = 1, hB forces this case but the signature remains valid.
- Finite nonlocal and nonreduced commutative rings B are included; no residue-field or
  quotient-of-a-DVR reduction is assumed.
- Characteristic zero and positive characteristic fields are both included exactly when
  `IsUnit (m : k)` holds. The forbidden equal-characteristic torsion case is excluded by
  that actual source hypothesis.
- f may be the identity, an open immersion, or nonseparated. It need not be finite as a
  morphism: “finite” in the item refers to the coefficients.
- Each degree may have its own constructible stratification. There is no shared
  stratification or specified uniform cohomological-dimension estimate.
- Coefficient modules may have infinite projective dimension; no Tor-amplitude predicate
  appears anywhere in the theorem's assumptions or conclusion.

Searches made (actual msearch queries, logged under NL and this item):

1. LeanFinder: `Bounded intrinsically constructible finite coefficient pro etale complexes
   have etale origin and finite type pushforward remains bounded constructible`.
   Eight unrelated Mathlib results on etale morphisms and algebras; no match.
2. Loogle: `AlgebraicGeometry.ProEtale, DerivedCategory`.
   Zero hits; the Mathlib service reports unknown identifier `AlgebraicGeometry.ProEtale`.
   This result is not evidence about the project's separate namespace.
3. Mathlib grep: `constructible|[Cc]omparison` in `AlgebraicGeometry/Sites`.
   One unrelated hit `pullbackComparison_forget_surjective`; no constructible-derived
   pushforward statement.
4. LeanSearch: `ordinary direct image along a finite type morphism over a field preserves
   bounded constructible finite coefficient pro etale complexes`.
   Eight unrelated Mathlib hits about finite/proper morphisms and finite fibres; no match.
5. `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   for the item id, proposed declaration names, intrinsic comparison maps, and
   constructible direct-image statements. The proposed names and item id have no earlier
   declaration. Relevant hits included the finite-ring origin theorem, the fixed
   bounded-below canonical mate, and the finite-type etale theorem; all are reused as
   proof dependencies. `ProEtale.boundedConstructible_rightDerivedLowerStar` in
   `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability` was opened:
   it requires `[IsSeparated f]` and starts from an etale-origin constructibility predicate,
   so it does not state this item. `Scheme.finiteField_proEtale_directImage_bounded_constructible`
   was also opened: it is restricted to finite-field coefficients and characteristic
   assumptions and has neither the origin nor canonical-map conclusion for arbitrary B.

Validation: the prescribed `scompile.py` passed both sandbox and library-location
compilation (9.6 s and 10.3 s). The initial diagnostics only identified owning modules
that required explicit public imports; those imports were added. No errors or warnings
remain. No global build or direct live-file edit was used.

## Second reading by NL

This is the dispatcher's worker final reread; the independent reading is performed by
its maintainer, as the brief specifies. The final node and module were opened together.
The field/ring hypotheses and both finite-type structure maps match the node exactly;
`hf` is the k-morphism equation. I checked that there is no separatedness hypothesis and
that input constructibility is the recorded intrinsic fixed-module predicate rather than
an etale-origin predicate. The two input cohomological conditions quantify over the same C.
The first existential supplies both bounded-constructible etale L and its actual
realization isomorphism alpha. The mate's source is ν_Y^* Rf_et,* L and its target is
Rf_proet,* ν_X^* L; composing with Rf_proet,*(alpha) gives exactly the asserted target C.
The final two conditions both refer to Rf_proet,* C and give every intrinsic constructible
cohomology sheaf and one finite vanishing interval. The two helper bodies contain no
`sorry`, arbitrary map, or arbitrary isomorphism choice. The one theorem proof is `sorry`
and has the full five-step natural-language plan. No mathematical signature change was
needed after this reread; compile-driven public-import repairs were the only fixes.
