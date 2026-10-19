## Worker report

Delivery: `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`.
The record is mixed: its two new declarations state the missing general proper/open
comparison compatibility and objectwise exchange invertibility; the existing upstream
declarations listed in `lean.declarations` supply the identity, pasting, canonical exchange,
and compatible-tower clauses. These existing results were read in full, including their
ambient section hypotheses, using `scompile.py --source` and the local upstream sources.
No node statement is corrected, no dependency record is replaced, and no new node is needed.

The new helper `AlgebraicGeometry.Etale.compactSupportProperOpenRefinementMap` has real data:
it applies `rightDerivedLowerStarPlus` for the proper factor of the target compactification
to the specified `properOpenComparison`, then inserts the inverse of the canonical
`pfComp'` compositor. Its type is `F_d K → F_c K` for `r : c.Refinement d`. This is the
map `C_r = Rp₂*(α_r)` in the node's proof. The helper belongs to the comparison notion
already introduced by this item and is recorded in `lean.declarations`.

`AlgebraicGeometry.Etale.compactSupportFiniteTorsion` is the only new postponed theorem.
Its first conjunct states objectwise invertibility of exactly the recorded exchange map.
Its second conjunct identifies each specified proper/open comparison with
`(derivedPlusFormalism (ModuleCat Λ)).shriekIso d c`, for every refinement, without
any density or Cartesian-refinement hypothesis. This clause, together with the recorded
upstream coherence declarations, gives the entire statement, as follows.

Clause-by-clause correspondence:

* Schemes and arbitrary base change: `X Y X' Y' : Scheme.{u}`, morphisms `f`, `f'`, `g`,
  `g'`, and `sq : IsPullback g' f' f g`. There is no property imposed on `g`.
* Separated finite type: `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
  Finite type is the conjunction of the latter two properties in the project's API.
* Supplied compactification: `c : Compactification f`; its real fields are `c.i`, `c.g`,
  openness, properness and `c.comm : f = c.i ≫ c.g`. The quasi-compact open condition
  follows from `c.quasiCompact_openImmersion` and the binder `[QuasiCompact f]`.
* Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
* Base-changed compactification: the exchange declaration uses `c.ofIsPullback sq`;
  its ambient scheme is `pullback c.g g`, its proper map the second projection, and
  its open map the induced pullback lift. Its two Cartesian squares are
  `Compactification.isPullback_i_ofIsPullback` and `isPullback_g_ofIsPullback`.
* Complexes in `D⁺(X_et,Λ)`: the universal binder
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  This is the six-functor encoding of `def-weil-pbc-derived-categories`, not the
  incompatible ULift ringed-site module encoding.
* Precisely the specified exchange: the first conjunct is `IsIso` of the component of
  `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c`. That definition
  is the record of `def-cbc-exchange-map`. Its two factors are the proper derived mate
  and the inverse extension-by-zero base-change transformation, as verified from
  `derivedPlusFormalism_pfBaseChange`, `derivedPlusFormalism_shriek` and `shriekBaseChange`.
  Its source and target functors are exactly `g⁻¹ Rp_* j_!` and `Rp'_* j'_! g'⁻¹`.
* Agreement under every specified proper/open refinement: the second conjunct quantifies
  over every `d : Compactification f`, `r : c.Refinement d`, and `K`; it says the helper
  constructed from `properOpenComparison` equals the component of the canonical
  `shriekIso d c`. Thus no restriction to Cartesian refinements is silently introduced.
* Independence of the common refinement: for any common refinement `e → c`, `e → d`,
  apply the second conjunct with `e` as its supplied compactification to both arrows.
  The comparison ratio `C_s⁻¹ C_r` equals `shriekIso c d` by the recorded
  `shriekIso_trans` and `shriekIso_refl`. It is therefore independent of the common
  refinement, including equalized or non-dense refinements.
* Compactification-independent map and agreement of exchanges: existing
  `Etale.rightDerivedLowerShriekPlusBaseChangeMap` together with the recorded
  `CompactSupportFormalism.lowerShriekBaseChange_eq` computes the canonical map using any
  supplied `c`; invertibility follows from the new first conjunct and these comparison
  isomorphisms. The new second
  conjunct identifies these canonical comparisons with the node's comparisons.
  Hence the exchanges for any two compactifications intertwine their specified
  comparisons by comparing both with this same canonical map.
* Naturality in `K`: both exchange maps are natural transformations, and their
  naturality equation is their `NatTrans.naturality` field. The second conjunct
  also identifies the helper with a component of a natural isomorphism, so it
  supplies naturality for the specified comparisons without an extra assumption.
* Identity base changes: recorded `CompactSupportFormalism.shriekBaseChange_id`,
  specialized to `Etale.derivedPlusFormalism (ModuleCat Λ)`, gives the identity
  equation with `pbId` unit identifications. For `c.ofIsPullback` of an identity
  square, `lowerShriekBaseChange_eq` transports that equation along the canonical
  compactification comparisons, as required by the node.
* Horizontal pasting: recorded `CompactSupportFormalism.shriekBaseChange_paste_horiz`,
  with successive base changes of `c`, gives exactly the equation after `pbComp'`.
  Its upper and lower Cartesian-square binders are satisfied by these pullbacks.
  `lowerShriekBaseChange_eq` transports it to other compactification choices.
* Vertical pasting: recorded `CompactSupportFormalism.lowerShriekBaseChange_paste_vert`
  gives the equation with `lowerShriekCompIso` on both sides. Its hypotheses supply
  compactifications for both morphisms, their composites, and their base changes.
  They require no qcqs base. All its quasi-compactness assumptions follow from finite
  type and base-change stability; all `HasCompactification` instances are provided
  by the supplied compactifications and their base changes, rather than Nagata over
  a restricted class of bases.
* Composition computed by compatible towers: recorded
  `CompactSupportFormalism.lowerShriekCompIso_hom_eq` expresses its composition
  map by any `Compactification.Triangle`. The dependency
  `exists_compactifiable_compatible_tower` supplies such towers over arbitrary bases.
  `compIso` is the chain of the proper/open exchange, open composition, and proper
  direct-image composition appearing in the node. The theorem's comparison clause
  identifies all its compactification comparisons with those specified in the node.
* No residue characteristic, constructibility, qcqs or additional base-change hypothesis
  occurs. The formalism's `HasBaseChange`, `HasProperExchange`, `HasProperBaseChange`,
  monoidal and sheafification instances are supplied for `ModuleCat Λ` by the imported
  modules; they are not extra mathematical assumptions in the signature.

Dependency declarations read and used:

* `def-cbc-exchange-map`: upstream
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`,
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
* `def-cbc-compact-support-square`: upstream `WeilConjectures.Compactification.BaseChange`,
  `Compactification.baseChange`, `ofIsPullback` and their Cartesian-square lemmas.
* `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  `Etale.DerivedCategoryModule` and Mathlib `DerivedCategory.Plus`, as explained
  in that module's full docstring and the node's mixed record.
* `def-weil-pbc-projection-compactification`: upstream
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `Etale.rightDerivedLowerShriekOfCompactification` and its bounded-below counterpart
  `rightDerivedLowerShriekOfCompactificationPlus` (the latter is the restriction of
  the former, by `rightDerivedLowerShriekOfCompactificationPlusCompatibility`).
* `def-weil-pbc-proper-open-comparison`: `Sheaf.AlgebraicGeometry.ProperOpenComparison`,
  `Etale.properOpenComparison`, including its specified three-factor
  `properOpenIdentification`. This exact declaration appears in the helper body.
* `lem-cbc-compactifiable-cofiltered`: upstream
  `WeilConjectures.Compactification.CategoryBaseChange`,
  `Compactification.baseChangeFunctor`, `isCofiltered`, and
  `quasiCompact_openImmersion_iff`; these were read with their ambient hypotheses.
* `lem-cbc-compactifiable-compatible-tower`:
  `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`,
  `AlgebraicGeometry.exists_compactifiable_compatible_tower`.

Every recorded proof-dependency module is imported. The proof-only node
`lem-cbc-proper-open-interchange-coherence` has no Lean record yet, so no import for it
can be added; its use is documented in the theorem's complete seven-step proof plan.
It is a proof input, not a missing object needed to type this statement.

Edge cases checked before writing:

* Empty schemes, empty opens and the zero complex are allowed; there is no nonemptiness,
  nonzero support or `Nontrivial Λ` binder.
* The zero ring is included by `CommRing Λ` and `Finite Λ`.
* All residue characteristics, including those dividing the coefficient exponent, are
  included; finite coefficients only enter via torsion proper base change.
* Arbitrary, possibly non-qcqs bases and non-quasi-compact base-change morphisms are
  included. Quasi-compactness is a hypothesis on `f`, not on `Y` or `g`.
* A refinement can add an extra proper component above the open. In that case its square
  over `X` need not be Cartesian, so the existing
  `shriekBaseChange_refinementComparison` alone would not state the node. The new
  comparison clause deliberately takes only `r : c.Refinement d`.
* Identity base changes retain the canonical pullback identifications; no literal equality
  between chosen fibre products and their factors is assumed.
* Bounded below has no prescribed lower degree. The binder ranges over all of `D⁺`.
* The scheme universe is arbitrary; coefficient modules use the established common `u+1`
  size convention of the small étale six-functor library.

Searches for existing declarations:

* `msearch.py ... leanfinder "Compact support base change for bounded below etale sheaves
  with finite ring coefficients"`: eight hits, only ordinary ring/scheme étale base change,
  including `RingHom.Etale.isStableUnderBaseChange`; no matching derived theorem.
* `msearch.py ... loogle '"shriek"'`: zero hits.
* `msearch.py ... grep 'compact.support|proper.base.change' AlgebraicGeometry`: zero hits.
* `msearch.py ... leansearch "Base change isomorphism for derived direct image with compact
  support"`: unavailable, Internal Server Error; the successful other searches were used.
* `rg` of `WeilConjectures/SixFunctors` for the item id, `shriekBaseChange`,
  `lowerShriekBaseChange` and the exact compactification-relative exchange name:
  the older local checkout does not contain the new BaseChange module; reading the
  published source via `scompile.py --source` found the exact exchange and invertibility
  instance plus the formal coherence theorems. They are reused in the mixed record.
* `rg` of `lean/Sheaf` for the item id and compact-support base change found only proof
  citations and qcqs specializations such as `EtaleCompactSupportBaseChangeQcqs`;
  neither supplies the general proper/open comparison identification in this delivery.
* Read upstream `Formalism/Compactification`, `Formalism/BaseChange`,
  `Formalism/Canonical`, `Formalism/Composition`, `Etale/Derived/LowerShriekFormalism`
  and `LowerShriekPlusBaseChange`. The upstream refinement comparison explicitly
  requires `IsPullback c.i (𝟙 X) r.hom d.i`, whereas this node does not.
* Exact-name `rg` over Mathlib, upstream and `lean/Sheaf` for
  `compactSupportFiniteTorsion|compactSupportProperOpenRefinementMap`: no matches.

Validation: the sole delivered Lean module compiled cleanly through `scompile.py`, both
with its core imports and again with every available proof-dependency import. Only the
named theorem has a postponed proof. The helper is a genuine composite of existing maps.
No statement dispute or dependency-record repair was needed.

Dry-run repair: the published source also has two newer named isomorphism instances,
`isIso_rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap` and
`isIso_rightDerivedLowerShriekPlusBaseChangeMap`, but the preflight mixed-record index
does not recognize them. They were omitted from the optional declarations list because
the new first conjunct already states their needed invertibility, and the recorded
canonical comparison equation transfers that invertibility to the canonical exchange.
No Lean statement or construction was changed.

## Second reading by NO

I read `dag/nodes/sec-smooth-purity/thm-cbc-finite-torsion.json`, its blueprint source
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-cbc-finite-torsion.md`,
the Stacks locations named by the proof (`more-etale.tex`, Tags 0F7I, 0F7J and 0F7F,
and `etale-cohomology.tex`, Tag 0DDE), the complete delivered module, and each of the
seven `stmt_deps` records and declarations.

The node inventory and Lean verdicts are:

- The finite commutative coefficient ring is rendered by
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`; no field, characteristic,
  `Nontrivial`, or nonzero assumption is added. Verdict: exact.
- The schemes and square are rendered by `{X Y X' Y' : Scheme.{u}}`, arrows
  `{f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}`, and
  `sq : IsPullback g' f' f g`. This is the compact-support Cartesian square and
  imposes no property on `g`. Verdict: exact.
- Separated finite type is rendered by `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`. The recorded compactification dependency identifies the latter
  two properties with finite type in this API, and no property of the base schemes is
  assumed. Verdict: exact.
- The supplied compactification is the explicit `(c : Compactification f)`. Its
  open and proper maps and commutative factorization come from the recorded
  `Compactification` declaration; the module does not replace it by an arbitrary map.
  Verdict: exact.
- The complexes are exactly
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} Λ))`, the six-functor ordinary étale module encoding recorded by
  `def-weil-pbc-derived-categories`. Verdict: exact.
- The exchange clause is the first conjunct, objectwise
  `IsIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app K)`.
  The dependency source confirms this is the proper derived exchange on `c.ofIsPullback
  sq`, followed by the inverse extension-by-zero comparison, with the node's exact
  source and target. Verdict: exact.
- The node's compactification-independence clause is represented by the second
  conjunct for every `d : Compactification f`, every `r : c.Refinement d`, and every
  `K`; it equates the real composite
  `compactSupportProperOpenRefinementMap Λ r K` with the component of
  `(derivedPlusFormalism (ModuleCat Λ)).shriekIso d c`. Thus arbitrary refinements are
  included, with no Cartesian or density condition. Verdict: exact.
- Naturality, identity base change, horizontal and vertical pasting, and compatible
  tower composition are supplied by the recorded upstream declarations listed in the
  mixed `lean.declarations` record; they are not silently omitted from the node. The
  node's `proof` explains how those declarations specialize to this finite-coefficient
  formalism. Verdict: covered.

I checked the edge cases explicitly. Empty schemes, empty opens, and the zero complex
are allowed. The zero finite commutative ring is allowed. All residue characteristics,
including characteristics dividing the coefficient exponent, are allowed. Identity
base changes retain the canonical pullback unit identifications. No index set or degree
parameter occurs, so there is no hidden empty-index or `n = 0` exclusion. The single
scheme universe `u` and the established coefficient universe `u + 1` are bound in the
file; no variable or universe is implicit under `relaxedAutoImplicit = false`.

For duplicate checks I ran fresh `msearch.py` searches with different wording:

- LeanFinder: `arbitrary refinement proper open comparison compact support derived
  exchange`; the eight hits were unrelated topology/shrinking and partition-of-unity
  declarations, with no matching theorem.
- Loogle: `CompactSupportFormalism shriekIso refinementComparison`; zero hits because
  `CompactSupportFormalism` is not a Loogle identifier in the imported environment.
- Source/project grep for `compactSupportProperOpenRefinementMap`,
  `rightDerivedLowerShriekOfCompactificationPlusRefinementIso`, and
  `shriekBaseChange`; only the existing upstream refinement/coherence API and the
  delivered helper were found, with no duplicate of this target statement.
- I also read the upstream `LowerShriekCoherence`, `LowerShriekFormalismComparison`,
  `LowerShriekPlusBaseChange`, `Compactification.BaseChange`, and the project
  `ProperOpenComparison*` modules. The upstream refinement comparison requires a
  Cartesian square when used directly; its arbitrary-refinement canonical isomorphism
  does not identify the separately specified `properOpenComparison` map. The delivered
  helper and second conjunct supply precisely that missing identification. The existing
  Noetherian comparison package was not substituted because its hypotheses are stronger
  than this node's arbitrary-base statement.

The only issue found was documentary: the worker report did not yet include this
second-reading section. I added this section; no Lean source, node statement, dependency
record, or proof route required correction. The helper has real composite data and the
only postponed theorem remains a single named `sorry`. The node copy's `lean.statement`
is verbatim the theorem signature. `scompile.py` compiles the delivered module cleanly,
with no errors or warnings other than the permitted postponed theorem.
