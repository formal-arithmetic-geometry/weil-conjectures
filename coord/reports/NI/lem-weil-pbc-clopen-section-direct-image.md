## Worker report

The module `Sheaf.AlgebraicGeometry.ClopenSectionDirectImage` states
`AlgebraicGeometry.Etale.clopenSectionDirectImage`, with one `sorry` and no new definitions.
It supplies a natural isomorphism together with the equation identifying its components
as restriction to the section. The equation avoids choosing any inverse in the statement.

Hypothesis and clause correspondence:

- The schemes and morphisms are `{X V : Scheme.{u}}`, `p : V ⟶ X`, and `s : X ⟶ V`.
- The open immersion is `[IsOpenImmersion s]`; closed image is
  `hs : IsClosed (Set.range s.base)`.
- The section condition is `hsp : s ≫ p = 𝟙 X`.
- The coefficient ring is `Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ]`.
  Commutativity is the convention of the cited derived-category and extension-by-zero
  definitions. The coefficient universe is exactly their six-functor encoding.
- `D⁺(X_et,Λ)` is `DerivedCategory.Plus (Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} Λ))`. All its objects occur as `K`.
- Derived extension by zero is `openImmersionLowerShriek ... s |>.mapDerivedCategoryPlus`;
  derived direct image is `rightDerivedLowerStarPlus ... p`.
- `e` is an isomorphism from their functor composite to the identity functor. Its components
  therefore have exactly the displayed source `Rp_*s_!K` and target `K`, naturally in K.
- The final equation specifies which isomorphism: postcomposing `e.hom.app K` with the
  unit `K → s^*s_!K` equals `Rp_*` applied to the derived unit
  `s_!K → Rs_*s^*s_!K`, followed by the canonical composition and identity isomorphisms.
  The unit `K → s^*s_!K` is invertible for an open immersion, so this uniquely determines
  `e`. At a test scheme this is restriction of sections to the section component. The
  equation thus encodes the word “canonical” and the stated description of the map.
  It imposes no extra condition beyond the source's chosen restriction isomorphism.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded module for
  `def-weil-pbc-derived-categories`; its D⁺ encoding is Mathlib `DerivedCategory.Plus`
  of module-valued etale sheaves (the unbounded encoding is `Etale.DerivedCategoryModule`).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-scheme-conventions` is a convention record with no declaration/module.
  Scheme morphisms and the explicit open-immersion/closed-image hypotheses implement
  the conventions relevant here. No other geometric property is assumed.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, `openImmersionLowerShriekUpperStarAdjunction`,
  `upperStarIsoLocalizationRestriction`, and exactness of extension by zero.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `lowerStar`, used through
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, which supplies
  `rightDerivedLowerStarPlus`, `lowerStarComp`, `lowerStarIdDerivedPlus`, and the
  derived adjunction API. `Functor.rightDerivedFunctorPlusCompIso'` is the canonical
  derived composition isomorphism. Its injective-preservation argument is supplied by
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` applied
  to `upperStarLowerStarAdjunction`; it is a term, not an added hypothesis.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`:
  full faithfulness of extension by zero makes its sheaf-level adjunction unit invertible.
  `Functor.mapDerivedCategoryPlusNatIso`, `mapDerivedCategoryPlusIdIso`, and
  `mapDerivedCategoryPlusCompIso` transport this unit to D⁺. These are the three
  factors after `e.hom.app K` in the equation.
- Proof-only imports cover the remaining recorded proof dependencies:
  `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct` (`Etale.sheaf_clopen_product`),
  `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
  (`Scheme.etaleModule_enoughInjectives`),
  `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`
  (`Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`),
  `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
  (`DerivedCategory.Plus.exists_injective_nonempty_iso`, derived comparison on injectives),
  and `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
  (`CochainComplex.IsKInjective.Qh_map_bijective`). The definitions import supplies the
  recorded exactness, adjunction, and inverse-image-restriction proof dependencies.

Edge cases checked: X empty forces V empty because p exists; both derived categories then
have only zero objects up to isomorphism. The identity section with empty complement is
included, as is any nonempty complement with arbitrary p. The zero coefficient ring and
zero K are included. There is no nonemptiness, connectedness, separatedness, properness,
Noetherian, or cohomological-degree assumption. D⁺ allows any integer lower bound.

Searches made with `msearch.py` (raw service results are in the sandbox searches.jsonl):

- LeanFinder: “For a clopen section s of a scheme morphism p the derived direct image of
  extension by zero is canonically the identity”: eight Zariski restriction/scheme-open
  hits, including `Scheme.Opens.ι_app_self` and `Scheme.Modules.restrictFunctorId_hom_app_app`;
  none states the etale derived section composite.
- Loogle: `CategoryTheory.Functor.rightDerivedFunctorPlus,
  AlgebraicGeometry.Etale.openImmersionLowerShriek`: zero hits, unknown identifier for the
  project-only lower shriek.
- Mathlib grep: `clopen.*section|section.*clopen`: eleven topology/open-subgroup hits,
  no derived etale result.
- LeanSearch: “Derived pushforward of extension by zero along an open and closed section
  is canonically the identity”: unavailable, Internal Server Error.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for clopen/section and
  derived lower shriek: no matching statement. The nearby unbounded
  `isIso_derivedOpenImmersionLowerShriekToLowerStar` compares extension by zero to Rs_*
  and does not involve a retraction p. `FiniteClopenOpenCoverSection` is a geometric
  existence lemma. Neither is this statement.
- Literal item-id search in upstream found no declaration. The proposed declaration name
  was searched in Mathlib, upstream, project sources, and `dag/lean_names_upstream.json`:
  no collision.

The source blueprint node and its full proof were read. No statement correction, new node,
unusable statement dependency, or STATEMENT-DISPUTED issue was found. The proof's
module-sheaf enough-injectives clause is supplied by the coefficient category's existing
Grothendieck-abelian API; its recorded proof module is retained as required.

Validation: server-only single-file compile through `scompile.py` passed cleanly in 1.9 s
(nice 19, two threads, 60 seconds per file). Final dry run uses `deliver2.py --no-push`. The second reader is responsible for independent review and delivery.


## Second reading by NI

I independently read the sandbox node and Lean module, the blueprint source
`sec-smooth-purity/sk-def-sf-operations/lem-weil-pbc-clopen-section-direct-image.md`,
the dependency nodes and the source declarations listed below. No mathematical or
Lean mismatch was found. I left the statement, module, and node record unchanged;
this section records the independent review.

Object, hypothesis, and conclusion checklist (H3):

- Arbitrary schemes X and V: `{X V : Scheme.{u}}`. Verdict: exact; no affine,
  Noetherian, separated, finite-type, or properness assumption occurs.
- Scheme morphism p from V to X: `(p : V ⟶ X)`. Verdict: exact, with no property of p
  assumed besides the displayed section equation.
- Open immersion s from X to V: `(s : X ⟶ V) [IsOpenImmersion s]`. Verdict: exact.
  I opened Mathlib's `AlgebraicGeometry.OpenImmersion`: the abbreviation is the
  open immersion of the underlying locally ringed spaces, as the dependency requires.
- Closed image: `(hs : IsClosed (Set.range s.base))`. Verdict: exact. Together with
  the open immersion this makes the image clopen; it imposes no closedness of p.
- Section equation ps = id: `(hsp : s ≫ p = 𝟙 X)`. Verdict: exact, with Lean's
  left-to-right composition order. `hsp.symm` has precisely the orientation required
  by `lowerStarComp`'s optional composite-morphism argument.
- Finite coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. Verdict:
  exact under the node's cited definitions: the blueprint source and recorded
  `def-weil-pbc-derived-categories` define these coefficient categories for a
  commutative ring, as does `def-weil-pbc-extension-by-zero`. Thus commutativity is
  inherited context, rather than a new restriction on a noncommutative version.
  `Finite` asks for finiteness, without chosen enumeration or nonzero assumption.
- Every bounded below object K: `∀ K : DerivedCategory.Plus (Sheaf
  X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Verdict: exact, using the recorded
  derived-category module's six-functor encoding. The lower bound is arbitrary and
  can be negative; this is not a restriction to nonnegative complexes.
- Extension by zero and derived direct image: the functor source of e is
  `(openImmersionLowerShriek ... s).mapDerivedCategoryPlus ⋙
  rightDerivedLowerStarPlus ... p`. Verdict: exact. I opened the extension-by-zero
  definition and its exactness instances, `Etale.lowerStar` (evaluation after etale
  base change), and `rightDerivedLowerStarPlus` (the bounded below right derived
  functor of that lowerStar). No Zariski or structure-sheaf functor is substituted.
- Isomorphism Rp_*s_!K to K, naturally and canonically by restriction: `∃ e : ... ≅ 𝟭 ...`
  and the equation for every K. Verdict: exact. The natural isomorphism packages the
  naturality in the source's proof; it is not merely objectwise existence. The
  three factors following `e.hom.app K` are the derived unit K to s^*s_!K, obtained
  from the sheaf-level invertible unit using the identity, natural-isomorphism, and
  composition comparison isomorphisms. On the right, the derived unit at s_!K is
  mapped by Rp_*, then composed with Rp_*Rs_* to R(ps)_* and R(id)_* to id.
  I read `Adjunction.derivedPlus_unit_app_fac`,
  `Functor.rightDerivedFunctorPlusCompIso'` and its unit compatibility, and
  `lowerStarIdDerivedPlus`. At an etale test object the unit is restriction to
  the section, by `upperStarIsoLocalizationRestriction` and its localization
  adjunction. The invertible unit on the left therefore makes the equation
  characterize exactly the restriction isomorphism. There is no arbitrary choice
  of identification or extra assertion about an unrelated map.

Dependency and delivery checks (H4, H5, H6, H8, H12, H13): I read all five statement
nodes. The scheme-conventions node is explicitly a convention collection, with no
missing declaration to invent. I opened the actual declarations in
`DerivedCategories`, `UpperLowerStar.Defs`, `Derived.UpperLowerStarCoherence`,
`LowerShriek.OpenImmersion.Defs`, and `LowerShriek.OpenImmersion.FullyFaithful`.
The last module supplies the invertible unit; transport from localization restriction
accounts for the unit of the adjunction with upperStar. The injective-preservation
argument in the signature is an existing theorem applied to the existing adjunction,
not an extra hypothesis. I also inspected the clopen-product and enough-injectives
proof modules: the latter uses a constant-ring SheafOfModules encoding, while this
statement uses module-valued sheaves. As the worker noted, enough injectives for the
latter is provided by the existing Grothendieck-abelian instance; the proof import is
retained, without treating the different encodings as definitionally equal.
There are no new definition nodes or delivered dependency modules. There is no
statement correction requiring a citer audit. The module introduces only the named
theorem with whole proof `sorry`, no hollow data or private notions. Its source-tagged
docstring carries all five proof steps and their dependencies.

Edge cases: if X is empty, existence of p forces V empty, and the statement includes
the resulting zero sheaf categories. Identity s and empty complement are allowed;
so are nonempty complements with arbitrary morphism to X. The zero ring and zero K
are allowed. No prime, characteristic, invertibility, connectedness, or nonemptiness
condition is added. There is no varying index set; the proof's decomposition has two
components, either of which may be empty. The scheme universe u is arbitrary and
both schemes may be placed in a common universe. The coefficient/module universe
u+1 is the dependency's standard small-etale-site encoding; finite rings can be
lifted to it, and no independent too-small test-object universe is introduced.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: “For a retract of an open and closed immersion, pushforward
  of extension by zero on derived etale module sheaves is naturally the identity”.
  Eight hits, including `Scheme.Modules.restrictFunctorAdjCounitIso` and
  `Scheme.Modules.restrictAdjunction`; their displayed signatures are Zariski
  structure-sheaf restriction/pushforward, not this etale constant-coefficient result.
- Loogle via msearch: `CategoryTheory.Functor.rightDerived` returned twelve ordinary
  derived-functor API hits, not the desired composite. A search for the project-only
  total-derived composition identifier was unknown to the service; I read its
  upstream declaration directly instead.
- LeanSearch via msearch: “Pushforward of extension by zero on a disjoint component
  along a retraction is naturally identity” was unavailable (Internal Server Error).
  This is recorded as an unavailable search, not as evidence of absence.
- Independent rg across Mathlib, upstream WeilConjectures, and project lean/Sheaf:
  `clopen.{0,60}section|section.{0,60}clopen|[sS]ection[Dd]irect[Ii]mage` and the
  lowerStar/lowerShriek identity/section pattern found no matching statement.
  Nearby finite-clopen-cover lemmas concern existence of geometric sections.
  I inspected upstream `UpperLowerStar.FiniteEtale`: it supplies clopen sections
  and a finite-etale adjunction, not this arbitrary-retraction derived composite.
  The open-immersion derived comparisons do not assert the p-retraction result.
  The full proposed name and literal item id have no upstream collision, including
  in `dag/lean_names_upstream.json`.

Validation: the node's lean.statement equals the file's entire theorem signature
verbatim. All universes and variables are explicitly bound; all lines have at most
100 characters. Independent server-only scompile.py compilation passed with no
errors or warnings in 1.8 seconds, nice 19, two threads, 60-second per-file limit.
