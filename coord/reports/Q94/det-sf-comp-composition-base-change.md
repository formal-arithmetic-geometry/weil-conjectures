## Worker report

Repair of the return on immutable head `e0f343f7cbdf` (H3 F1–F3 and H11).
The saved packet was inspected first and its prescribed dry run was run before editing.
That dry run failed: its node signatures were stale, its dependency module lacked the
blueprint docstring tag, its report omitted the dependency-module section, and its main
module timed out. The sandbox's intermediate coherence replacement also omitted the
common-dense-refinement normalization. The current shared library now provides a usable
`Sheaf.Paper.CompactificationCoherenceCocycle`, so the replacement module and dependency
node copy have been removed. The packet retains the existing work on the three repairs,
uses current published dependencies, and replaces the rejected signature and stale report.

The delivered module is `Sheaf.SixFunctors.DetSfCompCompositionBaseChange`.
Its only theorem is `AlgebraicGeometry.ProEtale.CondensedRing.det_sf_comp_composition_base_change`,
whose proof is exactly `by sorry`. Every auxiliary definition has real data. The module and
declarations have source/blueprint docstrings, and the theorem docstring follows all eight
steps of the current DAG proof. No mathematical statement correction or new node is needed.
The item node changes only `lean` and adds the two landed dependencies used explicitly:
`det-sf-comp-coherence-cocycle` and `def-weil-pbc-ambient-ringed-exchange`.

Hypothesis-by-hypothesis reading:

- Prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Positive prime characteristic p is `(p : ℕ) [Fact p.Prime]`; the field is
  `(k : Type u) [Field k]`, `_hkp : ringChar k = p`, and `[Fact (p ≠ ℓ)]`.
- Λ is the commutative condensed ring
  `Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with `[MonObj Λ]` and
  `[IsCommMonObj Λ]`. Crucially, `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`
  enforces exactly the coefficient convention of `sk-def-localizing-closure`.
  Its six alternatives are finite discrete rings killed by an ℓ-power, Z_ℓ, Q_ℓ,
  finite extensions E, their valuation rings, and the algebraic closure with its stated
  topology. Λ is not unrestricted.
- X, Y and Y' are `Scheme.{u}`, each with `Over (Spec (.of k))` and structural-map
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances. These are exactly
  the standing separated finite-type k-schemes. Y' is therefore qcqs. For using the
  coherence theorem, the helper derives `CompactSpace` using
  `QuasiCompact.compactSpace_of_compactSpace` and `QuasiSeparatedSpace` using
  `quasiSeparatedSpace_of_quasiSeparated`, on the same structural map. No additional
  qcqs hypothesis is imposed.
- `f : X ⟶ Y` has `[f.IsOver (Spec (.of k))]`, `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, `[QuasiCompact f]`: precisely a separated finite-type
  k-morphism.
- `v : Y' ⟶ Y` has only `[v.IsOver (Spec (.of k))]`. There is no extra hypothesis
  of flatness, properness, quasi-compactness or quasi-separatedness on v.
- The square is the literal scheme pullback: `X' = pullback f v`,
  `u = pullback.fst f v`, `f' = pullback.snd f v`.
- Each `c : Compactification f` is the existing open/proper factorization, with no
  density assumption. Its open is quasi-compact because f is quasi-compact, by
  `c.quasiCompact_openImmersion`. The base-changed compactification is exactly
  `c.baseChange v`, and `v' = pullback.fst c.g v`.

Clause (1): the existential family `o` gives, for every c, the natural isomorphism
`D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧)`.
The equation `(o c).inv = detSfOpenBaseChangeMap Λ f v c` fixes its canonical
normalization; this is not a bare choice of an abstract isomorphism. The named arrow
is open-unit insertion, the published pullback-square comparison transported through
`L(j*) ≅ D(j*)`, and contraction of the base-changed open counit. This is the
adjunction exchange construction and hence the common-right-adjoint comparison in
the source proof. Its direction is `j'! u* → v'* j!`, so the clause-(1) map is its inverse.

Clause (2): `detSfCompactSupportBaseChangeComposite` is an actual natural transformation.
It is the published `condensedAmbientExchange` for the proper literal pullback square,
whiskered by `D(j!)`, followed by `Rp'_*` applied to `(o c).hom`, with the canonical
functor associators. `detSfProperBaseChangeMap` is merely an abbreviation applying that
published mate to the identity identification with the fibre product. The theorem
quantifies over EVERY c and EVERY `K : (localizingClosureProEtale Λ X).FullSubcategory`.
For that c and K it asserts source membership in `localizingClosureProEtale Λ Y'`,
target membership in that same closure, and `IsIso` of the specified composite's component.
These are precisely the assertion that this natural transformation restricts to an
isomorphism of functors between the two full localizing subcategories: full subcategories
inherit every map and inverse between their objects, and a natural transformation is an
isomorphism exactly when all components are. There is no existential arbitrary β and no
assertion of invertibility on the whole unbounded derived category. Naturality is already
part of the constructed transformation. Both closure-preservation clauses and invertibility
are asserted for all compactifications, rather than just a selected c or just the target.

Clause (3): `detSfCanonicalCompactificationComparison` applies
`Classical.choose (compactification_coherence_cocycle Λ ℓ hΛ f)` to the same
compactifications, bundled into the recorded boundary-refinement category. The existing
existence theorem constrains its family by the equation against EVERY common dense
refinement, as well as identity and cocycle. That normalization determines its family
up to equality; this choice does not choose an unconstrained comparison or data from
an existence assertion lacking uniqueness. The comparison is defined only on the localizing
source. The theorem supplies `hU` that pullback carries K into `Loc(Dctf(X',Λ))`, so the
base-changed canonical comparison can be evaluated there. Its final equation says
`v*.map(φ_f(c₁,c₂)_K) ≫ β_c₂,K = β_c₁,K ≫ φ_f'(c₁',c₂')_(u*K)`.
This is the compatibility square with the canonical comparisons on both bases. There is
no quantification over arbitrary isomorphisms φ or φ'. In particular, when c₁=c₂ the
coherence comparison is the identity; the rejected independent choice φ'=-id is unavailable.
Neither the compared compactifications nor their base changes are required to be dense.

Dependency declarations read and used (all signatures and docstrings were opened):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField` is the recorded standing-setting convention. Our explicit
  Over/structural-map binders express that setting, and c is quantified arbitrarily.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; it publicly retains
  `Sheaf.Paper.LocalizingClosure.localizingClosureProEtale` in namespace
  `AlgebraicGeometry.ProEtale`. The closure is the ordinary ambient localizing closure
  on `constantModelBoundedConstructible` intersected with finite Tor amplitude.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`.
  These are the recorded constant-scalar-model notions, not the older arbitrary-matrix
  constructibility predicate.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, the recorded
  total-derived convention; the actual module-object functors here are the published
  generic total derived functors on Mathlib `DerivedCategory`.
- `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`;
  `WeilConjectures.Compactification.BaseChange`: `Compactification.baseChange`,
  `isPullback_i_ofIsPullback`, and `baseChange_g`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and
  `quasiSeparatedSpace_of_quasiSeparated`. The scheme qcqs facts are obtained from
  the standing structural maps; no alternative definition of qcqs is introduced.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `leftDerivedUpperStarIsoMapDerivedCategory`, `leftDerivedUpperStarComp`, and
  `derivedUpperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`;
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction`.
- `Sheaf.Paper.CondensedAmbientExchange`: `condensedAmbientPullbackComparison` and
  `condensedAmbientExchange`; `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `ChosenCartesianSquare`. These provide the exact published canonical exchange.
- `Sheaf.Paper.CompactificationCoherenceCocycle`: `compactification_coherence_cocycle`,
  `compactificationLocalizingCandidate`, `compactificationRefinementComponent`;
  `Sheaf.Compactification.BoundaryRefinement`: `BoundaryCompactification`.
- `WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport`:
  `CategoryTheory.Functor.squareTransport`, for reassociation of the open mate.

Proof-only imports retain the available pullback-preservation, open-preservation,
compactification-preservation, unbounded-extension, internal-module equivalence and
derived-composition-normalization interfaces. The coherence dependency already imports
the common dense refinements, proper/open interchange and derived-compositor interfaces.

Searches (the first three were repeated for this repair):

- `msearch.py ... leanfinder "canonical exchange natural transformation extension by zero pullback base change derived functors"`:
  eight generic Ext, Kan-extension, pullback and localization hits; none is this statement.
- `msearch.py ... loogle "Functor.squareTransport, CategoryTheory.mateEquiv"`:
  zero hits; Loogle does not index the project `Functor.squareTransport`.
- `msearch.py ... grep "openImmersion.*BaseChange|BaseChange.*openImmersion|squareTransport" CategoryTheory`:
  no Mathlib hits. Direct source search locates squareTransport in the published project.
- Prior packet `leanfinder "proper base change for compactly supported derived pushforward on localizing constructible categories"`:
  generic pushforward/composition hits, no matching theorem.
- Prior packet `loogle "rightDerivedLowerShriek, derivedBaseChangeMap, localizingClosure"`:
  zero hits; names not indexed by Loogle.
- `rg` across the allowed upstream, side framework and `lean/Sheaf` trees found the landed
  condensed ambient exchange and coherence theorem, which are now reused. No existing
  declaration states the item's three-clause result. The existing integral compact-support
  theorem uses Loc(Dbc) and integral coefficients, not this all-admissible Loc(Dctf)
  statement; its proof depends on this item, so it is not substituted for this theorem.
- The direct upstream node-id search found no declaration. New helper names were checked
  in upstream and side sources for collisions; none is already declared.

Edge cases checked: v=id is allowed; c₁=c₂ uses the canonical identity comparison;
nonflat v and nondense base-changed compactifications are included; empty X and zero K
remain in the same categories; no restriction to bounded complexes is introduced in
Loc(Dctf); ℓ=2 and p=2 are separately allowed with p≠ℓ; all six admissible coefficient
cases remain, including the zero finite ring and degree-one extension cases Z_ℓ,Q_ℓ.
No independent site or coefficient universe was equated: schemes are in u and the
abelian coefficients are `Ab.{u+1}`, exactly as in the published module-object framework.
The localizing closure's ambient coproduct convention is inherited unchanged.

## Second reading by Q94

Fresh self-check under the dispatcher's prohibition on starting other agents. I reopened
the current node, the clause-(1) source/proof, the landed coherence and coefficient modules,
and the entire final Lean file. This is not a claim of a second worker's independent review;
the maintainer's independent review remains required.

F1 is repaired: the old arbitrary φ,φ' binders are gone. The saved intermediate
coherence structure asserted uniqueness from identity/cocycle alone, which is insufficient;
that whole replacement was removed. The final helper instead selects the family constrained
by the landed theorem's common-dense-refinement normalization. It has a localizing source,
and the final equation uses that same family on Y and Y', evaluated after u* with hU.
For c₁=c₂ the two normalized families yield identities, so φ=id,φ'=-id cannot occur.

F2 is repaired: I traced the definition of β all the way to the published ambient mate,
then Rp'_* of the inverse of the canonical open exchange. The old unrelated existential β
and full-unbounded isomorphism are gone. For EVERY c and K in Loc(Dctf), the theorem gives
both target-category membership statements and IsIso of this precise component. This
is equivalent to a natural isomorphism between the corresponding full-subcategory functors.
The clause-(1) isomorphism is itself normalized by equality of its inverse with the explicit
unit/square/counit arrow, so β cannot conceal an arbitrary open isomorphism either.

F3 is repaired: hΛ is the existing six-case admissibility predicate, explicitly indexed by
the same prime ℓ as the characteristic exclusion. The standing field, scheme and k-map
binders remain, Y' is qcqs from them, and v has no new property. I checked the literal
pullback projections, the canonical base-changed compactification, and that no density of
its open was used. Docstrings contain source/blueprint tags and all eight DAG proof steps;
all universes and variables are bound; the only postponed proof is the item's named theorem.
The natural statement needs no correction and has no STATEMENT-DISPUTED flag.
