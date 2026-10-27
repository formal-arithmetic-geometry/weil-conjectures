## Worker report

Q122, 2026-10-22. The module `Sheaf.SixFunctors.AmbientExactClopenComparison`
states `AlgebraicGeometry.ProEtale.AmbientClopen.ambientExactClopenComparisonLocalizes`.
Its single postponed theorem is the entire assigned node. All helper definitions
have real data; there are no additional postponed assertions. No statement correction or dependency-module repair was needed. The returned H2
repair adds one definition owner for existing realization data. The original natural-language statement,
proof and proof dependencies are unchanged.

### Hypotheses and coefficient categories

- `F : FiniteFieldDatum.{u}` supplies the finite field and its algebraic closure
  `F.k`; `l`, `[Fact l.Prime]`, `_hl : l ≠ F.p` impose precisely the coefficient
  characteristic condition. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` are the finite coefficient extension.
- The already recorded `scalarRings l E n` are `ULift (R/t^(n+1))`, and
  `scalarTransitions` are the actual lifted quotient maps. Thus `∀ n : ℕ`
  covers exactly all positive levels, including level one, without a level-zero
  term. `finiteScalarRing` transfers the recorded positive-level finiteness to
  this common size lift; it constructs no new coefficient ring or uniformizer.
- `U,V,W,Z : Scheme.{u}` have `Over (Spec (.of F.k))` and the four pairs
  `LocallyOfFiniteType`/`QuasiCompact` on their structure maps. This is finite
  type over the fixed algebraic closure, without a separatedness assumption.
  All four morphisms have `IsOver` binders.
- The binders for `k,i` are `IsOpenImmersion` and `QuasiCompact`; those for `r,p`
  are `IsProper`. `h : k ≫ p = r ≫ i` is the commuting square. There is no
  `IsPullback` assumption on it. The only cartesian square passed to beta is
  the actual `pullback p i`.
- The finite-level presentation is the dependency's
  `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} Λ)`, the standard presentation
  of modules over the constant coefficient sheaf. Its ordinary unbounded
  derived category is `ProperOpenDerived Λ T`. This reuses the exact same
  sheaf presentation and total/exact pullback comparisons as
  `ProperOpenProjectionMate`; it is not a private module category.
- The system presentation is the already published `VaryingRing.Modules C τ T`
  on the ringed sequence site, with its actual semilinear transitions, and
  `VaryingRing.Derived C τ T = DerivedCategory (Modules C τ T)`. It is specialized
  to `scalarRings` and `scalarTransitions`. Nothing is evaluated, restricted in
  scalars, completed, or replaced by a limit to state the system equality.

### Each conclusion and its construction

1. `alpha Λ k r p i h` writes the ordinary beta/projector/compositor word in full.
   `StrictTower.squareLift` is `s=(k,r)`, with projections `pullback.fst p i` and
   `pullback.snd p i`. Its existing open-and-closed immersion instances supply
   the clopen decomposition. `projector` is the actual ordinary adjunction unit
   followed by inverse open-to-direct-image comparison, hence identity on the
   open component and zero on its complement. `openComp` uses
   `Adjunction.leftAdjointCompIso` with the pullback compositor; `openCongr`
   transports the equality `s ≫ b = k` by adjoint uniqueness. The final factor
   uses `upperStarComp` and `pullback.lift_snd`. For systems these are precisely
   the already defined `VaryingRing.moduleAlpha`, `moduleBeta`, `modulePi`,
   `moduleJComp` and `moduleGComp`; no duplicate system arrow is introduced.
2. The source and target are functor categories, so these are natural
   transformations. The existing additivity and finite-limit/colimit instances
   express exactness; `localizeSquare` requires precisely these exactness
   instances, including for all four factors.
3. `Normalized` expresses identity restriction on every ordinary sheaf: apply
   the open unit for `i`, the pullback-square compositor and the restriction of
   the transformation, and obtain exactly the open unit for `k` on `r* M`.
   The units are isomorphisms, so this is exactly the stated restriction being
   the identity. `Systems.Normalized` is the identical equation for every
   simultaneous system, with its system unit and `moduleSquareG`.
4. The first two conjuncts of both `OrdinaryAssertion` and `Systems.Assertion`
   assert this normalization and uniqueness among *all* natural transformations
   with it: `∀ a, Normalized ... a → a = alpha ...` (respectively moduleAlpha).
5. `localize` is `Localization.liftNatTrans` of the termwise cochain map followed
   by `DerivedCategory.Q`. `localizeSquare` inserts exactly the standard
   `mapDerivedCategoryCompIso` identifications. There is no boundedness condition.
   `derivedAlpha` further uses only the published comparisons between total
   inverse image and exact termwise inverse image, to place it in the precise
   type of `properOpenAlpha`.
6. `OrdinaryAssertion` states `derivedAlpha = properOpenAlpha` and separately
   states that the localized ordinary beta equals `properOpenBeta.hom`, with
   the same total/exact pullback comparisons. The corresponding system clauses
   identify the localized `moduleAlpha` and `moduleBeta.hom` with the intrinsic
   `SemilinearProperOpen.alpha` and `.beta.hom`.
7. `AdjunctionOnComplexes a d` gives two equations, one for the unit and one
   for the counit, on *every* unbounded complex, using the standard
   `mapDerivedCategoryFactors` isomorphisms. OrdinaryAssertion applies it to
   both specified ordinary/derived open adjunctions for `i` and `k`.
   Systems.Assertion applies it to both actual localized system adjunctions
   and identifies those with the intrinsic `SemilinearProperOpen.jAdj`.
8. System comparison clauses use `HEq` solely to handle two published
   presentations of the same functors: the source file proves `push_eq`,
   `pull_eq`, `extension_eq`, `P_eq`, `J_eq` and `R_eq` by equality of the
   actual coefficient maps and chosen adjoints. These are equal functors,
   not unrelated equivalent categories or arbitrarily chosen transports.
   Hence these heterogeneous equalities say exactly equality after that
   canonical equality transport, including equality of the adjunction data.
9. The last ordinary conjunct gives the component of `properOpenMate` as
   `eta_p`, then `S_p(derivedAlpha at S_r M)`, then `S_p(J_k epsilon_r)`.
   The system clause gives the same component equation for VaryingRing.gamma
   and identifies it with SemilinearProperOpen.gamma. (In VaryingRing notation
   `G` is inverse image and `P` is direct image.)
10. The final main-theorem conjunct identifies the *recorded*
    `z.properOpen.gamma` of ProperOpenProjectionMate in every recorded
    realization with this very word. `realizationAlpha` is the intrinsic
    system alpha conjugated by `z.canonicalBridge.pull` and `.shriek`;
    those bridges are fixed by ordinary sections and adjunctions. The proper
    unit and counit are exactly `(o.direct p).adj` and `(o.direct r).adj`.
    Thus this clause states the normalization in the dependency's coordinates,
    rather than only asserting that some mate exists. No invertibility or
    projection-formula identity is claimed.

### Dependency declarations and imports

Every recorded statement dependency was read with its source declaration and
its docstring. The following are used, directly or through their existing
canonical scheme specializations:

- `def-weil-l-adic-coefficient-extension`: module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`; its imported coefficient-extension
  definitions give the quotient rings, uniformizer and quotient maps.
- `def-weil-scheme-morphism-properties`: recorded convention, no declaration
  of its own; Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`,
  `IsProper` and the scheme-over category implement the relevant properties.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules` (transparent `SheafOfModules`); system
  categories use it directly and the finite presentation is the existing
  constant-module sheaf presentation in the proper/open dependency.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `Scheme.proEtaleConstantRingDerivedPullback` and the publicly reexported
  finite/intrinsic module-sheaf calculus; this includes the proper/open
  dependency's `upperStar`, `lowerStar`, derived adjunctions and exact comparisons.
- `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData`,
  `.semilinearDerivedSections`; the canonical scheme specializations used here
  are the existing VaryingRing and SemilinearProperOpen constructions.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `.fst`, `.snd`, `.lift`, `.lift_fst`, `.lift_snd`.
- `def-weil-pbc-composite-adjunction`: Mathlib's
  `CategoryTheory.Adjunction.comp`, `.leftAdjointCompIso` from
  `Mathlib.CategoryTheory.Adjunction.Basic`.
- `def-weil-pbc-adjunction-mate`: `Mathlib.CategoryTheory.Adjunction.Mates`,
  `CategoryTheory.mateEquiv` (used by the existing proper/open mates).
- `lem-sf-proper-open-projection-mate`:
  `Sheaf.SixFunctors.ProperOpenProjectionMate`, `properOpenAlpha`,
  `properOpenBeta`, `properOpenMate`, `ProperOpenDerived`, `ProperOpenPull`,
  `ProperOpenPush`, `ProperOpenShriek`, and the system normalization through
  `Realizations.properOpen.gamma`.
- `def-pc-sheaf-restrict-scalars`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars`; the existing system category incorporates
  precisely these restrictions in its transitions.
- `lem-pur-site-restriction-module-adjunction-exact`:
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`,
  `SheafOfModules.localizedSystemExact`, `.localizedSystemAdjunction`;
  these supply the exact extension/restriction calculus used by the scheme
  specializations.
- `lem-sf-open-tensor-normalization`:
  `Sheaf.SixFunctors.OpenTensorNormalization`, `SheafOfModules.openTensorNormalization`
  and `OpenTensorNormalization.exactDerivedAdjunction` and its normalized beta
  calculus. The last definition has its own already landed owner,
  `def-weil-exact-derived-adjunction`, added to stmt_deps because it appears
  explicitly in this statement.
- Added landed `def-sp-varying-ring-proper-open-arrows`:
  `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`,
  `VaryingRing.moduleAlpha`, `.moduleBeta`, `.modulePi`, `.moduleSquareG`,
  `.alpha`, `.gamma`; owns the actual underived system word.
- Added landed `def-sf-semilinear-proper-open-comparisons` and
  `def-coef-semilinear-proper-open-mate`:
  `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`,
  `SemilinearProperOpen.alpha`, `.beta`, `.gamma`, `.jAdj`; owns the
  intrinsic derived system word, whose definition is compared to localization.
- Added landed `def-sf-integral-system-canonical-bridge`:
  `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`,
  `WeilConjectures.IntegralSystemRealization.scalarRings`, `.scalarTransitions`,
  `.CanonicalBridge`, `.CanonicalBridge.pull`, `.CanonicalBridge.shriek`;
  owns the canonical transport to the recorded system realization.
- Added landed `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum`; owns the fixed finite-field/algebraic-closure
  datum, without any extra geometric assumptions.

These additions only cite already recorded constructions, as authorized by
brief-stage2 section 5. A read-only traversal of statement and proof edges
confirmed that none reaches the assigned item, so no dependency cycle is added.
The proof-only import `Sheaf.CategoryTheory.ExactDerivedComposition` supplies
`Functor.existsUnique_mapDerivedCategoryCompIso`.
The Mathlib matches of the factorization/localization proof dependencies are
`Functor.mapDerivedCategoryFactors` and `Localization.lift`, `.liftNatTrans`,
`.natTrans_ext`; their modules are publicly imported because the helpers use them.
The clopen restriction proof dependency has no recorded declaration yet and
is named in the proof docstring; it is not silently replaced by a hypothesis.

### Edge cases and source check

The source places read were Stacks `more-etale.tex`, Tag 0F7B,
`sites-cohomology.tex`, Tag 07A7, and `derived.tex`, Tag 015F. The statement's
extension to the ambient pro-etale and simultaneous system categories is
explicitly agent-origin, as the node records.

Checked empty U (projector and all maps to its zero extension), empty W
(forces empty U), the zero sheaf/system, identity maps, a cartesian square
(s is an isomorphism, complement empty), and a nonempty complement killed by
pi. None of these introduces an invertibility assertion. The uniqueness
condition still quantifies over all natural transformations. The first
positive quotient is included and there is no invalid inverse scalar extension
or exactness assumption on the nonflat quotient transition maps. Complexes
remain arbitrary and unbounded. Site objects, morphisms and coefficient
universes use the existing small-pro-etale/size-lift convention; no equality
of independent site universes is imposed. The characteristic exclusion is
retained even though the categorical assertion is more general.

### Searches and validation

Searches through the required msearch wrapper:

- Loogle `CategoryTheory.Adjunction.localization`: three hits, the generic
  localization definition and its unit/counit equations; no geometric assertion.
- LeanFinder `Exact localization of clopen proper open comparison preserves
  normalized base change and adjunction mate`: eight generic adjunction
  localization hits, no exact comparison theorem.
- Mathlib grep `clopen|lowerShriek` in CategoryTheory: zero hits.
- LeanSearch `Exact localization of the proper open clopen comparison equals
  the intrinsic derived comparison with normalized adjunction mate`: eight
  hits, principally Adjunction.derived, .derived', .localization and its data;
  no geometric clopen comparison.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and the
  proposed namespace/declaration returned no match. Earlier searches for
  properOpenAlpha, clopen localization, beta and lowerShriek located the
  dependency constructions cited above, but no theorem combining the clauses.
  The proposed full names also have no match in `dag/lean_names_upstream.json`.

The complete final module compiled with scompile.py against both its sandbox
name and its library name: no errors or unexpected warnings. The latest
completed check took 16.6 s and 21.5 s respectively, within the fixed 60 s limit.
There is no STATEMENT-DISPUTED flag and no identified node fault.

## Second reading by Q122

The dispatcher explicitly forbids starting other agents. This is a second
self-reading, not an independent-worker review; the maintainer's independent
review is still required. I reopened the full node, the emitted signature and
the underlying ordinary/system arrow definitions. I checked the direction of
all three mate factors, both localization-factor equations, the exact positive
index shift, and the equality of the two published system-functor presentations.
I retained the explicit realization-alpha transport so the last conjunct refers
to the dependency's actual gamma rather than a freshly named mate. No change to
the mathematical node statement was made. No extra separatedness, cartesian,
boundedness, reducedness, limit, or invertibility condition appears.


## Returned H2 repair

The saved packet first passed dry-run preflight/compile as 41bc3e409a3. That
mechanical pass did not repair the independent return of immutable head
5a786a7c4a78. I compared the saved node with current main: all fields other
than lean/stmt_deps agree and current main has no item lean record. The
wrapper rebases the saved packet onto current main; no direct git action was used.

1. Removed theorem stmt_dep lem-sf-semilinear-proper-open-mate-pasting.
   Added landed def-sf-semilinear-proper-open-comparisons for alpha/beta/jAdj
   and def-coef-semilinear-proper-open-mate for gamma. Their declaration
   bodies and docstrings in SemilinearProperOpenMatePasting were checked.
2. Added landed def-sf-integral-system-operations for Operations, System,
   Operations.push, Operations.shriek, pull and the actual derived adjunctions,
   from Sheaf.SixFunctors.IntegralSystemOperations.
3. Added landed def-cbc-strict-tower-proper-open-arrows for StrictTower.squareLift
   and its open/closed instances, from Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows.
4. Added def-sf-integral-system-realization-data, an existing:true owner for
   ProperOpenCoherence, Realizations and their explicit helper definitions in
   Sheaf.SixFunctors.IntegralCompactificationSystemRealization. In particular
   ProperOpenCoherence.canonical retains the canonical gamma normalization;
   Realizations.properOpen and Realizations.canonicalBridge are the fields used
   by the final clause. No existence theorem is assumed by this ownership node.

The mathematical node statement, proof, proof_deps and entire Lean source are
unchanged. The declaration signature is still verbatim. I reread the final
realization mate formula with the actual fields open: it quantifies over every
operation package and recorded realization and uses its given proper unit and
counit. The prior independent clause and edge-case checks still apply.

## New nodes

def-sf-integral-system-realization-data registers existing published definition
data; it creates no module and duplicates no Lean definition. Its principal
signature is verbatim Realizations, and it owns ProperOpenCoherence and all
17 existing realization/arrow helpers previously listed only under the
realization theorem. Source: Stacks 0F7B–0F7F, 07A7, 0941 and the blueprint
realization construction. The natural-language definition follows every field:
proper/open gamma, adjunct/canonical normalizations and three pasting fields;
Realizations compositors/open/bridge/properOpen, tensor coherence, natural
comparison, realization model, normalized open/input/unary/tensor/support
recursions, reduction/counit equation, ringed models/completion, canonical
generator/context coherence and finite compact-support comparison. Empty
input families are allowed; this definition asserts no inhabitant exists.

LeanSearch for coherent integral realizations returned eight unrelated generic
topology/semilinear results. Loogle Realizations, ProperOpenCoherence returned
zero hits (unknown identifier Realizations). Mathlib grep for these names
returned zero hits. Read-only rg in WeilConjectures found no match; Sheaf
found the published structures. DAG ownership inspection found only the
realization theorem and mentions in the composition theorem, with no definition
owner. Blueprint search ProperOpenCoherence returned zero; integral realization
returned three unrelated trace/zeta nodes. Exact wrapper outputs are retained
in the new node mathlib_searches.

### Repair self-reading by Q122

I read all fields of both published structures, their preceding helper
definitions and the new node together. Structure types retain specified
normalizations as fields, rather than claiming they exist; in particular
canonical is a field, not an extra theorem imported to prove the item. All
newly cited definition records have usable published declarations. No Lean
change, statement correction or private replacement was necessary.

The repaired packet passed server preflight and all per-file compiles in dry run
723237926f7. A final local comparison confirms all non-lean/non-stmt_deps
item fields and the verbatim signature are unchanged. The available local DAG
has no path from the added owners back to the item; the server preflight is
authoritative for current-main graph validation.
