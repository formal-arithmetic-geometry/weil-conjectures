## Worker report

Item: lem-sfb-nonaffine-closed-test-exchange-identification. Stage 2, Q88.
Module: `Sheaf.Paper.NonaffineClosedTestExchangeIdentification`.
Namespace: `AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification`.

The delivery states the canonical closed-test calculation for qcqs sources without
an affine-source hypothesis. All three new theorems have exactly `by sorry` as
their proofs. The only definitions are three instances which expose the existing
canonical shift structures through the already named functors, using
`inferInstanceAs`. No ring, module category, pullback, section functor, mate or
restriction map is redefined. The repair adds one definition node owning the already landed canonical maps; no dependency module is changed.

The source was read in `literature/stacks-project/proetale.tex`, labels
`lemma-closed-immersion-affines` (09BK) and
`lemma-closed-immersion-affines-apply` (09BL), and
`literature/stacks-project/sites-cohomology.tex`, label
`lemma-unbounded-cohomology-of-open` (0D6F). The latter explicitly allows an
arbitrary site object, which is the point needed for nonaffine T. The node's
complete ten-step proof is carried in the main theorem's docstring. The other
two theorem docstrings specify their portions of that proof.

The newly landed `Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion` was discovered
during final searches and read in full. Its first four declarations are
source-independent, even though its later exchange criterion requires an affine
source. The initially drafted covering/geometry/conservativity restatements were
removed and replaced by an import of that module. In this repair the import is proof-only: none of its declarations enters a new theorem signature. The main nonaffine theorem
never applies its affine-source criterion or the affine-source exchange-model theorem.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Arbitrary commutative condensed ring Λ | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ] [IsCommMonObj Λ]`. This is the underlying ring-object encoding of the recorded `Profinite.CondensedRing`, without a topological-ring presentation. |
| Λ_T = p_T^*Λ | The existing `condensedRingObj Λ T` in every internal module category. |
| Exact module inverse images; ordinary unbounded internal module derived categories | `pull Λ f = (CondensedRing.upperStar Λ f).mapDerivedCategory`; the recorded upperStar is exact for pulled-back condensed coefficients. Direct images are `CondensedRing.moduleObjectDerivedPushforward`, the total right derived functor of the full module composite. No completed category is used. |
| Compatible size convention | One explicit universe `u`; schemes and coordinate rings are in `Type u`, sites have object universe `u+1` and morphism universe `u`, and coefficients/groups are `Ab.{u+1}`. All these are the dependency interfaces' existing size convention. |
| U = Spec A, Z = Spec(A/I), s closed | `(A : Type u) [CommRing A] (I : Ideal A)` and the existing `closedMap A I`, definitionally `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`. Mathlib supplies `IsClosedImmersion` of this map. |
| f : X → U is qcqs; X need not be affine | `(f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]`; no `IsAffine X`, finite-presentation or properness binder. |
| X_Z and projections h, f_Z | `(h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))` with `w : IsPullback h fZ f (closedMap A I)`. This permits any chosen model of the indicated fibre product, including Mathlib's chosen one. |
| Closed-site lift v | The recorded `Scheme.AffineProEt.closedSiteLift A I`. |
| Admissible affine ind-etale V, both V and W=v(V) w-contractible | `(V : (Spec (.of (A ⧸ I))).AffineProEt)` and the two `IsWContractibleRing Γ(..., ⊤)` instances. `AffineProEt` is precisely the recorded affine ind-etale basis. |
| These objects cover | Reused `ClosedLiftedTestIsomorphismCriterion.closed_lifted_tests_cover`, whose covering presieve consists entirely of tests with the two required w-contractibility properties. |
| V = W ×_U Z and the pair (B,IB) is henselian | Reused `closed_lifted_test_geometry`: the canonical `IsPullback`, `HenselianRing` at the actual extended ideal `I.map (((Scheme.ΓSpecIso (.of A)).inv ≫ W.hom.appTop).hom)`, and the ring equivalence B/IB ≃ Γ(V) normalized by the specified inclusion's section map. |
| IB ⊆ Jac(B) | Already part of Mathlib's `HenselianRing` class, field `HenselianRing.jac`. This is extracted from the preceding existing geometry theorem, not omitted or added as an assumption. |
| Joint detection by derived evaluations | Reused `closed_lifted_tests_detect_isomorphisms`, on the full unbounded derived category. Its hypothesis uses precisely `sectionsOver Λ V.hom` for all admissible tests. |
| K ∈ D⁺(Mod_ΛX) | The two natural isomorphisms are functors with source `DerivedCategory.Plus`; their components use `K.obj` via the canonical inclusion `DerivedCategory.Plus.ι`. |
| T = X ×_U W | `pullback f W.hom`, with restriction along `pullback.fst f W.hom`. |
| T₀ = X ×_U V and b closed | The canonically identical iterated fibre-product model `pullback fZ V.hom`. The existing `testMap A I w.toCommSq V` is the actual map into T, constructed by its two projections. The last conjunct of the main theorem states it is a closed immersion. |
| First canonical natural isomorphism | `eLeft`, from `ι ⋙ Rf_* ⋙ pull s ⋙ sectionsOver V.hom` to `ι ⋙ sectionsOver (pullback.fst f W.hom)`. Its normalization states that preceding it by the actual `closedComparison` gives the existing Leray `sectionComparison`. This fixes eLeft uniquely. |
| Second canonical natural isomorphism | `eRight`, from `ι ⋙ pull h ⋙ RfZ_* ⋙ sectionsOver V.hom` to `ι ⋙ pull h ⋙ sectionsOver (pullback.fst fZ V.hom)`. Its hom is explicitly the whiskered canonical `sectionComparison`. Under the existing `pullComp` and the projection equality `testMap ≫ projection_T = projection_T0 ≫ h`, this target is RΓ(T₀,b^*(K|T)). Those exact coefficient/composition maps are retained in `testRestriction`. |
| Evaluated actual ambient exchange is restriction | The main equality is `whiskerLeft ι (evaluatedExchange ...) ≫ eRight.hom = eLeft.hom ≫ whiskerLeft ι (testRestriction ...)`. The existing `testRestriction` is defined by the derived b-unit and the normalized direct-image section-composition comparison. |
| Actual exchange, rather than an arbitrary map | `actual_ambient_exchange` equates `exchange Λ w.toCommSq` with the recorded `CondensedRing.condensedAmbientExchange` conjugated by `leftDerivedUpperStarIsoMapDerivedCategory` at s and h. The chosen Cartesian square is built from `w.isoPullback` and its two projection equations. This makes the preceding equality about the actual ambient mate. |
| Naturality in K | `eLeft` and `eRight` are natural isomorphisms of functors on D⁺, not separately chosen object isomorphisms. The equalities themselves are equalities of natural transformations. |
| Naturality in test objects | `nonaffine_test_naturality` states `TestNaturality` for both f and fZ at every `r : V' ⟶ V`, using the actual `closedSiteLift.map r`; its third conjunct is the closed-unit comparison's naturality equation. Combined with the unique normalizations, these are naturality of both isomorphisms. |
| Shifts and connecting maps | Main theorem conjuncts `NatTrans.CommShift eLeft.hom ℤ`, `NatTrans.CommShift eRight.hom ℤ`, and `NatTrans.CommShift (whiskerLeft ι (evaluatedExchange ...)) ℤ` use the existing canonical shift structures. Naturality at the connecting morphism K₃ → K₁[1], followed by these shift equations, gives the square for image triangles, so connecting maps are included. |
| Restriction to an affine open of a larger target | Reuse the already source-general `ClosedTestDerivedExchangeModel.section_comparison_base_change_naturality` and `derived_restriction_localization`, publicly imported. The former retains every face of the localization cube and the actual test-fibre map, with `[WeaklyEtale v]`; any open immersion satisfies this. Set its v to the affine-open inclusion, b and b' to the two test maps, and the four faces to the restricted fibre-product squares. The latter applies to the closed inclusion between test fibres and its open restriction and also to `closedSiteLiftInclusion`/`closedComparison`. Neither existing statement assumes an affine source. Together with the unique eLeft/eRight normalizations they give exactly the requested compatibility, including the actual b-unit. These existing statements are reused, not duplicated as specialized new theorems. |
| No invertibility of restriction or exchange; no finite presentation or properness | There is no `IsIso` assumption or conclusion on `testRestriction`, `evaluatedExchange`, or `condensedAmbientExchange`. `IsIso closedComparison` concerns only the canonical closed-test section identification. Only the two section-comparison isomorphisms are asserted. |

### Dependency declarations read and used

- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`; its public upstream `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` supplies the total-derived adjunction and `leftDerivedUpperStarIsoMapDerivedCategory`. The full signatures and computational docstrings were read.
- `def-weil-size-convention`: metatheoretic convention, no declaration; rendered by the explicit compatible universes above.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`; the public module was read. Its `Mon` of abelian sheaves is rendered with an underlying sheaf, `MonObj` and `IsCommMonObj`, exactly as the derived operations require.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`, including `spec_of_quotient_mk`.
- `def-weil-pbc-scheme-conventions`: no declaration of its own; use `AlgebraicGeometry.QuasiCompact`, `QuasiSeparated` and `Scheme`, rather than recreating these properties.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`; the universal property, projection signatures and induced maps were read.
- `def-exc-closed-site-lift`: `WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift`, `AlgebraicGeometry.Scheme.AffineProEt.closedSiteLift`; its object and map definitions were read, together with `closedSiteLiftInclusion` and the geometric square in `AffineClosedSiteFunctorProperties`.
- `sk-def-pe-wlocal`: `WeilConjectures.RingTheory.ProEtale.WContractible`, `IsWContractibleRing`; its inherited w-strictly-local condition and extremally disconnected component space are the specified notion.
- `def-weil-pbc-henselian-terminology`: `WeilConjectures.Mathlib.RingTheory.Henselian`, `IsStrictlyHenselianLocalRing`, and Mathlib `HenselianRing`/`HenselianLocalRing`. The relevant pair is the one supplied by the landed geometry theorem; the `jac` field was read explicitly.
- `def-weil-pbc-ambient-ringed-exchange`: `Sheaf.Paper.CondensedAmbientExchange`, `AlgebraicGeometry.ProEtale.CondensedRing.condensedAmbientExchange` and `condensedAmbientPullbackComparison`. Both definitions were read in full, including the canonical derived pullback comparisons and adjunction mate.
- `def-weil-pbc-ind-etale-basis`: `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`, `AlgebraicGeometry.Scheme.AffineProEt`, `toProEt`, `precoverage`, `topology`.
- Definition statement dependency `def-sfb-closed-test-derived-exchange-maps` (added by this repair): `Sheaf.Paper.ClosedTestDerivedExchangeModel`. Uses its canonical `pull`, `exchange`, `closedMap`, `sectionsOver`, `closedComparison`, `sectionComparison`, `testMap`, `testRestriction`, `evaluatedExchange`, `TestNaturality`, `sectionsArrow`; its generic localization statements are reused for the open-target clause. These definitions and the precise signature of its affine-source main theorem were read. The latter is not used.
- Proof-only dependency `lem-sfb-closed-lifted-test-isomorphism-criterion` (removed from stmt_deps in this repair): `Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion`. Publicly supplies `closed_lifted_tests_cover`, `closed_lifted_test_geometry`, `closed_lifted_test_evaluation_exact`, `closed_lifted_tests_detect_isomorphisms`. These are exactly the source-independent first paragraph; the later affine-source criterion is not applied.

All currently recorded proof-dependency modules are imported, with proof-only imports
plain and statement imports public. `lem-sfb-ambient-qcqs-exchange-canonical-shifts`
has no recorded declaration/module yet, so there is no import for it; the main
statement explicitly includes the required canonical shift compatibility. No
unstated proof dependency is used as an input hypothesis. The source-independent
criterion was originally unstated but landed during this turn and is now imported.

### Edge cases and verification

- X may be P¹_U or another nonaffine qcqs scheme: the type has no affine-source
  instance argument and uses site-section localization on nonaffine T.
- I=0: s is the identity, and all formulas reduce through canonical composition to
  the identity closed restriction. They do not force a spurious properness condition.
- I=A: Z and all tests are empty. The module section complexes over the empty scheme
  vanish. Covering and detection use the actual empty-site topology, not a nonempty
  test-family assumption.
- K=0 and the zero coefficient ring are admitted by every binder.
- Every bounded-below K and every shift are allowed; no chosen lower bound or
  nonnegative shift is imposed. Conservativity stays on the full unbounded category.
- Tests have the site's existing size; there is no independent undersized test universe.
- Definitions never choose an arbitrary map/isomorphism. The main existential
  isomorphisms are uniquely fixed by their actual closed-unit and section comparisons.

Every probe and compile was module-mode and used `scompile.py`. The final module
compiled both as a sandbox and under its actual library module name without errors
or non-sorry warnings (20.5 s and 17.2 s in the final standalone run). No global build,
local Lean compiler invocation, direct git command, or live source mutation was used.

### Searches

All search queries below were actually run through `msearch.py`; its sandbox log
records the requests and returned names.

- LeanFinder: `closed immersion pro etale derived sections base change exchange is restriction nonaffine source`. Eight unrelated scheme-immersion and formal-unramified hits; no exact derived-exchange result.
- Loogle: `CategoryTheory.Functor.rightDerivedFunctorCompIso, CategoryTheory.IsPullback`. Zero hits; reports unknown first identifier. This is not treated as evidence that the project's canonical derived-composition API is absent; it was read directly from its recorded source.
- Mathlib grep: `closed_test|closedComparison|sectionComparison` in `CategoryTheory`. Zero hits.
- LeanSearch: `pro etale closed immersion derived base change exchange restriction`. Eight hits about stability of closed immersions/etale morphisms, not this statement.
- Local `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for `closedTest|ClosedTest|closed_test|nonaffine|Nonaffine`, the item id, and the proposed namespace/main theorem names. Found the affine `ClosedTestDerivedExchangeModel`; no nonaffine main statement. Its definitions have no affine-source hypothesis and were reused. Later searches for `tests_cover|liftIdeal` found the newly landed criterion module, whose exact source-independent clauses were then reused and the redundant drafts removed.
- The upstream sectionComparison hits outside this model concern different Zariski/etale section constructions; their types do not state this closed-test condensed-module derived result.

No statement correction, disputed statement or dependency module is needed.
The item's original mathematical statement, proof and proof-dependency list remain unchanged.
The two theorem statement dependencies in the returned packet are removed and replaced
by the new definition node. All theorem signatures and bodies remain unchanged.


## New nodes

`def-sfb-closed-test-derived-exchange-maps` owns the canonical constructions already
present in `Sheaf.Paper.ClosedTestDerivedExchangeModel`, by an `existing: true` record.
It records `pull`, the canonical derived adjunction `adj`, `pullComp`, the square
comparison `square`, its mate `exchange`, ordinary and derived section-composition
isomorphisms, the unit-defined `restriction`, `sectionsOver`, `restrictionOver`,
`sectionComparison`, `closedComparison`, `closedMap`, `testMap`, `testRestriction`,
`evaluatedExchange`, `sectionsArrow`, `fibreMap`, and the proposition `TestNaturality`.
All nineteen declarations have concrete definition bodies in the unchanged landed
module. In particular, none is an object chosen from the affine-source theorem.
No new Lean module or duplicate notion is introduced. The source is Stacks 09BL
(unit-section closed-site evaluation) and 0D6F (sections on localized sites).

The hypotheses of this definition node are precisely commutative condensed Λ,
ordinary derived internal modules, morphisms or commuting squares, A and I for the
closed specialization, and an affine ind-etale V. They render the existing binder
lists of the recorded definitions. No affine/qcqs source or w-contractibility
hypothesis enters these constructions. The TeX gives each map by the actual
adjunction unit/counit, ordinary section identity, pullback composition or universal
property used by its body. TestNaturality is a proposition, not an asserted theorem.
The node's primary `lean.statement` is verbatim the `testRestriction` signature.
The existing module continues to house the declarations; its theorem ownership
record is not edited.

Fresh searches on 2026-10-22: LeanSearch `Canonical closed test derived exchange
maps and unit-defined derived section restriction for condensed module sheaves`
returned 8 hits about ordinary module sections, condensed categories and Zariski
restriction; LeanFinder `Closed test derived exchange canonical section comparisons
restriction unit maps` returned 8 hits about monoidal comparison and profinite
sections. Neither gives this construction. Mathlib CategoryTheory grep for
`closedComparison|testRestriction|evaluatedExchange|TestNaturality` returned 0 hits.
The exact outputs from msearch are copied into the node's mathlib_searches.
Local rg over WeilConjectures and Sheaf finds the exact maps in the existing model
module, and unrelated closedComparison declarations. DAG grep finds that model's
theorem node and the lifted-test criterion, with no definition-node owner.
`blueprint_refs.py search 'closed test derived exchange'` returned 0; ancestor is
`det-sf-comp-coherence-cocycle`. The new node inherits that ancestry. The existing
`def-sfb-derived-exchange-scalar-comparisons` records the different
IntegralLisseClosedBaseChange interface and its scalar maps; it does not own the
closed-test section comparisons or test restriction reused here.

## Repair of returned delivery

The return of immutable head `b8a09f32bab2` identified H2: two theorem nodes were
listed as statement dependencies although the signatures use only plain canonical
map definitions from the model and no declarations of the criterion. This repair
adds the definition owner above, replaces the model theorem in stmt_deps by that
node, and removes the criterion from stmt_deps. Its existing proof dependency stays,
and its import changes from public to proof-only. The maps module remains publicly
imported through the new definition node. No mathematical statement is corrected,
no live source file is changed, and no theorem signature or body is changed.
The saved packet's initial dry run passed as commit `3af6e83a7e8`; that mechanical
pass did not remove the independent review finding, which is addressed here.

## Second reading by Q88

Reread the returned finding against the saved module and the current live module.
Every canonical declaration named in the finding is now recorded under the new
definition node; its nineteen names are plain defs/abbrevs and its primary signature
matches the live source exactly. The item has neither of the two theorem nodes in
stmt_deps. The criterion contributes covering/geometry/conservativity only through
the proof and is now imported accordingly. Compared the saved signatures with
lean.statement and checked that the only source edit is import visibility. The
mathematical clause mapping above still holds, including actual ambient exchange,
normalization of both section isomorphisms, shifts, connecting maps and naturality.
Rechecked empty tests, I=0, I=A, zero coefficient ring, K=0 and a nonaffine qcqs X:
none of the definitions imposes an extra assumption or an invertibility conclusion.
This was a focused self-check; no additional agent was started, as instructed.


Repair validation: `scompile.py` compiled the delivered module in sandbox mode
(29.3 s) and under `Sheaf.Paper.NonaffineClosedTestExchangeIdentification` (22.8 s),
with no errors or non-sorry warnings. A direct packet self-check confirmed that only
stmt_deps and lean differ from the current base item, lean.statement is verbatim,
all nineteen existing declarations are defs/abbrevs, all new-node dependencies exist,
and every delivered Lean line is within 100 characters.
