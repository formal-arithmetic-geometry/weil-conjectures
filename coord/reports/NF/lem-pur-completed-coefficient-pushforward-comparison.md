## Worker report

The module `Sheaf.Paper.CompletedCoefficientPushforwardComparison` states the node as
`WeilConjectures.CompletedCoefficientPushforward.comparison`. Its conclusion is the
existence of a package of normalized total derived functors and comparisons. This
retains their universal transformations; no functor or map is selected from an
uncharacterized existence assertion. Every definition has actual data; the two
named theorem proofs are postponed.

Hypotheses and coefficient objects:

- `l`, `[Fact l.Prime]`, `p`, `[Fact p.Prime]`, `_hlp : l ≠ p` render the distinct primes.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` render the finite extension. The recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal` and `coefficientExtensionRing` give exactly its
  integer ring, chosen uniformizer and quotients.
- `X Y : Scheme.{t}` and `f : X ⟶ Y` are arbitrary, without properness or
  finiteness hypotheses. All sheaves use `ProEt.topology W` on `W.ProEt`.
  The independent coefficient universe is `max u (t+1)`; no equality of
  site-object and site-morphism universes is assumed.
- `R`, `A`, `N`, and `projection` abbreviate the recorded completed ring,
  the generalized constant ring, the recorded finite quotient sheaf and its
  actual limit projection. Index `n : ℕ` means exponent `n+1`, hence all
  and only the positive exponents in the node.
- `constantPush` is the sheafification adjunction applied to constant sections.
  `structureMap` is fixed by `structureProjection` for every finite projection.
  `finiteStructure` and `constantStructure` are the corresponding actual
  constant-section maps. These are the direct-image adjoints of the stated
  inverse-image structural maps, not arbitrary ring maps.
- `Mod` is the recorded `ringedSiteModules`/Mathlib `SheafOfModules` category.
  Ordinary unbounded derived categories use `HasDerivedCategory.standard`, selected by
`hasDerived`; the general comparison records retain abstract localization parameters.
  `RightImage` records the universal total right derived unit and invertibility
  on K-injectives. `ExactImage` records the factorization of termwise restrictions
  through the localization, with `SiteData.U`, `V`, and `restriction` using
  the actual `SheafOfModules.restrictScalars` functors.

Clauses of the conclusion:

- `constantSquare.comparison` gives `U_Y F_R ≅ F_A U_X` (Lean composes functors
  in execution order). The inverse of `finiteSquare n |>.comparison` gives
  `F_R V_Xn ≅ V_Yn F_n`. `Square.normalization` equates the transformations
  on every input complex after the two universal derived units, exactly fixing
  the two ringed-topos factorizations. The ordinary comparisons are normalized
  to the identity on sections in the three `*Ordinary_identity` fields.
- `quotientSquare` gives restriction along every `n ≤ m`; `quotientIdentity`,
  `quotientCoherence`, and `projectionCoherence` give the unit, three-level
  composition, and completion-projection diagrams. `ExactIdentity` and
  `ExactComposition` retain the termwise normalizations of their associators.
- `Systems` is the existing semilinear `SheafOfModules.CoefficientSystem`,
  not a new tower category. `finiteIso_generator` fixes its harmless
  quotient-of-ULift versus ULift-of-quotient presentation on every generator.
  `systemEvaluation`, `systemTransition`, and `systemMap` fix the restriction
  of systems to actual strict `R_W`-module towers. The equalities of raw section
  functions use `HEq` because their scalar presentations have different types.
- `systemPush`, its evaluation normalization, `systemImage`, `towerImage`,
  and `diagramSquare` assert a comparison in the derived categories of
  strict diagram categories. This is stronger data than evaluated arrows;
  `towerEvaluation` fixes its evaluation against the same completed image.
- `SiteData.limit` is the total derived functor of the actual ordinary tower
  limit. Its projections are fixed by `limitProjection_normalization`.
  `ordinaryLimit` is fixed to `limit.post`; `limitComparison` is fixed by
  `limitNormalization`, and its projection equation is `limitProjection`.
- `preservesComplete` uses exactly the recorded
  `IsDerivedCompleteUnrestricted` predicate. `strictReductionExists` transposes
  the recorded `unrestrictedIntegralComplexTower` to an actual complex of
  strict towers. `reconstruction` quantifies over every flat-term K-flat
  representative `P`, every identification `Q P ≅ K`, every such strict
  transpose `C`, and every normalized augmentation. No representative is
  excluded by an arbitrary lift choice.
- `IsReductionAugmentation` fixes the map in each degree and section by the
  actual `unrestrictedIntegralTensorSection ... 1 x`; `reductionAugmentation`
  specifies its unique map to the ordinary limit. `reconstruction` says that
  the map obtained from its derived-limit unit, followed by `limitComparison`,
  is an isomorphism for complete `K`. This fixes the canonical natural
  reconstruction, rather than asserting an arbitrary object isomorphism.
  The `limitProjection` equation identifies its nth component with direct
  image of the quotient unit; `finiteSquare` supplies the stated finite
  coefficient identification.
- `ComparisonData.completeComparison` restricts the full natural constant
  square to the complete full subcategory. Together with `preservesComplete`
  and the imported recorded constant-completion equivalences, this gives
  the final transport of complete direct image, including all arrows.

Dependency declarations read and used (the exact recorded interfaces are imported):

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-proetale-site`: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralCoefficientGerm`, `WeilConjectures.integralConstantToCompletion`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- `def-weil-pbc-completed-pullback`: `Sheaf.Paper.PbcActualStrictPullback`, `AlgebraicGeometry.Scheme.pbcActualStrictCompletedPull`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-pc-sheaf-restrict-scalars`: Mathlib match `{'declaration': 'SheafOfModules.restrictScalars', 'file': 'Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean', 'how': 'exact'}`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`, `CategoryTheory.ringedToposDerivedPushforwardComposition`.
- `lem-weil-ringed-tower-pushforward-limit-comparison`: `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`, `CategoryTheory.ringedTowerPushforwardLimitComparison`.
- `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteUnrestricted`, `WeilConjectures.IsDerivedCompleteUnrestricted`.
- `def-weil-integral-reduction-tower`: `Sheaf.Paper.IntegralReductionTower`, `WeilConjectures.integralReductionTower`.
- `lem-weil-pbc-constant-completion-equivalence`: `Sheaf.Paper.ConstantCompletionEquivalence`, `CategoryTheory.ConstantCompletion.equivalence`.

The generalized constant-to-completion map below replaces only the unusable
same-universe constant interface. The coefficient ring, its diagram and limit,
reduction tower, and derived-completeness predicate are reused unchanged.
The general composition, strict-diagram and constant-completion dependencies
supply the mathematical constructions; their small-site presentations can be
transported to a small model without identifying the original site universes.

Edge cases checked: the identity scheme map and identity coefficient restriction
are included (the unit field is explicit); empty schemes and zero complexes are
not excluded; unbounded complexes have degree type `ℤ`; exponent one is index
zero and no exponent-zero quotient is introduced; all `m = n` and all successive
restrictions occur; arbitrary strict representatives and their isomorphisms
occur in the reconstruction; scheme and coefficient universes remain independent.
The characteristic prime is retained exactly as the node states it, although
the coefficient comparison itself does not need it in its construction.

Searches made before writing:

- `leanfinder` query `Derived pushforward commutes with restriction of completed adic coefficients and strict quotient towers`: `IsAdicComplete.StrictMono.of_comp_lift`, `IsAdicComplete.StrictMono.mkQ_comp_lift`, `IsAdicComplete.StrictMono.of_lift`, `IsAdicComplete.StrictMono.factorPow_comp_extend`. No exact derived strict-tower comparison.
- `loogle` query `SheafOfModules.pushforwardComp`: `SheafOfModules.pushforwardComp`, `SheafOfModules.pushforward_id_comp`, `SheafOfModules.pushforward_comp_id`, `SheafOfModules.pushforward_assoc`. No exact derived strict-tower comparison.
- `grep` query `pushforwardComp|restrictScalars` in `Algebra/Category/ModuleCat/Sheaf`: `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`, `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`, `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`, `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`. No exact derived strict-tower comparison.
- `leansearch` query `derived direct image restriction of scalars sheaves modules`: `PresheafOfModules.restrictScalarsObj`, `PresheafOfModules.restrictScalars`, `ModuleCat.RestrictScalars.obj'`, `ModuleCat.restrictScalars.map_apply`. No exact derived strict-tower comparison.
- `rg` in the named upstream and side Lean directories for the item ID,
  completed-coefficient pushforward names, and relevant restriction/composition
  names: no existing declaration states the whole node. Existing ordinary
  pushforward composition and scalar restrictions are reused.

No statement correction and no new independent definition node is needed.
The statement is not disputed. Source places read: Stacks `0D6E` (derived
pushforward composition), `0A07` (derived direct image and inverse limit),
`099N` (1),(4), and the current blueprint `fix-prop-adjunctions` proof, Step 1.

## Dependency modules

`def-weil-completed-integral-coefficients`: its recorded
`integralConstantToCompletion` forced the finite extension and scheme into the
same universe. `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` supplies
exactly the same constant sheaf, quotient maps, cone and limit lift with
independent universes. The underlying completion is still
`completedIntegralCoefficientSheafUnrestricted`; no second completion is defined.
The cone compatibility is a named postponed theorem with the quotient-induction
proof plan. The copied dependency node changes only `lean` and explains this
interface defect in `lean.note`.

## Second reading by NF

The dispatcher explicitly forbids starting other agents. This section records a
fresh rereading of the node and both modules by the sole dispatched worker;
the maintainer's independent review remains separate. The matching above was
checked against the actual fields, with special attention to the strict-diagram
clause, canonical augmentation rather than arbitrary cone isomorphism, the
identity restriction, the preservation predicate, and independent universes.
The raw section-function equalities were separated from their scalar-linear
bundled maps so that `HEq` expresses unchanged sections without equating different
scalar structures. Universe-instance selection is checked by compilation rather
than by imposing a new equality on inputs.

## Saved-packet repair (2026-10-17)

The required initial dry run found that the saved packet lacked the item node
copy. Restored the current node, changed only its `lean` field, and recorded the
verbatim theorem signature and all helper declarations. The dependency copy also
changes only `lean` compared with the current repository.

The compiler exposed universe unification between the site and coefficient
categories. The repair retains independent `t` and `u` and all mathematical
clauses. `hasDerived` selects `HasDerivedCategory.standard`; `modAbelian`
reuses Mathlib's abelian instance with the existing sheafification inputs and
exposes its native preadditive structure directly. The coefficient-system,
quotient-sheaf and evaluation APIs now receive their three universes explicitly.
`ordinaryTowerLimit` fixes its actual category before inference and is just
Mathlib's `lim`. No canonical map or coefficient object is replaced.

The records disable generation of size and constructor-injectivity auxiliaries.
The data are grouped into inherited coefficient, system-restriction, limit,
coherence, strict-diagram and completeness records within this one module. Every
original field is retained with the same type; `SiteData` and `ComparisonData`
inherit them. This reduces dependent-record checking without adding a hypothesis
or changing any of the canonical normalizations. Temporary checkpoint and heartbeat probes are confined to scratch
work and absent from delivered files. The long line reported by the compiler
has been wrapped. All theorem proofs remain `sorry`; definitions have actual data.

## Continued saved-packet repair (2026-10-17)

The first dry run in this session confirmed that the coefficient-map module
compiled, while the comparison module exceeded the 60-second limit. A scratch
profiler with a reduced heartbeat budget located repeated kernel unfolding in
`SiteCoefficientData`'s section-identity clauses. `IsSectionwiseIdentity` now
names their unchanged underlying-section property. It quantifies over every
object, site object and section, and uses heterogeneous equality only to forget
the scalar presentations. For the three restriction identities this is equivalent
to the earlier equality, because restriction preserves the underlying sections.
The same predicate supplies the ordinary constant, finite, quotient, system
evaluation and tower-evaluation normalizations. No identity case is removed.
The diagnostic checks this coefficient record in about 1.7 seconds.

`quotientMap` remains the actual recorded tower map, with explicit source and
target ring sheaves. The flat-term hypothesis now imports `FlatOnSite` directly
and specifies the original pro-etale site. The site's object universe `t+1`,
morphism universe `t`, and coefficient universe `max u (t+1)` stay independent.
The accidental comment fragment `synthesis.` was removed from `lean.declarations`;
the real predicate helper is listed instead. The primary theorem signature and
the natural-language node statement are unchanged.

The second reading checks these replacements against the node: all ordinary
comparisons still induce the identity on sections; their derived comparisons
still have the universal-unit normalization; the strict-diagram square, quotient
coherence, inverse-limit projections, completeness predicate and canonical
reconstruction augmentation are retained. Only the two named theorem proofs
are postponed across the two delivery modules; every definition has real data.

Final compiler-driven details: the flatness predicate receives the existing
`integralCoefficientAbLocallyBijective` and the weak-sheafification component
`.isRightAdjoint` of `integralCoefficientAbSheafify` explicitly. Two additive
fields whose record argument cannot be inferred are retained as fields, without
global instance registration; `completeComparison` installs its recorded
additive witnesses in its definition. This changes no mathematical assumption.

Validation: the prescribed `scompile.py` compiled both delivered files without
errors or warnings. The main module passed in 24.4 seconds as a sandbox module
and 25.8 seconds under its final library name; the coefficient-map module passed
in under four seconds. No timeout or heartbeat limit was increased. The primary
record signature is verbatim, all delivered Lean lines have at most 100 characters,
and no profiling options or diagnostic declarations occur in the delivery.


## Independent maintainer repair

The immutable delivery at 74fa771414e5f5170178a2906c47a075b21fa955 was read
independently against the item, all thirteen statement dependencies, the exact
recorded interfaces, Stacks 0D6E/0A07/099N, and blueprint fix-prop-adjunctions Step 1.
The mathematical statement and its hypotheses are retained.

H6 mechanical repair: the original integralConstantConeOfUniverses contained a
local change/rw/simpa proof. The existing named postponed compatibility theorem
now states the consecutive-arrow naturality equality in the precise form consumed
by NatTrans.ofOpSequence. The cone supplies this theorem directly. Its two sides
are the same quotient maps as before: the source map is identity and the target
map is the recorded consecutive coefficient transition. The theorem still has
proof sorry, and its quotient-induction proof plan remains in its docstring.
No declaration is added or removed, no data is replaced by sorry, and the primary
recorded signature is unchanged. No JSON correction is needed.

Independent clause checks: distinct primes and the finite extension are the
binders of comparison; R/A/N are the recorded coefficient sheaves; n means n+1.
Mod, push and exact restrictions use the published module constructions.
RightImage keeps the universal unit and K-injective computation. Square retains
common-composite normalization. The constant/finite/quotient identity, associator,
and projection equations fix all restriction comparisons. SystemRestrictionData
retains evaluations, transitions and maps of strict systems; diagramSquare is an
isomorphism before evaluation. SiteLimitData and limitNormalization keep actual
strict derived limits and their projections. IsReductionAugmentation is x↦x⊗1;
reconstruction applies to every flat-term K-flat representative, representative
isomorphism, strict transpose and normalized augmentation. preservesComplete uses
the recorded predicate. completeComparison restricts the constant square to the
complete subcategory, giving the transport under the recorded coefficient
equivalences. Empty schemes, zero complexes, unbounded degrees, exponent one,
identity restrictions, all successive restrictions and independent universes are
included. No properness, boundedness, geometric characteristic or extra instance
is assumed.

The original two files independently reproduced through scompile.py: coefficient
module 2.8 seconds under its library name; comparison module 25.6 seconds under
its library name (20.2 seconds as sandbox). Both completed without diagnostics.
The complete fixed coefficient module and the unchanged comparison module were
then compiled together through the same wrapper: 2.9 seconds for the fixed
coefficient module and 26.8 seconds for the comparison under their library names,
with no diagnostics. The main sandbox check took 20.0 seconds. All compilations use isolated per-file overlay checks; no
global build or project-clone modification was performed.
