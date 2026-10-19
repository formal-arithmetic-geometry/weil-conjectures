## Worker report

Group NU, stage 2, item `lem-a1-degree-zero-compact-support-sections`.
The delivery states the comparison of completed degree-zero cohomology with ordinary
inverse-system adic sections. The primary declaration is
`WeilConjectures.a1DegreeZeroCompactSupportSections_natural` in
`Sheaf.Paper.DegreeZeroCompactSupportSections`. Its natural comparison package is
`A1DegreeZeroNaturalComparison`. The companion theorem
`a1DegreeZeroCompactSupportSections` displays the direct objectwise formulation.
Every theorem proof is `sorry`; definitions contain actual data. The sole chosen
functor is specified uniquely, on both objects and arrows, by the named theorem
`a1DegreeZeroLisseInclusion_existsUnique`.

Hypotheses and clauses, checked against the node with the Lean file open:

| Node | Lean |
| --- | --- |
| Finite-field datum, including the specified algebraic closure of the finite field | `D : FiniteFieldDatum.{u}`; the geometric fibre is literally `(D.geometricFiber X₀).left` |
| A prime different from the residue characteristic | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`; residue-field invertibility is derived by `sfWeilPrimeInvertible`, not assumed |
| Algebraic closure of Q_l | `(Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`; this is the universe of the recorded algebraic lisse category |
| X₀ smooth, separated, finite type over k₀ | `X₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom] [Smooth X₀.hom]` |
| A lisse Qbar-Weil sheaf F in the completed common-stage category | `F : sfCommonStageWeilSheaf D l hl X₀ Ω` and `HasCommonStageLisseLattice ... ((sfCommonStageWeilForget ...).obj F.obj)`; the latter is the already landed smooth-lisse carrier predicate, not a new private notion |
| Underlying object, with Weil structure forgotten | Every cohomology argument and realization uses the recorded `sfCommonStageWeilForget`, with no Frobenius-fixed-section condition |
| Existence of an inverse-system lisse L | Both theorems quantify `L : A1DegreeZeroLisse ...` directly; its literal coefficient pair and integral model determine `a1DegreeZeroRealization` |
| L realizes For(F), without declaring the categories equal | `A1DegreeZeroRealizes` requires an isomorphism in the actual common-stage category to `lisseIntegralCommonStage` of the actual inverse-limit realization `a1DegreeZeroRealization` |
| Natural H⁰ identification with ordinary sections | `A1DegreeZeroNaturalComparison.ordinary` is a natural isomorphism from the descended ordinary cohomology functor to the unit coyoneda functor on the full algebraic-coefficient lisse category. Its `ordinaryIntegral` comparison identifies the functor with the actual derived cohomology functor on every finite integral stage. `a1DegreeZeroCompactSupportSections_natural` identifies its source value with `adicOrdinaryCohomology ... For(F) 0` by an Ω-linear equivalence |
| Hom from the constant unit in the recorded lisse category | `a1DegreeZeroUnit` is `lisseAlgebraicUnit`; `A1DegreeZeroSections` is literally its Hom into L. `ULift` in the natural isomorphism only reconciles the larger Hom universe; it changes no mathematical elements |
| Natural injective Ω-linear compact-support map | `A1DegreeZeroNaturalComparison.compact` is a natural transformation between the compact and ordinary module-valued functors on the full algebraic-coefficient category; `ordinaryIntegral` and `compactIntegral` identify their arrow actions with the actual completed cohomology functors at every finite field; `injective` asserts componentwise injectivity. Composing with `ordinary.hom` and the displayed linear cohomology equivalences gives α. In the objectwise theorem this is `e ∘ a`, with `a : H_c⁰ →ₗ[Ω] H⁰` and `Function.Injective a` |
| Linearity in the Hom target | `linear` and the objectwise linearity clause assert preservation of zero and every `b • s + t` on each actual geometric fibre. These are precisely the canonical Hom-vector-space operations, tested on the jointly faithful adic fibres; no arbitrary module structure on Hom is selected |
| For every compact-support class | `support : ∀ L (z : compactCohomology.obj L), ...`, and the objectwise theorem's final `∀ z : adicCompactCohomology ... 0` |
| Exactly its nonzero geometric-fibre locus is closed | `∃ Z : TopologicalSpace.Closeds X, ... ∀ κ [Field κ] [IsAlgClosed κ] y t, y.base t ∈ Z ↔ a1DegreeZeroSectionFiber ... y (...) ≠ 0` |
| Its reduced closed subscheme is proper over k | `IsClosedSubsetProperOver (D.geometricFiber X₀).hom Z`; this is exactly the recorded vanishing-ideal/reduced-closed-subscheme definition |
| Fibres have the stipulated adic meaning | `a1DegreeZeroSectionFiber` uses `(lisseAlgebraicFiberFunctor ... y Ω).map s`, whose construction is the inverse limit, rationalization and final scalar extension of the recorded model fibres |
| No affine, connected or dimension restriction | None occurs in either theorem; the geometric-property helper derives Noetherianness and separatedness from finite type over the field |

The compactification argument `c` is arbitrary. It is a presentation of the recorded
compact-support construction, available by Nagata, not an extra properness hypothesis
on X. The statement holds for every such presentation. Cohomology comparisons use
actual completed direct image, actual compactification functors, point derived
sections, homology, and scalar extension. Naturality is expressed by natural isomorphisms/transformations on the entire
algebraic-coefficient lisse category, rather than only integral maps or objectwise
bijections. The `ordinaryIntegral` and `compactIntegral` natural isomorphisms are
quantified over every finite field, fixing the functors to the actual integral
cohomology actions. The coefficient comparison tower laws give this descent, as
described in proof step 7.

The proof docstring records all nine steps of the node: smooth lisse lattice and
normalized reductions; integral constructibility and compactification; finite-level
ordinary/compact comparison; injective restriction with proper support; inverse limit
and degree-zero Milnor vanishing; unit maps and flat rationalization; lattice and
coefficient independence/naturality; stabilization of supports on finitely many
clopen components; clearing denominators, including the zero class. The helper
constructibility theorem and the uniquely characterized inclusion each have their own
complete proof explanation. They belong to this same comparison notion and are
listed in `lean.declarations` of its node.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, its `geometricFiber`.
- Mathlib: `AlgebraicGeometry.Smooth`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, the scheme-over-base and bundled `Over` conventions. The scheme
  morphism-properties dependency is a convention node with Mathlib matches.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilForget`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.LisseAdicSheaves`: `LisseIntegralSheaf`, `LisseAlgebraicSheaf`,
  `lisseAlgebraicUnit`, `lisseAlgebraicPair`, `lisseCoefficientPairModel`,
  `lisseAlgebraicOfModel`.
- `Sheaf.Paper.LisseAdicFiberFunctors`: `lisseAlgebraicFiberFunctor`,
  `lisseAlgebraicModelMap` (the actual coefficient-localized integral arrow).
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `Scheme.IsClosedSubsetProperOver`; its current source was read using
  `scompile.py --source` because the older checkout did not contain it.
- `Sheaf.Paper.CommonStageLisse`: `HasCommonStageLisseLattice`. Its landed node
  `def-a1-common-stage-lisse-lattice` is added to `stmt_deps`.
- `Sheaf.Paper.LisseIntegralCompletedRealization`: the new definition node
  `def-a1-lisse-integral-completed-realization` owns
  `lisseIntegralCompletedRealization`, `lisseIntegralCommonStage`, and
  `lisseIntegralPointCohomology`. They respectively use the existing finite-level
  conversion and ordinary inverse limit, the recorded rational localization and
  finite-stage inclusion, and `pointFibreIntegralAmbient` with homology and inverse
  ULift coefficient restriction.
- `Sheaf.Paper.CompletedCoefficientPresentationTransport`:
  `purCoefficientModel` is the definition-owned exact transport of the two
  normalized completed coefficient presentations. It replaces the immersion
  theorem module's `ImmersionCompletedPullback.transport`.
- `Sheaf.Paper.CurveWeilMiddleExtension` publicly retains
  `middleExtensionLevelFunctor`, used only for its
  identity-morphism finite-level site/coefficient conversion. No curve hypothesis
  occurs in that functor or in the new realization.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient` replaces the
  theorem-module helper `pointCompletedDerivedSections`. Its canonical lifted
  coefficient action is transported back with `ULift.ringEquiv.symm.toRingHom`.
- `Sheaf.Paper.OrdinaryCompactCohomology`: `rationalOrdinaryCohomology`,
  `rationalCompactCohomology`, used by the dependency extension below. The helpers
  are owned by `Sheaf.Paper.CommonStageCompactWeilCohomology`, which publicly
  retains the old `OrdinaryCompactWeilCohomology` interface.

The returned H9 observation is repaired by removing the nonpublic imports that
were needed only for future proofs. The retained public imports supply the
statement's actual data and predicates. The nine-step proof plan and its DAG proof
dependencies remain in the docstrings and node. The statement does not import
`AdicMiddleExtensionConstructible`, `SfImmersionCompletedPullbackComparison`, or
`PointSectionsScalarExtension` directly for generic helper definitions.

Source reading: the current blueprint proof of `lem-a1-affine-hc0` was read, together
with Milne Definition 18.1 and Remark 29.7 and Bhatt--Scholze Propositions 6.8.4,
6.8.14 and Remark 6.8.15. The lemma extracts the degree-zero proper-support argument;
it does not import the affine-curve hypothesis from its consumer.

Edge cases checked before finalizing the statement:

- Empty X and the zero sheaf/class: Hom and both groups are zero; take empty support.
- Proper X: the full support is permitted, and ordinary and compact groups agree.
- Constant sheaf on affine A¹: a nonzero constant ordinary section has nonproper
  full support, so is excluded from the compact-support image; the theorem does
  not incorrectly identify all ordinary sections with compact sections.
- A point disjoint union A¹: compact classes may live on the proper component;
  connectedness is not assumed and supports may be proper nonempty clopen unions.
- Different ranks on disconnected components and rank zero on a component are
  permitted; no globally constant-rank binder occurs.
- Integral coefficient torsion is allowed in the integral-model functors and dies
  after rationalization. Finite Tor amplitude may include degree -1 before
  rationalization; the helper docstring does not assert integral local freeness
  for every integral model.
- A section divisible by the uniformizer may vanish at the first finite level;
  support is tested on the inverse-limit fibre, and the proof stabilizes the
  increasing finite-level loci rather than using only the first quotient.

Searches for an existing statement (all returned no match):

- `msearch.py ... leanfinder "Degree zero compactly supported cohomology injects
  into global lisse adic sections with proper support"`: unrelated analytic
  support/function lemmas, no adic comparison.
- `msearch.py ... loogle "CompactSupport, LisseAlgebraicSheaf"`: unknown
  `CompactSupport`, no result for this comparison.
- `msearch.py ... grep "compact.*[Ss]upport.*[Ss]ection|[Ss]ection.*[Pp]roper"
  AlgebraicGeometry`: unrelated structure-sheaf/support results, no match.
- `rg` in the upstream WeilConjectures sources for compact support, lisse sections
  and the exact item id: no declaration of this assertion. The existing cohomology
  and inverse-system constructions were reused rather than redefined.
- `rg` in `lean/Sheaf` found the `AffineCurveHcZero` consumer's documentary reference
  and the coefficient/realization helpers above, but no existing theorem of this
  node. The upstream declaration-name index had no names matching the new names.

No statement correction or disputed statement. The item's original mathematical
statement, nine proof steps, and proof dependencies remain unchanged. Its added
statement dependencies are the landed common-stage lisse predicate, the recorded
lisse fibre-functor definition, and the new realization definition node. The
returned theorem-node dependency is removed.

## Dependency modules

`def-weil-ordinary-compact-cohomology`: the §1(B) extension is in
`Sheaf.Paper.CommonStageCompactWeilCohomology`. NX's recorded interface covers
compact support only, over a compactification of X₀ over k₀, as a Weil sheaf.
It supplies neither ordinary H⁰ nor the coefficient-module value with Ω in
`Type (u+1)` required by this item's lisse category. Its main definition
`commonStageCompactWeilCohomology`, `sfWeilCohomologyPoint` and
`sfWeilCohomologyPoint_isFinite` are retained verbatim. The dependency record keeps
NX's module, main declaration, statement, file and three declarations, and adds
only `WeilConjectures.adicOrdinaryCohomology` and
`WeilConjectures.adicCompactCohomology` to `lean.declarations`, together with the
required explanation in `lean.note`. The repair author/date are recorded as NU
and the current UTC date, as preflight requires. Other dependency-node fields
are unchanged.

The two appended helpers retain the previously checked text with independent
coefficient universe `v`. They compute the recorded finite-stage rational groups,
then use `ModuleCat.extendScalars` along
`K.stage.val.subtype.comp (Shrink.algEquiv ...).toRingHom`. The result is
`ModuleCat.{max u v} Ω`; no site and coefficient universes are identified.
`OrdinaryCompactWeilCohomology.lean` stays unchanged on the base and is not part
of this packet. It remains publicly imported by NX's module, preserving Q43's
older Frobenius-retaining interface. The item now imports NX's owning module.

## New nodes

`def-a1-lisse-integral-completed-realization` owns
`Sheaf.Paper.LisseIntegralCompletedRealization`. For a normalized lisse integral
system it defines the actual inverse-limit realization in degree zero, using the
identity finite-level conversion and the definition-owned exact normalized
coefficient transport. Its common-stage object is literally the image under
`GeneralAlgebraicallyClosedCoefficients.inclusion` of the object localized by
`sfRationalConstructibleLocalization`.
Its point normalization uses the recorded integral fibre, homology, and the inverse
ULift coefficient identification. The source is BS 6.8.4(1),(4), 6.8.14(2),
Remark 6.8.15 and Weil II (1.1.1) b)--d); the point convention is the recorded
finite-coefficient-point definition. No curve, dimension, connectedness, or
nonemptiness hypothesis enters the construction.

Searches for this definition: LeanSearch's inverse-limit/lisse-realization query
returned eight unrelated inverse-system, adic-completion and profinite-limit hits;
Loogle's `LisseIntegralSheaf, sfRationalConstructibleLocalization` query returned
no hits (unknown `LisseIntegralSheaf`); Mathlib grep
`Lisse.*Realiz|lisse.*realiz|Integral.*Realization` in AlgebraicGeometry returned
zero hits. The new node records their exact structured outputs. DAG/Sheaf/upstream
rg and blueprint_refs `inverse-limit` found general limit/completion nodes and
generic helpers in theorem modules, but no definition node for this realization.
Existing finite-level conversions, coefficient transport, rational localization,
common-stage inclusion and point fibre are reused, rather than duplicated.

## Returned review repaired

1. H2/H4: removed `lem-a1-adic-middle-extension-constructible` from statement
   dependencies and replaced it with the new definition node. Removed direct uses
   of `adicMiddleExtensionIntegral`, `adicStageObject`,
   `ImmersionCompletedPullback.transport`, and `pointCompletedDerivedSections`.
   All realization and point cohomology constructions now pass through the
   explicitly cited definition module and its recorded definition dependencies.
2. H2/H13, immutable return head `5266638bfe4d`: retained NX's dependency
   record and its three declarations. Moved the two independently sized
   coefficient-value helpers, with unchanged signatures and bodies, to NX's
   `CommonStageCompactWeilCohomology` module. The item imports this module.
   Q43's `OrdinaryCompactWeilCohomology` module is unchanged on the base.
   The dependency note and the Dependency modules section now explain why NX's
   compact-only Weil-sheaf interface does not supply this item's ordinary H⁰
   or its Ω-valued coefficient groups. No existing declaration loses ownership.
3. H9: removed all imports used only by future theorem proofs. Actual signature
   and construction imports remain public. Every delivered module is compiled
   separately through scompile.py.

## Second reading by NU

This is the required author self-reading; the dispatcher forbids starting other
agents and the maintainer supplies independent review. I reread the unchanged
mathematical node against both theorem signatures and the natural-comparison
record. Every hypothesis and clause is matched in the Worker report table.
The realization remains an actual inverse limit of the given integral system,
not an unconstrained chosen object; its rationalization retains the literal
finite coefficient field. The comparison is natural on the full localized lisse
category and fixes both ordinary and compact actions by their actual integral
functors at every field. Injectivity, fibrewise Ω-linearity, exact nonzero-fibre
locus and properness are unchanged. Empty X, zero sheaf/class, proper X,
affine A¹, and disconnected X remain covered.

I also read the new definition node with its module open: its three declarations
are exactly the integral functor, rational-localization/stage-inclusion object,
and point cohomology normalization stated there. The ordinary limit and exact
coefficient restriction preserve the maps; the point fibre uses its canonical
constant-to-completion action and inverse ULift transport. All data are explicit,
all variables and universes are bound, and the module has no postponed theorem.
For this repair I reread NX's module and dependency record alongside the
item's updated import. The original three NX declaration texts and its main
record fields remain identical to the base. Both appended helper declarations
retain exactly their previously reviewed signatures and bodies, including
independent universe `v`, finite-stage rational cohomology and canonical scalar
extension. Q43's original module is unchanged and still publicly imported.
The dependency note explicitly identifies NX's compact-only Weil-sheaf output
and the missing ordinary H⁰ and Ω-valued coefficient-module interface.
No mathematical statement correction was needed.

## Repair validation

The prescribed scompile.py compiled all three packet modules separately in
dependency order: CommonStageCompactWeilCohomology,
LisseIntegralCompletedRealization, and DegreeZeroCompactSupportSections.
Exit status was zero with no errors or warnings. The ownership self-check
compared NX's module and node with current main: its original declaration texts
and primary record fields are unchanged; the dependency node differs only in
lean, with both helpers added to declarations and the required note.

The first repaired dry run compiled all modules but rejected lean.by = NX on the
extended dependency record. The repair-author metadata is now NU; NX's module,
primary declaration, statement, file and original owned declarations remain
unchanged.
