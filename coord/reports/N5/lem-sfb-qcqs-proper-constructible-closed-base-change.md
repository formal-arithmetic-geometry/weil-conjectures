## Worker report

The main module `Sheaf.Paper.QcqsProperConstructibleClosedBaseChange` states
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_constructible_closed_baseChange`.
Its sole theorem has proof `by sorry`; no theorem is proved. The same item module defines
`AlgebraicGeometry.ProEtale.IsNormTopologicalLocalizingAdmissibleCoefficient`, a real
Prop-valued predicate for precisely the six coefficient cases of the item, and lists it
in the item record's `lean.declarations`. It publicly imports the original closure
interfaces. There are no new nodes, dependency modules, or statement corrections.

Source read: the item's complete six-step proof and statement; blueprint main-20261015,
`sec-six-functors-basics/sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md`,
paragraph (2); and `sec-proetale-coefficients/sk-def-localizing-closure/_section.md`.
The first source invokes closed-complement proper base change on the Dctf generators.
The node explicitly formulates its stronger qcqs/full-coefficient scope as an agent claim,
not as the theorem of a narrower literature source. This delivery preserves that scope.
No repair-note file exists for this item.

The statement-to-Lean correspondence is as follows.

| Hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Commutative condensed ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ] [IsCommMonObj Λ]` |
| Exact admissible discrete/induced ell-adic list | `hΛ : IsNormTopologicalLocalizingAdmissibleCoefficient ℓ Λ` |
| Finite ell-power-annihilated commutative ring | First disjunct: `A : Type`, `CommRing A`, `Finite A`, `DiscreteTopology A`, `IsTopologicalRing A`, and `∃ n, ∀ a, (ℓ ^ n) • a = 0` |
| Z_ell and Q_ell | Condensed-ring isomorphisms with `Profinite.continuousMapRingObj ℤ_[ℓ]` and `Profinite.continuousMapRingObj ℚ_[ℓ]` |
| Finite E inside the fixed algebraic closure | `E : PadicAlgCl.FiniteIntermediateField ℓ`, with its induced subfield topology |
| E and O_E | `Profinite.continuousMapRingObj E` and `Profinite.padicIntegersRingObj ℓ E`; the latter uses the induced topology on `PadicAlgCl.integers ℓ E` |
| Norm-topological algebraic closure | Final disjunct is exactly `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`, allowing all continuous sections |
| Coefficients Lambda_T = p_T^* Lambda | Existing `condensedRingObj Λ T` in every internal module category |
| Ordinary unbounded D_T | Existing `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))` |
| Size convention | Explicit universe `u`, schemes `Scheme.{u}`, site object/Hom universes as in the upstream small pro-etale site, coefficient sheaves in `Ab.{u + 1}`; existing derived-category instances infer the larger derived universe |
| qcqs scheme S | `[CompactSpace S] [QuasiSeparatedSpace S]` |
| Proper Y over S | `(q : Y ⟶ S) [IsProper q]` |
| Proper f | `(f : X ⟶ Y) [IsProper f]` |
| Closed c | `(c : C ⟶ Y) [IsClosedImmersion c]` |
| Quasi-compact complementary open immersion | `[QuasiCompact (Scheme.Opens.ι (X := Y) ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩)]` |
| X_C and a, f_C | Exactly `pullback f c`, `pullback.fst f c`, `pullback.snd f c` |
| Chosen Cartesian identification | Inline `ChosenCartesianSquare` with `pullback.condition`, `Iso.refl _`, and the two `Category.id_comp _` equations; this is actual real structural data, not an additional hypothesis |
| Every bounded constructible finite-Tor L | `(L : ConstantModelConstructibleFiniteTor Λ X)`; `L.obj` is the ambient object |
| Finite constant scalar-model constructibility | This subcategory uses `constantModelBoundedConstructible`, then `IsConstantModelConstructible`, `IsFiniteConstantStratified`, and `HasFiniteConstantLocalModel` from the dependency module |
| Finite Tor amplitude | The same subcategory intersects with the existing `DerivedCategory.finiteTorAmplitude _` |
| Canonical map is an isomorphism | `IsIso ((condensedAmbientExchange Λ ...).app L.obj)` |
| Source c^* Rf_* L | By the imported definition, `(lowerStar Λ f).rightDerivedFunctor` followed by `(upperStar Λ c).leftDerivedFunctor` |
| Target R(f_C)_* a^* L | By the same definition, `(upperStar Λ (pullback.fst f c)).leftDerivedFunctor` followed by `(lowerStar Λ (pullback.snd f c)).rightDerivedFunctor` |
| Exact inverse image with pulled-back rings | Existing `upperStar` is the full tensor module inverse image; its left-derived functor is the dependency's pullback. The pulled-back coefficient comparison is canonical, and this inverse image is exact. No separate coefficient action or arbitrary comparison is supplied. |
| No further geometric assumptions | No field, characteristic, Noetherian, dimension, or density binders occur. No qcqs assumption is added on X, Y, C, or X_C. |

Using an existential finite intermediate subfield to describe the coefficient family covers
all choices of E in the node; the theorem is universal in Λ. Ring isomorphisms are in `Mon`
of condensed abelian groups, so they preserve additive and multiplicative structure. The
finite-ring binder `Type` loses no isomorphism class, since any finite ring has a small
finite representative. The finite-ring case includes the zero ring and exponent zero.

Statement-dependency declarations read and used:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, whose extra final
  finite-subextension-valued clause requires the item-specific coefficient list. Existing
  `CategoryTheory.localizingClosureOfSize` and `IsLocalizingSubcategoryOfSize` are retained.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback`; both are the full ordinary total derived functors,
  definitionally the functors used by `condensedAmbientExchange`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor` and its above-listed
  constituent definitions. Read the full definitions and their docstrings.
- `def-weil-size-convention`: metatheoretic convention; no declaration is required.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, extending separated, universally closed, locally finite type.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and `Morphisms.QuasiCompact`, `QuasiCompact`.
  They occur through properness and the complementary open's compactness condition.
- `def-weil-quasi-separated-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated` and `quasiSeparated_iff_quasiSeparatedSpace`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, with its closed embedding and surjective stalks.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the canonical `Scheme.Opens.ι` is an open immersion.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and `pullback.condition`.
- `def-weil-pbc-ambient-ringed-exchange`: `Sheaf.Paper.CondensedAmbientExchange`,
  `AlgebraicGeometry.ProEtale.CondensedRing.condensedAmbientExchange` and
  `condensedAmbientPullbackComparison`. Read both complete definitions and docstrings.
  The first is literally the derived-adjunction mate of the second, which is the
  canonical derived pullback composition comparison. Thus invertibility is asserted of
  the prescribed map, rather than of an arbitrary arrow or only its endpoints.

All already stated proof-dependency modules are imported non-publicly unless they are
also statement imports. The five currently unstated proof nodes are
`lem-sfb-qcqs-integral-finite-model-completeness`, `lem-sfb-integral-ambient-tower-comparison`,
`lem-sfb-integral-quotient-exchange-comparison`,
`lem-sfb-qcqs-rational-integral-localizing-generators`, and
`lem-sfb-qcqs-proper-integral-rational-scalar-comparison`. They are not needed to type this
statement; their six-step argument is preserved in the theorem docstring. No missing
statement dependency was left unstated.

Edge cases checked before writing: the zero complex and zero coefficient ring remain
allowed; an empty S, X, Y, or C is allowed whenever the displayed arrows exist; C = Y
with c the identity is allowed (empty complement); C empty is allowed whenever its
complementary open is quasi-compact. The complementary open is not replaced by its
reduced closed complement, so nonreduced closed immersions are included. Non-Noetherian
and infinite-dimensional qcqs bases are not excluded, and no invertibility of ell on S
is imposed. Tor amplitude has no fixed common interval and the complex has no prescribed
cohomological bound; the existing subcategory existentially supplies its own bounds.
The exact coefficient predicate excludes no item case and does not replace continuous
algebraic-closure sections by finite-subextension-valued sections.

Searches actually run:

- `msearch.py ... leanfinder`: “Proper base change along a closed immersion for bounded
  constructible complexes of finite Tor amplitude over condensed coefficients on the
  pro-etale site”. Eight hits: stability of closed immersions/properness/finite type,
  and unrelated condensed monoidal results; no matching derived exchange theorem.
- `msearch.py ... loogle`: `IsProper, IsClosedImmersion, IsIso` returned an unknown
  identifier diagnostic, so this query was inconclusive; qualified names were retried.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsClosedImmersion`
  returned the two proper-monomorphism characterizations of closed immersions, not the item.
- `msearch.py ... grep`: `(baseChange|base_change).*(IsProper|isProper)|IsIso.*[Cc]losed`
  in `AlgebraicGeometry` returned seven geometry-only hits, not a derived sheaf exchange.
- `msearch.py ... leansearch`: “Admissible condensed coefficients finite ell power
  torsion rings ell-adic integers finite extension valuation rings fields and all
  continuous functions into the algebraic closure”. Eight valuation/adic-ring hits,
  no exact admissibility predicate.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id, closed/base-change
  patterns, coefficient predicates and all-continuous algebraic-closure coefficients.
  No exact item declaration. The upstream module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` was opened:
  its E and finite-subextension-valued algebraic-closure statements require schemes of
  finite type and separated over a field of positive characteristic different from ell,
  so they do not state this node. `RefinementBoundaryVanishing` has similar field
  hypotheses and states vanishing rather than the item. The two existing admissibility
  predicates both differ in their finite-subextension-valued algebraic-closure clause.
- Read the precise upstream continuous-map coefficient constructions and the definition
  of `PadicAlgCl.FiniteIntermediateField`; the latter bundles finite-dimensionality
  inside the fixed algebraic closure, and the former distinguish the two Qbar sheaves.

There is no concrete counterexample or typing defect in the item's statement, and no
STATEMENT-DISPUTED claim is made. The six-step proof remains postponed in full.

## Return repair

The return on immutable head `1ea465a1fe70` identified H13/H4: the previous delivery
reassigned `sk-def-localizing-closure` to a coefficient predicate and orphaned its
localizing-closure module. Its node file is now restored byte-identically from live,
including Q90's three declarations and the existing repair note. The item imports
`Sheaf.Paper.LocalizingAdmissibleCoefficients` directly. The separate
`NormTopologicalAdmissibleCoefficients.lean` delivery module is removed.

The six-case `IsNormTopologicalLocalizingAdmissibleCoefficient` now belongs to the item
module and is listed in the item's `lean.declarations`, as the return requests. It uses
the existing ring constructions; the last disjunct is all continuous norm-topological
algebraic-closure sections. There is no `padicAlgClRingObj` disjunct. The theorem's
signature, geometric hypotheses, canonical exchange arrow, and six-step proof docstring
are unchanged. No localizing closure or shared dependency interface is redefined.

## Second reading by N5

This section records the writing worker's own second pass with the item file and node
statements open; an independent reading is left to the maintainer, as the dispatch brief
requires and prohibits starting other agents. The coefficient pass checks the six
disjuncts against the item list; the extra final clause of the imported broader predicate is excluded by the item-owned predicate.
The returned dependency-record reassignment is repaired as described above. The geometric
pass matched q and f proper, the qcqs base, the closed immersion and the quasi-compact inclusion of precisely its open complement.
The categorical pass checked that `L.obj` inhabits the correct ordinary module-object
D(X), and that the canonical projection square gives the actual mate in D(C).
Compilation initially found that field projection `.ι` on the literal topological open
was unresolved; this was corrected to the explicit `Scheme.Opens.ι (X := Y)` with
exactly the same open. No hypothesis or conclusion changed. Both theorem and definition
have explicit universe and variable binders, no local notation or instances, and all
lines are at most 100 characters. The sole `sorry` is the item's theorem proof.

## Validation

The mandatory initial dry run on the saved packet passed mechanically (commit
`8f74141ca2c`), but retained the independently reported H13/H4 defect; the repair above
therefore follows the maintainer's concrete return. The dependency node copy matches
live byte-for-byte and every non-`lean` item field matches live. The theorem signature
in `lean.statement` is verbatim from the module and is unchanged from the return.
Both declarations explicitly bind their variables and universe; the only `sorry`
is the item's theorem proof, and no line exceeds 100 characters.

`scompile.py` compiled the single delivered module cleanly in both namespaces:
sandbox 5.1 s, library 5.3 s. No errors or warnings occurred.
The repaired `deliver2.py --no-push` run returned OK at `be02faf913a`, passing server
preflight and compilation. Its staged paths are only the item node, item module, and
report; the restored dependency node is absent from the diff.
No global build, direct live-library write, or direct Git command was run.
