## Worker report

Repair of L's independent review of immutable head `4e2f6bcdeb00`. The saved packet was inspected first and its prescribed dry run passed at `bd451825d8` without a push. That check established shape and compilation only: the saved definitions really were zero-valued, as the return said. This delivery replaces their data. Current shared-main node and the saved node were compared without Git: before this repair their only differences were `lean`, `statement`, and `statement_change`. The current nine-step proof and its dependencies are preserved.

The module is `Sheaf.Paper.ConnectedConstantH0`, declaration `WeilConjectures.connected_constant_h0`. It states the finite, completed, and rational clauses on the recorded ordinary cohomology objects. The three postponed propositions are the main theorem, compatibility of the actual projections, and existence/uniqueness of the integral unit with its finite-unit projections. All three are clauses of this same DAG statement and have source/proof docstrings. Every definition has actual data; the integral unit is chosen from a uniqueness statement specifying every projection, rather than from mere existence.

Hypothesis correspondence:

- The datum `(p,a,q,k₀,k)` is `D : FiniteFieldDatum.{u}`; its fields contain primality, the positive exponent, the cardinality equation, the finite base field, and its chosen algebraic closure.
- The distinct prime is `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- The finite extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Integers, uniformizer, and quotients are the recorded `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing`.
- The k-scheme is `(Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]`. Finite type is `[LocallyOfFiniteType (Y ↘ Spec (.of D.k))]` together with `[QuasiCompact (Y ↘ Spec (.of D.k))]`.
- Separatedness is explicitly bound in the theorem as `[IsSeparated (Y ↘ Spec (.of D.k))]`. Nonempty connectedness is `[ConnectedSpace Y]`, which extends preconnectedness with `Nonempty Y`; the empty scheme is excluded.
- The site is Mathlib's small `Scheme.ProEt` with its topology. The coefficients are exactly `finiteCohomologyCoefficient`, `integralCohomologyCoefficient`, and `rationalCohomologyCoefficient` used by the recorded `finiteOrdinaryCohomology`, `integralOrdinaryCohomology`, and `rationalOrdinaryCohomology`. There is no substitute cohomology carrier.

Clause correspondence:

1. `connectedFiniteH0SectionsIso` identifies finite H⁰ with actual point sections of the underived direct image of the regular coefficient sheaf. It is the composition of `Functor.mapDerivedCategoryHomologyFunctorIso`, `Functor.homologyRightDerivedFunctorObjSingleFunctorIso`, and `Functor.rightDerivedZeroIsoSelf`; this is the resolution-augmentation identification in the node. Its section carrier is evaluation over the base change of the point's final object, canonically Y. `connectedFiniteCoefficientIso` removes only the predecessor cast in the published coefficient object. `oneFinite` transports the actual ring section `1` through the inverse of this H⁰ identification. `unitMap` is `LinearMap.toSpanSingleton` applied to that class, hence sends a to a times the unit class. The first two conjuncts assert `unitMap ... n 1 = oneFinite ... n` and bijectivity for every n.
2. `connectedIntegralImage` makes exactly the Roos choice used in `integralImage`; its product and object are the same, with proof-irrelevant instance arguments. `connectedFiniteTowerIso` applies the recorded identity-on-sections restriction comparison, then the derived image of the actual `constantCoefficientReductionMap`, then the harmless positive-index coefficient identification. `connectedFiniteTowerH0Iso` takes H⁰ and commutes exact scalar restriction with H⁰. `Q n` conjugates H⁰ of `sfDirectImageTransition` by these identifications. `P n` takes H⁰ of point sections of `connectedIntegralImage.projection ≫ Pi.π ... n` and follows it with this same identification. These maps are constructed from the requested arrows, with no zero-map fallback. `connectedH0_projections_compatible` states `Q n (P (n+1) x) = P n x` with `sorry`; `limitTuple` uses that named proposition to enter `connectedH0Tower`, the subtype of genuinely compatible finite tuples. The main theorem repeats compatibility explicitly and states bijectivity of `limitTuple`. `connectedH0_integral_unit_existsUnique` specifies the unique integral class with every projection equal to `oneFinite`; `oneIntegral` is that class. The next two conjuncts give every `P n oneIntegral = oneFinite n` and bijectivity of `a ↦ a • oneIntegral`, identifying the limit with O_E through constant coefficients.
3. `rationalTensorComparison` is the actual `pointRationalNormalization` at `rationalImage ... Y (rationalCohomologyCoefficient ...)`. `rationalH0TensorIso` takes its H⁰, commuting exact fraction-field tensor, coefficient restriction, and carrier lift with H⁰. It also uses the recorded pure-tensor-normalized `pointFibreRationalDownIso`. Its source is E tensor integral H⁰, presented by `ModuleCat.extendScalars (pointIntegralToField l E)` with ULift coefficients and then the canonical coefficient-down functor; it is the tensor in the node, with the factors interchanged by the tensor symmetry. `rationalH0TensorMap` removes only the target carrier ULift using `ULift.moduleEquiv`. The theorem asserts bijectivity of this actual E-linear H⁰ map. `oneRational` is its image of the pure tensor `1 ⊗ oneIntegral`; the theorem includes that formula explicitly. The last two conjuncts normalize `rationalScalarMap 1` and assert its bijectivity. The former `Nonempty`-iso conjunct is gone; `rationalTensorComparison` is used in the construction.

Localization sizes were checked explicitly with `#print`/`#check` through `scompile.py`. Recorded finite sections use the standard localization with Hom universe u+2; recorded integral cohomology uses Hom universe u+1; recorded rational cohomology uses Hom universe u. `connectedH0IntegralModuleDerived` and `connectedH0FieldModuleDerived` expose exactly the already-recorded Grothendieck small-Hom localizations. `connectedSectionsRestrictionIso` transports the published *ordinary* identity-on-sections square through exact localization at those precise sizes. It does not assert an equality of universes or change either site's universe. This is a helper for the canonical map in this owning node, not a replacement dependency statement.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
- Mathlib `Topology.Connected.Basic`: `ConnectedSpace`; Mathlib scheme morphism files: `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`; Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` (current recorded reexport of `Sheaf.Paper.OrdinaryCompactCohomology`): the three ordinary cohomology/sections constructions, `integralImage`, `rationalImage`, and the three coefficient objects.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfDirectImageTerm`, `sfDirectImageTransition`, `SfIntegralDirectImage.projection`; the recorded `sfIntegralDirectImage_constructible` makes the same Roos choice as ordinary cohomology.
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible`: `finiteConstantCoefficientObject`, `constantCoefficientReductionMap`, `integralConstantCoefficient_constructible`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the recorded completed constant maps, reexporting the completion and projection constructions used by those dependencies.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `finite_coefficientExtensionRing` and its unchanged coefficient-ring constructions.
- `Sheaf.Paper.SfRationalizationKaroubi`: the unchanged raw rationalization and localization objects.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient`, `pointRationalNormalization`, `pointFibreRationalDownIso`, `pointFibreCoefficientDown`, `pointIntegralToField`, and the exactness instances.
- `Sheaf.Paper.PointReductionUnits`: `pointUnitIntegralRestriction`, `pointUnitIntegralSectionsRestrictionIso`. This newly cited *existing* node supplies the actual identity-on-sections square; the module's larger derived target is transported locally, using its ordinary square, to the recorded integral H⁰ localization.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`, Mathlib's `CategoryTheory.Abelian.RightDerived`, and `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: the augmentation and exact homology comparisons named above.
- Proof-only imports retain the recorded derived-limit, coefficient-tower transition, Milnor, adic-completeness, Grothendieck-resolution and continuous-functions-sheaf inputs.

Edge cases: n=0 is exponent one and Q 0 reduces exponent two to exponent one; all positive levels occur. Empty Y cannot satisfy `ConnectedSpace Y`. Nonreduced connected schemes and E=ℚ_l are allowed. No smoothness or properness hypothesis is added. The finite unit section is the actual section 1 before any connectedness theorem, so the old zero-map counterexample is removed. The integral unit has a unique fully specified inverse-limit characterization. Rationalization is at the actual Y-dependent image, and the actual tensor map, rather than an arbitrary isomorphism, is used. No extra equality between site or coefficient universes is imposed.

Searches retained from the saved packet were rechecked against current sources. Repair searches actually run:

- `msearch.py` LeanFinder, “canonical degree zero constant sheaf cohomology on a connected scheme unit section”: eight hits, on scheme sections/structure-sheaf constants and generic sheaf sections; no exact three-clause statement.
- `msearch.py` LeanSearch, “degree zero cohomology of a constant sheaf on a connected scheme is the coefficient ring”: eight hits on `Sheaf.H` and group-cohomology H⁰/invariants. They concern different constructions and do not state this lemma.
- `msearch.py` Loogle, `Functor.mapDerivedCategoryHomologyFunctorIso, Functor.homologyRightDerivedFunctorObjSingleFunctorIso, Functor.rightDerivedZeroIsoSelf`: no hit; unknown first identifier in Mathlib's index. The first two actual APIs are project declarations, whose sources were opened directly.
- `msearch.py` grep, `homologyRightDerivedFunctorObjSingleFunctorIso|mapDerivedCategoryHomologyFunctorIso`, subdirectory `CategoryTheory`: zero hits; their project-source declarations were found by direct `rg`.
- `rg` over upstream `WeilConjectures`, Mathlib, and current shared `lean/Sheaf` for the item, connected-constant declarations, unit/augmentation, exact H⁰ comparisons, `pointUnitIntegralSectionsRestrictionIso`, and rational comparison names. It found the reusable augmentation and scalar-restriction APIs described above, and no duplicate of this item or its new helper names.
- `rg -l '"lem-pod-connected-constant-h0"' dag/nodes`, followed by JSON inspection of actual stmt/proof dependencies, confirmed exactly four citers. The constant-tower-transition node also mentions the item in metadata, but is not a citer by either dependency field.

## Returned points repaired

1. Replaced `oneFinite := 0`, `Q := 0`, and `P := 0` by the actual augmentation unit class, H⁰ transition, and H⁰ Roos projection. Replaced `oneIntegral := 0` by its unique fully specified finite-unit preimage. `oneRational` is the image of its actual unit tensor. Scalar maps use those classes.
2. Replaced the old `simp [Q, P]` compatibility proof in `limitTuple` by the named statement-only `connectedH0_projections_compatible`; included the same compatibility as a conclusion of the main theorem.
3. Removed the inhabited `Nonempty` comparison conjunct. Added bijectivity of `rationalH0TensorMap`, built from H⁰ of `rationalTensorComparison`, and the `1 ⊗ 1` normalization. The comparison is now used.
4. Every helper, including both localization aliases and every newly needed coefficient/projection comparison, has a source-place docstring and `(blueprint: lem-pod-connected-constant-h0)`. Every postponed theorem has a natural-language proof in its docstring and matches a clause of this DAG node.

## Statement corrected

The original TeX is preserved verbatim as `statement_change.old_statement`. The saved correction, which the return accepted, names the finite units, projection maps, and actual tensor comparison instead of arbitrary existential maps. This repair clarifies that the finite class uses the resolution augmentation, explicitly writes Q_n composed with P_(n+1)=P_n, and cites the existing identity-on-sections coefficient restriction node used in its canonical construction. It changes no blueprint unit, hypothesis, coefficient object, or desired isomorphism. The source remains Bhatt--Scholze Lemma 4.2.12, Milne pp. 124/126, and current main-20261015 cohomological-finiteness Proof Step 7. The nine-step DAG proof and its dependencies are unchanged.

The four-citer audit accepted by the return is retained; no citer file is edited:

- `lem-pod-frobenius-fixes-unit-section` — `holds: false`: its use must refer to the repaired finite/integral unit projections and actual rational unit-tensor map.
- `prop-cohomological-finiteness` — `holds: false`: Step 9 must consume the repaired actual scalar-to-H⁰ isomorphism.
- `lem-coef-finite-point-internal-hom-evaluation` — `holds: false`: its point reconstruction must consume the repaired augmentation/constant-section normalization.
- `lem-pod-point-completed-evaluation` — `holds: false`: its point completed-section identification must consume the repaired projection comparison.

## Repair self-check by NR

I reread the node with the repaired module open, matching every hypothesis and the three clauses as above. The old zero data, fake compatibility proof, unused rational comparison, and inhabited comparison conjunct are removed. A signature check confirms the node record matches the main theorem verbatim; every helper is listed in `lean.declarations`. This is the author's self-check. The maintainer supplies the independent reading under the dispatcher brief.

Validation is recorded below after the final clean compilation and delivery preflight.

Final `scompile.py NR lem-pod-connected-constant-h0 lean/Sheaf/Paper/ConnectedConstantH0.lean` passed with no errors or warnings: sandbox 6.3 s, library-path check 7.1 s. The proof-only constant-tower-transition overlay also compiled cleanly in 5.5 s. The module has three named statement-only `sorry` proofs and no `sorry` data. All source lines are at most 100 characters.

Required `deliver2.py NR lem-pod-connected-constant-h0 --no-push` passed at `96ab87d88b`: preflight and compilation passed, nothing pushed. Final record checks confirmed that the old statement and old dependency list are retained verbatim in `statement_change`, the current nine-step proof and proof dependencies are unchanged, the four-citer audit is complete, and the recorded signature matches the source exactly.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
