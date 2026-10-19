## Worker report

Item: lem-coef-covariant-derived-replacement-base-change. Group: Q155.
Module: `Sheaf.CategoryTheory.CovariantDerivedReplacementBaseChange`.
Declaration: `SSet.CovariantDerivedReplacement.covariant_derived_replacement_base_change`.

The module states the node, with one postponed theorem and real definitions for its
specified data. All helpers belong to this node and are listed in `lean.declarations`.
The original mathematical statement, proof and proof dependencies are unchanged.
The two already-landed nodes `lem-coef-kan-diagram-localized-evaluation` and
`lem-coef-kan-diagram-evaluation-restriction` were added to statement dependencies:
the conclusion uses their exact evaluation and restriction definitions. Both were
already proof dependencies. No new independent notion or dependency repair is needed.

Source reading: HTT, https://www.math.ias.edu/~lurie/papers/HTT.pdf,
Theorem the project server and preceding Proposition the project server (ordinary straightening adjunction
and its base-change compatibility), Proposition the project server (enriched diagrams), and
Section 3.3.2. The statement is the covariant dual, as specified in the DAG.
The theorem docstring gives all nine steps of the DAG's natural-language proof,
including the adjunct calculations and both derived triangle calculations.

Hypotheses and clauses, in the order of the node:

1. Small quasicategory B: `Base := {B : SSet.{u} // B.Quasicategory}`. The conclusion
   is simultaneous over these B to state naturality. `P : SimplicialRightFibration.Presentation`
   supplies the dependency's ordinary covariant model presentation. Its
   `CovDiagram B`, `P.covariant B`, and `quillen.adjunction` use the actual
   rigidification of B, actual covariant unstraightening and its ordinary left adjoint.
   There is no extra simplicial-enrichment assumption on that adjunction.
2. Chosen localizations and replacements: input `m : ∀ B, Models P B` fixes only
   localization maps for the exact slice/projective weak-equivalence classes,
   ordinary functors Q and T, their natural augmentations q and t, cofibrancy of QX,
   fibrancy of TF, and weak-equivalence augmentations. It does not assume any
   conclusion, comparison, enriched replacement, or commutation with base change.
   Arbitrary weak-equivalence replacement augmentations suffice; the separate
   projective trivial-fibration replacement clause retains its stated hypothesis.
3. Derived formulas: `Derived (m B)` is the dependency's actual
   `ReplacementAdjunction` for that ordinary adjunction and precisely those Q,q,T,t.
   `LocalData.derived` supplies this data. In particular, its `leftComparison`,
   `rightComparison`, `unit_normalization`, and `counit_normalization` specify
   LQ, UT and the localized composites with q and t inverted. Its `coherent` field
   gives the actual unit/counit, adjunction triangles and mapping-space adjunction.
   The `left`, `right`, `unit`, and `counit` helpers only expose these existing fields
   with the correct model instances. No strict arrow into an unreplaced object is
   asserted in place of the localized counit.
4. Unit and counit are equivalences: `LocalData.unit_counit` uses
   `UnitCounitEquivalences`, asserting `Enhanced.IsEquivalenceEdge` of the actual
   unit and counit in the full internal-hom functor categories. This is equivalence
   of entire coherent transformations, not merely an objectwise or ordinary
   categorical assertion.
5. Objectwise Kan F and a projective trivial-fibration cofibrant replacement:
   `KanReplacement` quantifies over every F,G and a:G→F, with F objectwise Kan,
   G cofibrant, and a both a projective fibration and weak equivalence. It concludes
   that G is objectwise Kan, U(a) is the dependency's actual equivalence over B,
   its localized edge is an equivalence, and the actual chain-evaluation edge of a
   between the two Kan diagrams is an equivalence of entire coherent diagrams.
   `chain_evaluation` and `bifibrant_evaluation` fix which evaluation is meant on
   all simplices and identify its bifibrant comparison. No restriction-preserves-
   projective-cofibrancy hypothesis or conclusion is present.
6. Derived restriction under arbitrary f:B'→B: `FibrantPullback` fixes the underlying
   functor to actual `Over.pullback f`, including arrows, and preserves the exact
   restricted covariant weak class. `restriction_agreement` fixes enriched
   restriction to `P.covariant_base_change.restriction f`. The fields
   `left_localization`, `kan_localization`, `pullback_on_fibrants`, and
   `restrict_on_kan` give these functors on the selected localizations.
7. Actual base change, not an arbitrary equivalence: `base_on_kan` is a natural
   isomorphism on Kan diagrams; `actual_base_change` identifies each underlying
   component with `P.covariant_base_change.comparison f`. The `beta_normalization`
   pasting square fixes the derived beta against this particular transformation
   and the representative comparisons. `alpha_mate` specifies alpha by the actual
   three-factor derived mate: L'p eta, L' beta L, and epsilon' r L. The fields
   `unit_square` and `counit_square` give the two stated compatibility homotopies
   for these actual derived unit and counit edges.
8. Enriched evaluation and normalized equivalence: `enriched_evaluation`,
   `enriched_evaluation_equivalence`, and `evaluation_on_kan` give E with its
   entire chain-evaluation normalization. `gamma` and `gamma_normalization` fix
   its restriction comparison against strict precomposition of that evaluation.
   `normalized_equivalence` is exactly equivalence of the composite `left ≫ E`.
   `normalized_comparison` compares pullback followed by this composite with this
   composite followed by actual precomposition. `normalized_formula` requires it
   to be the pasting of E alpha and gamma L.
9. Coherence: `Coherence C` includes identity and composition comparisons of
   derived restriction, normalized on representatives against actual
   `Over.pullbackId`, `Over.pullbackComp`, and the strict enriched restriction
   identities. It specifies beta/alpha identity and composition, and gamma and
   normalized-comparison identity/composition laws. `Comparison` always has fixed
   endpoints and is an equivalence edge in the full functor simplicial set.
   `Pasting`, `Pastes`, and `Commutes` retain actual composition triangles there;
   `SameClass` includes equality of both endpoints and equality of the represented
   homotopy-category arrows. These express homotopies of whole transformations.
   The four `CoherentDescent` fields additionally quantify over every parameter
   simplicial set, requiring full functor-category equivalence and contractible
   normalized lift spaces. Thus transport includes higher simplices and parameter
   diagrams. The existing `ReplacementZigzags` and `ReplacementIndependence`
   clauses retain fresh replacements after restriction and their higher
   independence. No strict equality between replacement functors and pullback
   is substituted for this coherent assertion.

Dependency declarations read and used (all module paths below begin
`Sheaf.CategoryTheory.`):

- `EnhancedDiagramsCones`: `SSet.Enhanced.diagramVertex`, `IsEquivalenceEdge`,
  `IsFunctorEquivalence`, and its full internal-hom conventions; `smallSpaces` is
  the existing transitive space interface used by Kan-diagram evaluation.
- `InfinityFibrationsCartesianRepair`: recorded `SSet.Enhanced.pCartesianEdge`
  and its imported `SSet.Enhanced.leftFibration` interface; the latter is the
  full-subcategory predicate used by `LeftFibrations`.
- `SimplicialRightFibrationPresentation`:
  `SSet.SimplicialRightFibration.Presentation`, `CovDiagram`, `covKanProperty`,
  `covKanWeak`, `CovariantData`, `CovBaseChangeData`, and
  `IsOverHomotopyEquivalence`. Read the full presentation and its ordinary
  adjunction, Quillen criterion, left-fibration criterion and base comparisons.
- `ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.ReplacementAdjunction`, `CoherentAdjunction`,
  and `quillenAdjunctionInfinityLocalization`. The replacement interface is reused,
  with no private copy of the derived adjunction or its normalized formulas.
- `SimplicialModelNerveLocalization`:
  `CategoryTheory.simplicial_model_nerve_localization` and its inclusion/localization
  interfaces. Its full fibrant-subcategory universal property underlies the
  representative comparisons and the descent fields.
- `SimplicialProjectiveModelCalculus`:
  `CategoryTheory.ProjectiveSimplicialModelStructure` and
  `SimplicialDiagramEnrichment`; the projective model and enriched transformations
  are those supplied in the covariant presentation, not a duplicate definition.
- `EnrichedDiagramRectification`:
  `CategoryTheory.EnrichedRectification.enriched_diagram_rectification` and
  `DiagramComparison`, used through the specified chain and bifibrant evaluation.
- `KanDiagramLocalizedEvaluation`:
  `SSet.KanDiagramEvaluation.KanDiagrams`, `IsChainEvaluation`,
  `BifibrantAgreement`, and `kan_diagram_localized_evaluation`.
- `KanDiagramEvaluationRestriction`:
  `SSet.KanDiagramEvaluation.RestrictionSystem`, `CoherentDiagrams`,
  `ContractibleNormalizedLifts`, `lowerNerve`, `ReplacementZigzags`,
  `ReplacementIndependence`, and `kan_diagram_evaluation_restriction`.
- `PointwiseEquivalences` is imported for the existing proof dependency
  `lem-coef-infinity-pointwise-equivalences`; it is used in proof step 3.

Searches actually made for this delivery:

- msearch.py LeanFinder, `derived covariant unstraightening replacement unit counit
  commute with pullback`: eight general ordinary pullback-adjunction hits,
  including `CategoryTheory.ChosenPullbacksAlong.pullbackComp_hom_counit`, its
  associativity variant and the unit/pullback identity lemmas; no full statement.
- msearch.py Loogle, `"Quillen"`: twelve ordinary cochain-complex model-category
  hits such as `CochainComplex.Plus.modelCategoryQuillen.cm5a` and its model
  instances; none is the covariant infinity-localized comparison.
- msearch.py grep, `unstraighten|ReplacementAdjunction|covariant.*derived`:
  no Mathlib hits.
- msearch.py LeanSearch, `derived covariant unstraightening replacement unit counit
  commute with pullback`: eight ordinary Over/ChosenPullbacks/derived-adjunction
  hits, including `CategoryTheory.Adjunction.derivedη.congr_simp` and
  `CategoryTheory.Over.mapPullbackAdj_unit_app`; no exact statement.
- rg of the upstream `WeilConjectures` tree and shared `lean/Sheaf` for the item,
  declaration and `unstraighten|ReplacementAdjunction|covariant.*derived` found
  the prerequisite presentations and derived-adjunction interfaces, but no
  existing theorem with all the replacement, evaluation and base-coherence clauses.
- `grep -rn 'lem-coef-covariant-derived-replacement-base-change'` in the prescribed
  upstream `WeilConjectures` source returned no occurrence.

Edge cases checked by reading the explicit quantifiers and constructions:

- Empty B is allowed: Base requires only quasicategory, with no nonemptiness or
  chosen vertex. Empty indexing and empty diagram categories cause no extra binder.
- Identity f and arbitrary composites g≫f are retained explicitly in Coherence,
  against the actual pullback and restriction identifications.
- A Kan diagram need not be cofibrant. The replacement clause quantifies over a
  separate cofibrant G, and allows identity replacements when applicable.
- After restriction a former projective cofibrant object need not stay cofibrant:
  the existing fresh-replacement zigzags are included without such a hypothesis.
- The ordinary categories have object universe u+1 and morphism universe u;
  coherent localization models live in SSet.{u+1}. The nerve lifts are explicit;
  neither a small base nor its large diagram category is silently identified with
  a different universe.
- Ordinary replacements need neither enrichment nor strict compatibility with f.
  The normalization uses actual ordinary natural transformations and localization.

Validation: all compilation used the prescribed scompile.py wrapper, compiling
single files only. The final module passed both its sandbox check and its actual
module check without errors or warnings, within the 60-second file limit. No
proof beyond the one expected theorem `sorry` was added. All variables and
universes are explicitly bound. No STATEMENT-DISPUTED issue or source correction
remains. No repair-note file exists for this item in the prescribed shared path.

## Second reading by Q155

I reread the node and final module clause by clause after the successful compile.
This is a self-review: the dispatcher's instruction forbids starting other agents;
the maintainer's independent review remains separate.

The final reading checked the exact replacement-adjunction interface rather than
merely existence of arbitrary arrows. It checked that the unit/counit are its
actual normalized edges, that beta is tied to the actual unstraightening base
isomorphism, and that alpha is its specified counit mate. It checked the separate
projective trivial-fibration replacement clause, full chain evaluation, fresh
replacement after restriction, and identity/composition laws for St = E L.

During drafting, direct strict arrows and insufficiently normalized comparisons
were replaced by the dependency's full replacement-adjunction data and the actual
base-change and mate pastings. Potential assumptions that restriction preserves
projective cofibrancy were removed in favor of the supplied fresh replacements.
Composition is now expressed by real triangle simplices and homotopy classes with
explicit endpoint equalities, preserving the same formulas while avoiding large
elaboration transports. The final module passes its single-file compilation with
the default resource limits. The recorded theorem signature is copied verbatim
from the file, and all 34 named declarations are recorded. The mathematical node
statement has not changed.
