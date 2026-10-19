## Worker report

The module `Sheaf.CategoryTheory.SimplicialDerivedHomAdjunction` states
`CategoryTheory.simplicial_derived_hom_adjunction` with proof `sorry`.  It uses
`SimplicialDerivedHomAdjunction` as the complete conclusion record.  The record's
`lift` fields are Mathlib finite-string localization lifts, so the derived functors
are exactly `LQ` and `UR` followed by localization.

The theorem hypotheses render the node as follows.  `M` and `N` are categories with
model-category and simplicial-category structures, all limits and colimits, and the
four functorial factorization instances.  `_SM` and `_SN` supply the simplicial
model-category tensor/cotensor and SM7 corner-map conditions.  `eL` and `eU` are
enriched functors, `a` is their underlying enriched adjunction, and `E` together
with `_enriched_left`, `_enriched_right`, and `_vertex` is the natural isomorphism
of simplicial mapping sets and its compatibility with ordinary adjuncts.  `_cof`
and `_triv` state preservation of cofibrations and trivial cofibrations.  `Q`, `R`,
`c`, and `r` are functorial cofibrant and fibrant replacements; `_hQ`, `_hR`, `hc`,
and `hr` state their object and weak-equivalence properties.  `CM` and `CN` are
the mapping-component comparisons of the dependency.

The conclusion record gives Brown preservation (`left_inverts`, `right_inverts`),
the two localized functors and their adjunction (including naturality and triangle
identities), preservation of cofibrant/fibrant objects, and invertibility of the
replacement maps.  `hom_formula` is the composite
`Hom(qLP,qY) ≅ π₀ Map(LP,Y) ≅ π₀ Map(P,UY) ≅ Hom(qP,qUY)`; it uses `CN.equiv`,
`E`, and `CM.equiv` and is explicitly normalized on actual maps by `actual_map`.
`unit_formula` is `q(c_X)⁻¹ ≫ q(η_QX) ≫ q(U(r_LQX))`, and `counit_formula` is
`q(L(c_URY)) ≫ q(ε_RY) ≫ q(r_Y)⁻¹`.  The `right_quillen` field records the
right-adjoint equivalent preservation statement.  `left_agreement` and
`right_agreement` give natural isomorphisms with direct localizations when the
corresponding functor preserves all weak equivalences.

Dependency declarations used are:

* `CategoryTheory.simplicial_boundary_collapse_test` from
  `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest` for the model and
  Quillen preservation conventions.
* `CategoryTheory.SimplicialTensorCotensor` and its `tensorMap`/`parameterMap` from
  `Sheaf.CategoryTheory.SimplicialTensorCotensor` for enriched tensor/cotensor data.
* `SSet.KanQuillen.right_proper_kan_quillen` from
  `Sheaf.AlgebraicTopology.KanQuillenRightProper` for the Kan model structure.
* `CategoryTheory.SimplicialMappingLocalization` and
  `CategoryTheory.simplicial_mapping_localization` from
  `Sheaf.CategoryTheory.SimplicialMappingLocalization` for mapping components.
* Mathlib `CategoryTheory.Localization.Construction.lift`, `wInv`,
  `HomotopicalAlgebra` model-category predicates, `CategoryTheory.Adjunction`,
  `EnrichedFunctor`, and `SSet.mapπ₀`.

Edge cases checked: arbitrary (including empty) indexing is covered by the explicit
universe-polymorphic categories; replacement maps are only inverted under their
weak-equivalence hypotheses; identity and formal inverse arrows are handled by the
finite-string localization; zero-dimensional and empty simplicial sets remain in the
model-category hypotheses; the actual-map clause handles identity maps; no
bifibrancy assumption is imposed on arbitrary objects.

Searches for an existing declaration found no project or source declaration by
`rg -n 'derived.hom.adjunction|QuillenAdjunction|SimplicialAdjunction'`, and no
matching Mathlib declaration.  `msearch.py leanfinder` searched “Simplicial Quillen
adjunction gives derived adjunction with cofibrant fibrant replacements and unit
counit” and found only `CategoryTheory.Adjunction.derived`, which requires absolute
Kan-extension hypotheses and does not state this result.  `msearch.py loogle`
searched `"Adjunction.derived"` and `msearch.py grep` searched
`QuillenAdjunction|derivedAdjunction|SimplicialAdjunction`; neither found a match.
The file compiles cleanly with `scompile.py`.

## Second reading by Q29

Independent maintainer reading of immutable delivery
`f43bc9e1c893d4778fe2e41f6b4ea3a43689459f`, 2026-10-17.
The mathematical statement and Lean module require no change. This replacement
records the actual clause-by-clause reading; the accompanying lean-record JSON
registers both helper declarations as well as the theorem.

I read the item and all four statement-dependency nodes in the immutable snapshot,
the delivered module and this report. I read the dependency Lean sources in the
read-only Q29 clone: SimplicialBoundaryCollapseTest, SimplicialTensorCotensor,
KanQuillenRightProper and SimplicialMappingLocalization, including their module
and declaration docstrings. I also read the reused cornerMap/SatisfiesSM7 in
SimplicialModelNerveLocalization and the Mathlib declarations listed below.

The source is blueprint main-20261015, sec-six-functors/sk-thm-sf-package/
prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2 and its concluding
unit/counit paragraph. It asks for derived coefficient adjunction and compatible
adjunction maps. The present ordinary prerequisite is agent-supplied; the blueprint
does not itself state a general simplicial Quillen theorem. The parent
lem-coef-simplicial-projective-model-calculus, Step 15, uses precisely its ordinary
mapping-component, replacement and direct-localization conclusions. No statement
correction or citer audit under section 1(C) is needed.

Hypotheses checked:

- `M : Type u`, `N : Type u'`, `Category.{v}`, `ModelCategory`, the four
  `HasLimits`/`HasColimits` instances and the four functorial-factorization
  instances render the inherited model-category conventions. Mathlib's
  ModelCategory alone only supplies finite limits/colimits and nonfunctorial
  factorization; the additional instances are therefore appropriate here.
- `SimplicialCategory` identifies ordinary arrows with mapping vertices.
  `_SM` and `_SN` use the existing `SimplicialModelCategoryData`, whose fields
  are the dependency's real tensor/cotensor universal elements and the existing
  SM7 predicate. Its corner map is the pullback lift of precomposition and
  postcomposition. Its fibration predicate is horn lifting, with realization
  weak equivalence if either input is weak, as in the Kan dependency.
- `eL`, `eU`, `E`, `_enriched_left`, `_enriched_right` express enriched functors
  and the two enriched naturality equations. `a` and `_vertex` identify their
  ordinary adjunction with the vertex restriction of `E`; they do not assume a
  second unrelated adjunction. `simplicialOrdinaryFunctor` is the literal
  composite of Mathlib's canonical ordinary/enriched identifications and
  `EnrichedFunctor.forget`, not an arbitrary arrow assignment.
- `_cof` and `_triv` say exactly that the left functor preserves cofibrations
  and trivial cofibrations. The right-hand version is a conclusion, not an
  additional assumption. Transposition of lifting squares proves the stated
  equivalence of formulations.
- `Q`, `R`, `c`, `r`, `_hQ`, `_hR`, `hc`, `hr` give functorial cofibrant
  replacement in M and fibrant replacement in N, with weak comparison maps.
  Neither arbitrary X nor arbitrary Y is assumed bifibrant. The weak maps need
  not themselves be trivial fibrations/cofibrations, which the node does not
  require for the chosen replacements.
- `CM` and `CN` are the dependency's actual component comparisons, including
  vertex normalization. Naturality and composition written on vertices extend
  to all components because every component has a vertex. No saturation or
  bifibrant-localization hypothesis is added beyond those comparisons.

Conclusions checked against `SimplicialDerivedHomAdjunction`:

- `left_inverts` and `right_inverts` assert inversion by the localized composites
  `Q ⋙ L ⋙ qN` and `R ⋙ U ⋙ qM`. The derived functors in `adjunction` are
  Mathlib `Localization.Construction.lift` of exactly those composites.
  Mathlib's construction is the quotient of finite arrow/inverse strings.
- `cofibrant_left`, `fibrant_right`, `right_quillen`, and the two replacement
  `IsIso` fields are valid intermediate consequences, not stronger premises.
- `hom_formula` uses `CN.equiv.symm`, `SSet.mapπ₀ (E P Y).hom`, and `CM.equiv`
  in the required order. Its input is precomposed with `qL(c_P)` and its output
  postcomposed with `qU(r_Y)`, exactly the required replacement identifications.
  `actual_map` explicitly identifies the value with the original ordinary adjunct.
- `unit_formula` is `q(c_X)⁻¹ ≫ q(η_QX) ≫ q(U(r_LQX))`.
  `counit_formula` is `q(L(c_URY)) ≫ q(ε_RY) ≫ q(r_Y)⁻¹`.
  Both inverses are the actual formal inverses of the weak replacement maps.
  `adjunction` supplies naturality and both triangle identities on all
  localization arrows, not only on arrows represented by single actual maps.
- `left_agreement` and `right_agreement` give natural isomorphisms with direct
  finite-string localization under preservation of all weak equivalences;
  the components are respectively `qL(c_X)` and `qU(r_Y)` with correct directions.

Proof documentation and dependencies checked:

The theorem has one proof, exactly `by sorry`, and its docstring contains all
eight node steps. Step 1 uses the two model weak factorization systems and
adjunction. Step 2 uses the split Brown factorizations (Mathlib BrownLemma,
CofibrantBrownFactorization and FibrantBrownFactorization); the section/retraction
and two-out-of-three arguments are valid. Step 3 descends on finite strings.
Steps 4-5 use the mapping comparisons to define
`Φ(a) = B(q(r_Y) ∘ a) ∘ q(c_X)⁻¹`. Naturality follows on
actual arrows from the replacement squares, on inverse arrows by cancellation,
and on strings by induction. Mathlib `Adjunction.mkOfHomEquiv` supplies the
adjunction. Steps 6-8 give the displayed comparison, unit/counit and direct
agreement. I recomputed their endpoints and directions. There is no missing
helper construction or new DAG prerequisite requiring repair.

One-definition searches and exact declarations:

I searched Mathlib, the Q29 project's Sheaf tree, and upstream WeilConjectures
with `rg` for QuillenAdjunction, SimplicialAdjunction, derivedAdjunction,
derived/hom/adjunction combinations, and both new helper names. The report's
recorded LeanSearch, LeanFinder and Loogle searches were also read; the unknown
Loogle identifier is not evidence of absence. Mathlib Functor/Derived/Adjunction,
`Adjunction.derived` (lines 137-149), requires derived Kan-extension hypotheses
not supplied by a one-line specialization here. Localization/Adjunction requires
both original functors already to descend. Upstream's derived-adjunction
transport result also starts with absolute derived functors. The project's
ModelInfinityDerivedAdjunction theorem concerns coherent infinity localizations
and does not provide this ordinary finite-string component formula. No exact
existing declaration or duplicated underlying notion was found. Existing tensor,
SM7, mapping-comparison and localization notions are reused.

Edge cases and universes:

I checked the identity Quillen pair, already cofibrant/fibrant objects, empty
mapping sets, identity and formal inverse arrows, and the case that only one
original functor preserves all weak equivalences. Nothing assumes pointedness
or identifies the initial and terminal objects. Empty and zero-dimensional
simplicial sets remain among the tensor parameters. There is no indexing-set or
characteristic restriction. Object universes u and u' remain independent. The
shared hom universe v is the common simplicial enrichment base required by an
enriched adjunction, not an equality of object and morphism universes. Finite-string
localizations may have larger Hom universes; the assumed component comparisons
are equivalences between these types, not a silent size restriction. The module
sets `autoImplicit false`; all variables and universes are bound.

Mechanical findings and corrections:

- The delivered lean record omitted `simplicialOrdinaryFunctor` and
  `SimplicialDerivedHomAdjunction` from `lean.declarations`. The complete
  replacement lean record registers them and the theorem (helper-record rule
  in check-brief2/section 1; H2 record completeness).
- The original second-reading paragraph enumerated topics without the actual
  checks (H11). This complete report replacement preserves the Worker report
  and supplies this independent reading.
- `lean.statement` is identical to the module signature under the whitespace
  normalization explicitly used by stage2_delivery.py. No token changed.
  There are no lines over 100 characters in the Lean file. Module, helper and
  theorem docstrings have source locations and the owning blueprint marker.
  The abbrev has real data, the structure specifies concrete output data and
  properties, and no definition extracts arbitrary data from an uncharacterized
  existence assertion. There is no local proof beyond the one theorem's sorry.

Compiler evidence:

Reproduced the reported compile using
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q29
lem-coef-simplicial-derived-hom-adjunction
snapshot/lean/Sheaf/CategoryTheory/SimplicialDerivedHomAdjunction.lean`.
Exit code 0; no errors or warnings. The installed wrapper announced server
compilation and compiled the dependency overlay SimplicialMappingLocalization
in 1.8 s, the sandbox file in 1.9 s, and the library-module check in 2.6 s, each
with its 60-second limit. This is the current prescribed wrapper behavior, not
an independently invoked ssh command. No Lean source changed, so a further
compile of metadata/report changes is unnecessary. No global build, live Lean
write, Git mutation, delivery or merge was performed. All corrections are in
the maintainer review's fixes directory.
