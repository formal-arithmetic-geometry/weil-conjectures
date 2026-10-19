## Worker report

Existing match: `SSet.Enhanced.Algebroid.algebroid_equivalence_nerve`, in
`Sheaf.CategoryTheory.AlgebroidEquivalenceNerve`, published under
`lean/Sheaf/CategoryTheory/AlgebroidEquivalenceNerve.lean:785` on `newtargets-dag`.
Its full signature and the definitions appearing in it were read. The item records
`existing: true` and introduces no duplicate item module, definition, theorem or proof.
A prerequisite module is included for the compiler annotation repair described below. The existing
statement is postponed with `sorry`; this is a stage-2 statement match, not a claim that
its proof has been completed. The node's natural-language statement and proof dependencies are unchanged. Its
statement dependencies gain the already landed `lem-coef-space-valued-straightening`
to deliver that interface repair under brief-stage2 §1(B) and §5.

The node already carried the NX interface and a passed independent Lean review. The
repair note for this item was also read: its stage is 1, its state is resolved, and it
explicitly asks that the statement and Lean record's mathematical interface be retained.
There is no released stage-2 defect to repair. No statement correction is needed.

Clause-by-clause comparison with the published Lean:

1. Presentably monoidal coefficients are represented by the explicit universe parameters
   `u v`, `E : SSet.{max (u + 1) v}`, `[Quasicategory E]`, the operadic projection `p`,
   and `hp : IsPresentablyMonoidal.{u, v} p`. The recorded predicate includes monoidality,
   presentability and preservation of small colimits separately in both tensor variables.
   `unit : UnitSection p` specifies the coherent tensor-unit representative, with its
   over-base equation and cocartesian unit constraints. It does not assume completeness
   or symmetry of the monoidal structure.
2. Algebroids are exactly vertices of `total p` from the recorded complete-algebroid
   dependency. The finite unit algebroids are `unitAlgebroid unit n`, constructed together
   by `unitCosimplicial unit`. `iotaLevel unit A n` is the recorded right-pinched model of
   `Map(E^n,A)`. The higher coherent version is `nerve unit A`, obtained by restriction of
   the existing two-variable `CategoryTheory.Spaces.yonedaPairing` to the opposite unit
   diagram. `nerveBifunctor` retains postcomposition in every simplex.
3. `IsNerveRealization unit` asserts a coherent augmented bifunctor extending
   `nerveBifunctor`, with a colimit cocone for every algebroid and apex precisely the
   already recorded `iota unit A`. Thus the realization is the specified object, rather
   than an arbitrary equivalent space introduced as a hypothesis.
4. `∀ A, IsEquivalenceGroupoid unit A` quantifies over every
   `GeometricDescent.Square ⥤ SimplexCategoryᵒᵖ` satisfying `IsGroupoidCover` and asserts
   `IsLimitingConeAt squareLegs` for its restriction of the nerve. That dependency's
   predicate requires injective increasing enumerations, union equal to the entire
   ordinal, singleton intersection, and bottom-right ordinal of length zero. This is
   exactly the restriction pullback for all nonempty ordered subsets in the node,
   including interleaved subsets rather than only adjacent intervals.
5. For one tensor-unit object label `r₀`, the two equivalence conclusions on
   `objectEvaluationSource unit r₀ A` and `objectEvaluationTarget unit r₀ A` give the
   canonical identification of `I_0(A)` with `objects A = U(A)`. Their common source is
   `objectEvaluationResolution`, constructed from the actual singly pointed total
   category. The existential `q` is a two-sided homotopy inverse to the specified
   `nervePinch` map from right mapping spaces to fixed-endpoint arrow mapping spaces;
   it is concluded, not assumed. The final biconditional in that clause is
   `IsComplete unit A ↔ IsWeakHomotopyEquivalence (...)`, where the composite runs from
   this resolution through `q`, singular realization's unit and `completenessMap` to
   `iota unit A`. Transport across the two evaluation equivalences is precisely the
   canonical `U(A) → I(A)` criterion.
6. `r₁ : Fin 2 → ObjectPoint (unitAlgebroid unit 1)` with
   `IsTwoObjectLabeling unit r₁` labels the two components of `E^1`. For all `x y`,
   `equivalenceFiber unit r₁ A x y` is the mapping space in `pointedTotal p 2` from
   the labeled `E^1` to `(A,x,y)`. It retains the endpoint identifications. The map
   `equivalenceEvaluation` evaluates the actual coherent algebra transformation into
   `unitMaps unit A x y = Map_V(1,A(x,y))`. `invertibleUnits` is its full subcomplex
   on the components containing coherent equivalences. The conclusion gives a weak
   equivalence `j` to that subcomplex and requires its composite with inclusion to be
   exactly `equivalenceEvaluation`.
7. The universally quantified pointed-algebroid edge `f` with hypothesis
   `IsFullyFaithful ((forgetPoints p 2).app _ f)` induces two `basedArrowLeg` maps.
   Both are asserted to be weak equivalences. The source leg identifies the mapping
   space to the source pointed algebroid; the target leg is postcomposition. This is
   the induced equivalence between the two specified `I_1` fibers under a fully
   faithful map, retaining all endpoint paths.
8. For every unpointed edge `f`, the biconditional
   `IsEssentiallySurjective unit (algebroidArrow f) ↔ EveryObjectInImage unit r₁ f`
   is exactly the two forms of essential surjectivity. The dependency defines the
   left side as surjectivity of the induced components map on the canonical iota
   postcomposition span. The right side quantifies over every target object and
   provides an actual object-family edge over the object-space map, together with
   a point of the equivalence fiber to that image object.
9. The next clause assumes both `IsFullyFaithful f` and that essential-surjectivity
   predicate, and concludes that the target leg `iotaMorphismLeg ... 1` is a weak
   equivalence. The source leg of this canonical postcomposition span is the usual
   equivalence to the source realization. Hence this says `I(F)` is an equivalence.
10. `IsFullyFaithful f → IsEquivalenceEdge transportSpaces f.val.space →
    IsEquivalenceEdge (total p) f` is exactly conservativity for a fully faithful
    algebroid map whose object-space map is an equivalence; it imposes no completeness.
11. The final universal clause takes an actual point `a` of the equivalence fiber and
    every third object `z`. It concludes the existence of both actual composition
    edges in `E`, with `IsEnrichedAction ... 0` and `IsEnrichedAction ... 1`, respectively,
    and asserts `IsEquivalenceEdge E e` for each. The action predicate fixes the inert
    factor squares, active composition square and cocartesian unitors. The conclusion
    therefore concerns the enriched mapping objects themselves, on both sides.
12. Naturality is carried by the actual simplicial maps and coherent categories, not
    by arbitrary maps supplied as hypotheses: `nerveBifunctor`, its augmented extension
    in `IsNerveRealization`, the universal pointed families, their evaluation formulas
    in every degree, and the operadic composition squares keep the higher simplices.
    The only inverses selected in the theorem's conclusion witness equivalences of
    these specified canonical maps.

Dependency declarations read and used by the existing statement:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: in namespace `SSet.Enhanced.Algebroid`,
  `total`, `UnitSection`, `unitCosimplicial`, `unitAlgebroid`, `universalFamily`,
  `familyPower`, `homObject`, `iotaLevel`, `iota`, `completenessMap`, `IsComplete`,
  `completeCategory`, `iotaMorphismLeg`, `IsEssentiallySurjective`, `IsFullyFaithful`,
  and `IsPresentablyMonoidal`. The main recorded declaration is `completeCategory`;
  the statement uses the companion declarations in that same recorded interface.
- `Sheaf.CategoryTheory.InfinityPresheafYoneda`:
  `CategoryTheory.Spaces.infinityYoneda` and its uncurried `yonedaPairing`, whose
  full signature, construction and source docstrings were read.
- `Sheaf.CategoryTheory.SpaceGeometricDescent`:
  `SSet.Enhanced.GeometricDescent.space_geometric_descent`, and its `index`,
  `indexMap`, `IsGroupoidCover`, `IsLimitingConeAt`, `IsColimitCocone`, `point`,
  `squareLegs` and augmented-index interfaces. The complete theorem signature and
  its proof docstring were read; no private replacement of the cone condition is used.
- `Sheaf.CategoryTheory.AlgebroidTerminalSpacePairing`:
  `SSet.Enhanced.Algebroid.terminalSpacePairing`, definitionally the recorded
  `CategoryTheory.Spaces.yonedaPairing`. Its source and full signature were read.

Edge cases checked: an algebroid with empty object space has vacuous pointwise fiber
and action assertions, but its essential-surjectivity predicate still detects failure
of a map from the empty space to a nonempty target. Empty source and empty target are
not excluded by any nonemptiness binder. Repeated labels `x = y` retain their endpoint
paths in `equivalenceFiber`. The case `n = 0` and covers with one singleton subset are
included by the ordinal cover predicate. All ordered-subset covers, not just Segal
interval covers, are allowed. Independent coefficient universes `u v` are retained;
no equality of object and morphism universes has been imposed. Composition is asserted
in `E` over the underlying monoidal fiber, without requiring a mapping-space functor
to detect equivalences.

Searches performed with `msearch.py Q11 lem-coef-algebroid-equivalence-nerve`:

- LeanFinder query: "The simplicial space Map(E n,C) of equivalences in an enriched
  infinity category is a groupoid object, whose realization detects completeness and
  fully faithful essentially surjective equivalences". Eight results concerning
  simplicial enrichment and `SSet.QCat`; none states this theorem.
- Loogle query: `SSet.Enhanced.Algebroid.algebroid_equivalence_nerve,
  IsEquivalenceGroupoid, IsNerveRealization`. Zero results; the first project-specific
  identifier is unknown to the Mathlib service.
- Mathlib grep query: `algebroid_equivalence_nerve|IsEquivalenceGroupoid|IsNerveRealization|
  equivalence nerve`, directory `CategoryTheory`. Zero results.
- Direct `rg` searches of the upstream `WeilConjectures` tree for the theorem name,
  predicates and blueprint id found no declaration there. Searching the project's
  `lean/Sheaf` found the exact existing module, including its main theorem at line 785
  and its groupoid and realization predicates at lines 563 and 578.
- The blueprint id was also searched in `dag/lean_names_upstream.json`; no upstream
  attachment was found.

The source place was opened at https://arxiv.org/html/1312.3178 and the named results
in Sections 5.1–5.3 checked against the node's references. No new source interpretation
or statement correction is introduced. No disputed statement was found.

Validation: the existing-declaration probe is compiled with the required `scompile.py`
wrapper. `deliver2.py --no-push` additionally checks the imported declaration and runs
server preflight. No global build or direct repository mutation is used.


## Dependency modules

`lem-coef-space-valued-straightening` owns
`Sheaf.CategoryTheory.SpaceValuedStraightening`. The existing-declaration probe and
first dry run both failed in that published module at `Diagrams` (line 64):
`lean.dependsOnNoncomputable`, because `smallSpaces` is noncomputable. The sole Lean
edit marks this abbreviation `noncomputable`; its data, universe, type and expansion
are identical. The dependency's node is copied with only `lean` changed, with this
reason in `lean.note`. It is already a landed node with a Lean interface, so the item
may cite it directly and include the repaired dependency module. This is required to
import the recorded algebroid interface through its space straightening prerequisite.

The repaired dependency continues to state its entire original node: small left
fibrations have the coherent diagram object `Diagrams B`; `Straightening.map` is the
classification equivalence, with Kan mapping objects and base pullback naturality.
`BaseNaturality` retains the coherent natural transformation on the nerve of all
quasicategory bases. `IsOrdinaryComparison` quantifies over every small ordinary
category, supplies the adjunction on all strict simplicial-set diagrams, and requires
`CommaPresentation` with both projections, their pullback property and both variable
actions. Its counit is objectwise weakly equivalent for every objectwise Kan diagram.
For every weak equivalence from the explicit left adjoint value of a left fibration
to a strict Kan-valued diagram, it compares the same global straightening with
`IsStrictCoherentNerve` of that diagram. `IsComparisonNatural` keeps both variable
naturality. The final theorem remains
`∃ S : Straightening, Nonempty (BaseNaturality S) ∧ ∀ C [Category C],
IsOrdinaryComparison S C`, proved only by the pre-existing `sorry`. Empty categories,
empty fibers, non-Kan adjunction inputs and non-projectively-cofibrant Kan diagrams
remain included. No new theorem or mathematical helper is introduced. Its node,
recorded declaration and entire module, including source and proof docstrings, were
read before making this annotation-only repair. All dependency imports are retained.

After the annotation repair, `scompile.py` passed for the delivered prerequisite
module and the existing-declaration import probe together, separately in dependency
order. It also rebuilt the affected algebroid import chain, including the existing
`AlgebroidEquivalenceNerve` module, cleanly. No compiler errors or warnings remained.
The added statement citation was checked for a reverse dependency path; none exists.

## Second reading by Q11

Independent maintainer reading of immutable delivery
`9e6e7a8c91d0eceb0e7b7133892687fc32d66c9a`, performed by Codex on 2026-10-17.
This section records the maintainer's reading, not a claim that the worker reviewed itself.

Read packet.md, check-brief2.md in full, the stage-2 brief and delivery-errors H,
the immutable item and all five statement-dependency nodes, the delivered
SpaceValuedStraightening module, and the reused AlgebroidEquivalenceNerve module
including its helpers and fourteen-step theorem docstring. The four other dependency
modules were read as well. The read-only clone's reused modules were checked byte for
byte against the delivery commit; they agree. The delivered straightening file was
read from the snapshot, since the read-only clone still has the unannotated abbreviation.

Clause comparison (names below are in SSet.Enhanced.Algebroid unless qualified):

| Node clause | Lean rendering and independent verdict |
| --- | --- |
| Presentably monoidal V and its algebroids | `IsPresentablyMonoidal.{u,v} p`, `UnitSection p`, and `total p`; the unit section specifies coherent unit constraints. No symmetry, completeness, or extra finiteness assumption. Correct. |
| E^n and simplicial mapping spaces | `unitCosimplicial`, `unitAlgebroid`, `iotaLevel`, and `nerveBifunctor`; the last restricts the existing two-variable Yoneda pairing. Correct. |
| Realization in spaces | `IsNerveRealization` supplies a coherent colimit augmentation with the already defined `iota` as apex. Correct. |
| All one-vertex ordered-subset covers | `IsEquivalenceGroupoid` uses the recorded `IsGroupoidCover` and `IsLimitingConeAt squareLegs`; injectivity, union, singleton intersection and increasing enumeration are present. Correct. |
| I_0 = U and completeness | The two canonical `objectEvaluation` legs identify the same resolution with the mapping space and the object fiber; `q` is concluded as an inverse of the specified pinch. The composite in the biconditional uses the recorded `completenessMap`. Correct. |
| Equivalence fiber and invertible components | `equivalenceFiber` is the pointed-total mapping space, so endpoint paths are retained. `equivalenceEvaluation` is uniquely fixed in every degree; `j` factors this actual map through `invertibleUnits` and is a weak equivalence. The definition of invertible components by extensions through E^1 agrees with GH Definitions 5.1.8 and 5.1.16. Correct. |
| Fully faithful maps on equivalence fibers | Both `basedArrowLeg` maps are asserted weak equivalences under the recorded `IsFullyFaithful` predicate. This expresses postcomposition as a canonical span. Correct. |
| Essential surjectivity | `EveryObjectInImage` uses an actual universal-family lift over the object's map and an equivalence-fiber point; `IsEssentiallySurjective` is the recorded surjectivity on components of the iota span. Correct, including empty source. |
| Fully faithful and essentially surjective | The target `iotaMorphismLeg` is a weak equivalence. Correct. |
| Fully faithful plus object-space equivalence | The conclusion is `IsEquivalenceEdge (total p) f`, without a completeness assumption. Correct. |
| Composition on either side | `IsEnrichedAction` fixes the inert factor squares, active composition square and cocartesian unitors. Both concluded `e` are equivalences in E, representing the underlying enriched category. Correct. |
| Naturality | The nerve and its augmentation use full coherent bifunctors; pointed families, evaluation formulas, and algebra operation squares retain higher simplices. No arbitrary comparison map is assumed. Correct. |

The dependency repair changes only `abbrev Diagrams` to `noncomputable abbrev
Diagrams`; its type and body are identical. Its theorem still asserts global coherent
straightening, Kan mapping objects, coherent base naturality, and the ordinary-base
adjunction on all simplicial-set diagrams. `CommaPresentation` fixes both projections,
their pullback and both actions; reducing the subset quotient to pairs (simplex, final
arrow) gives this same comma pullback. Kan hypotheses occur only where the node puts
them, and the comparison applies to every objectwise weak equivalence into a Kan
diagram, without projective cofibrancy. No mathematical interface changed.

Sources checked: Gepner--Haugseng arXiv:1312.3178v4, Sections 4.3--4.4 and 5.1--5.3,
particularly Definitions 5.1.6, 5.1.8, 5.1.13 and 5.1.16, Propositions 5.1.15 and
5.1.17, Definition 5.2.3, Theorem 5.2.5, Corollaries 5.2.7 and 5.2.10,
Lemmas 5.3.2, 5.3.4 and 5.3.5, Proposition 5.3.6 and Lemma A.5.5;
Rezk arXiv:math/9811037, Theorem 6.2; HTT 2.2.1.2 and 3.2.5.5--3.2.5.21.
The source permits exactly the hypotheses used. The item statement and fourteen proof
steps are unchanged by this delivery; no section 1(C) correction or citer audit is needed.

Edge cases checked: empty object spaces and targets, repeated endpoint labels,
n = 0, a singleton side of a cover, interleaved subsets and an interior common
vertex, empty ordinary categories and fibers, and non-Kan inputs to the ordinary
adjunction. Independent universes u and v remain bound; max (u+1) v provides the
ambient size without forcing them equal. Searches using equivalence-nerve names and
synonyms in Mathlib, upstream WeilConjectures and lean/Sheaf found the existing
project theorem and no competing upstream definition; the worker's semantic and
Loogle search records were read. The terminal pairing and hom-object conveniences
reuse their recorded definitions. The added straightening dependency has no reverse
path to the item: traversal of statement and proof dependencies with the snapshot
records overlaid on the read-only context reached 655 nodes and no missing IDs.

Both lean.statement fields equal their file signatures after whitespace normalization.
All variables and universes are explicitly bound, and neither relevant module has a
line longer than 100 characters. Source/blueprint docstrings are present. The delivered
module has only the pre-existing named theorem with `sorry`; there is no hollow data,
new proof, arbitrary map assumption, or pro-etale substitute. Chosen evaluation maps
in the reused module have unique full-simplex characterizations.

Compiler reproduction: the prescribed scompile.py wrapper returned exit 0 for the
snapshot SpaceValuedStraightening file alone (library check 15.6 s), then for that
file together with the unchanged, commit-verified AlgebroidEquivalenceNerve module.
The combined run rebuilt the private overlay's straightening, relative-nerve,
complete-algebroid and object-space-fibration imports, checked both preliminary
modules and both probes, and checked the two library modules (6.8 s and 14.5 s).
There were no errors or warnings. The installed wrapper currently delegates to a
server-side private overlay; no direct ssh command or alternate compiler was used.
No global build, clone edit, live Lean write, claim, delivery or merge was performed.

Finding and correction: H1/H11, the original second-reading section contained only
a disclaimer. It is replaced by this actual independent reading. The Worker report
is retained in full. No Lean or JSON correction is required. The complete replacement
report is supplied as `fixes/lem-coef-algebroid-equivalence-nerve.report.md`, a filename
accepted by tools/merge_delivery.py --stage 2 --apply-fixes.
