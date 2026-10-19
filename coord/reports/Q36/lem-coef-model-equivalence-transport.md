## Worker report

The module `Sheaf.CategoryTheory.ModelEquivalenceTransport` states all clauses of
`lem-coef-model-equivalence-transport` in five named theorems. Each proof is exactly
`sorry`; every theorem has the relevant steps of the node's eleven-step proof in its
docstring. Two helper declarations express this node's parameter and coherence
hypotheses. They contain real definitions/data and belong to this node's interface.
There are no new DAG nodes, dependency repairs, or statement corrections.

Hypotheses and clauses:

- Ordinary categories and a chosen equivalence/quasi-inverse are `{C : Type u}`,
  `{D : Type u'}`, independent `Category.{v}` and `Category.{v'}`, and `E : C ≌ D`.
  `E.inverse`, `E.unitIso`, and `E.counitIso` are the chosen adjoint-equivalence data.
- The given model structure is `[ModelCategory D]`. Completeness/cocompleteness in
  the convention of the marked-model dependency are explicit
  `HasLimitsOfSize.{w,w} D` and `HasColimitsOfSize.{w,w} D`; `w` is arbitrary and
  independent of both category universes. `hD : CombinatorialModelCategory D`
  supplies local presentability, small generators and both functorial factorizations.
  Left properness is exactly `hproper : (weakEquivalences D).
  IsStableUnderCobaseChangeAgainst (cofibrations D)`.
- `model_equivalence_transport` returns `M : ModelCategory C`, with each of its
  three classes equal to the corresponding `inverseImage E.functor`. Its subsequent
  clauses give combinatoriality, completeness, cocompleteness, and left properness.
  ModelCategory supplies the finite model axioms and weak factorization systems;
  CombinatorialModelCategory supplies their functoriality and set generation.
- Local presentability is recorded explicitly by
  `IsLocallyPresentable.{w} C ↔ IsLocallyPresentable.{w} D`. Fibrancy is detection of
  the fibration property of `hT.from X`, for every terminal object `(T,hT)`; the
  target is the canonical terminal arrow of `E.functor.obj X`. Cofibrancy uses
  every initial `(A,hA)` and `hA.to X`. Quantifying over these universal objects is
  equivalent to the usual IsFibrant/IsCofibrant definitions and adds no hypothesis.
- For every `I.IsSmall.{w}` with `I.rlp = trivialFibrations D`, the literal image
  `I.strictMap E.inverse` is small and its right lifting class is the transported
  trivial fibrations. The same clause for `J.rlp = fibrations D` gives the other
  system. The left classes are determined by these right classes in the already
  asserted model structure. `strictMap`, rather than Mathlib's iso-closed `map`,
  is essential: an iso closure need not remain small in a large category.
- `factorization_transport` applies to each chosen `FunctorialFactorizationData`
  of the two systems. Its middle functor is naturally isomorphic to
  `E.functor.mapArrow ⋙ F.Z ⋙ E.inverse`. The two displayed equations normalize
  its legs to `eta_X ≫ G(i_Ef)` and `G(p_Ef) ≫ eta_Y⁻¹`. Naturality of the middle
  isomorphism also specifies its maps on squares. The class assumptions
  `W₁.RespectsIso`, `W₂.RespectsIso` hold for both model-system pairs.
- In the additional simplicial clause, `[SimplicialCategory C]` and
  `[SimplicialCategory D]` are the specified enrichments. Their shared hom universe
  `v` is the universe of the given common parameter category `SSet.{v}`; their
  object universes remain independent. `TC` and `TD` are the existing enriched
  `SimplicialTensorCotensor` interfaces, not newly chosen enrichments.
- `R : SSet ≌ SSet` with `[R.functor.Monoidal]` expresses a strong monoidal
  equivalence for the cartesian structure. `IsKanParameterEquivalence R` states
  preservation AND reflection of monomorphisms (Kan cofibrations) and the exact
  `SSet.Enhanced.IsWeakHomotopyEquivalence` from the dependency.
- `TwistedComparisons.mapping` is `R(Map_C(X,Y)) ≅ Map_D(EX,EY)`, equivalently
  the node's inverse-R formula. `tensor` and `cotensor` are exactly its two object
  comparisons. `ordinary` respects every ordinary arrow and in particular enriched
  identity units; `composition` respects enriched composition using R's monoidal
  comparison. These equations imply naturality of `mapping` in both variables.
  `tensor_unit` and `cotensor_counit` compare the universal elements of the chosen
  enriched representing adjunctions. Thus they enforce compatibility with the
  actual tensor/cotensor adjunctions and their induced maps, units and iterates;
  the naturality/coherence diagrams follow by their universal properties. They
  are not unconstrained object isomorphisms.
- `simplicial_equivalence_transport` assumes the three inverse-image class equations
  and the given axiom `TD.SatisfiesPushoutProductAxiom`. It concludes that same axiom
  for TC. In addition, for EVERY pair of arrows i,j and their canonical pushout
  products q,r (specified by the existing `IsPushoutProduct` restriction equations),
  it gives `Arrow.mk (E.functor.map q) ≅ Arrow.mk r`. This is an isomorphism of
  the whole arrow, not only its endpoints; no cofibrancy restriction is imposed
  on this detection clause. The axiom includes triviality when either input is weak.
- `identity_and_opposite_parameters` includes both the actual categorical identity
  equivalence and Mathlib's `SSet.opEquivalence`: each has a strong cartesian
  monoidal structure and the two preservation/reflection conditions. The general
  simplicial theorem therefore covers both whenever the specified comparisons exist.
- `quillen_adjunction_transport` quantifies over two equivalences, both ordinary
  adjunctions `L ⊣ U`, `L' ⊣ U'`, and their left comparison
  `L ⋙ E₂.functor ≅ E₁.functor ⋙ L'`. Its right comparison is the adjoint mate.
  The cofibration/weak-equivalence inverse-image equations and `hQ` express the
  given Quillen adjunction. Its conclusion says L preserves cofibrations and
  trivial cofibrations, precisely the Quillen condition for the already supplied
  adjunction. The fibrations are determined by the model weak factorization
  systems; their equality is not an additional necessary assumption for this test.

Dependency interfaces read and reused:

- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`,
  `SSet.Marked.marked_point_cartesian_model` and `CartesianModelStatement`: the
  conventions of model structure, functoriality, small generators and enrichment.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, `SSet.Enhanced.coneCategory`
  and especially `SSet.Enhanced.IsWeakHomotopyEquivalence`: the underlying
  simplicial sets and realization-based Kan weak equivalences.
- `Sheaf.AlgebraicTopology.SimplicialOppositeHomotopyCalculus`,
  `SSet.simplicial_opposite_homotopy_calculus`: the actual order-reversal involution.
- Added landed dependency `def-coef-simplicial-tensor-cotensor`, module
  `Sheaf.CategoryTheory.SimplicialTensorCotensor`, declaration
  `CategoryTheory.SimplicialTensorCotensor`, its `tensorMap` and `parameterMap`.
- Added landed dependency `lem-coef-model-colimit-localization-comparison`, module
  `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`, existing
  `HomotopicalAlgebra.CombinatorialModelCategory`. Its full recorded theorem was
  also read; only its already-defined model hypothesis interface is used here.
- Added landed dependency `lem-coef-simplicial-sm7-generator-extension`, module
  `Sheaf.CategoryTheory.SimplicialSM7GeneratorExtension`, existing
  `CategoryTheory.SimplicialTensorCotensor.IsPushoutProduct` and
  `SatisfiesPushoutProductAxiom`. The recorded generator-extension theorem and its
  proof docstring were read. These three added dependency edges were checked for
  a path back to this item; none closes a DAG cycle.
- Proof dependencies: `ModelCategory.transport` in Mathlib's ModelCategory.Transport;
  `Equivalence.toAdjunction` and equivalence-preservation of limits/colimits from
  the Mathlib adjunction imports; `Equivalence.isLocallyPresentable` in
  Mathlib.CategoryTheory.Presentable.Adjunction; opposite calculus, subdivision
  comparison and Kan-Quillen modules. Every stated proof-dependency module is
  imported directly or exposed by a statement-dependency import.

Edge cases checked: empty diagrams and initial/terminal objects; empty generating
sets; identity equivalences; arbitrary non-skeletal equivalent categories (literal
image required for smallness); empty simplicial sets; nonfibrant inputs in the
arrow comparison; both triviality cases of the pushout-product axiom; identity and
order reversal of simplicial parameters. No nonemptiness or cofibrant-generator-domain
assumption is added. All universes and binders are explicit; `autoImplicit false`.

Searches on 2026-10-17:

- `msearch.py leansearch`: "model category equivalence transport simplicial left
  proper combinatorial" returned eight hits, including ModelCategory.mk', the Kan
  model class interfaces, Monoidal.Transported, and homotopy facts; no complete match.
- `msearch.py leanfinder`: "Transport a left proper combinatorial simplicial model
  category along an equivalence with twisted simplicial tensor enrichment" returned
  eight hits on Kan class interfaces, ModelCategory.mk'/finite axioms, and hoFunctor
  monoidality; no complete match.
- `msearch.py loogle`: "ModelCategory.transport, Equivalence.isLocallyPresentable"
  returned zero hits (unknown unqualified ModelCategory.transport). Direct source
  inspection found both fully qualified Mathlib declarations, but neither states
  the additional left proper, generators, functorial and twisted simplicial clauses.
- `msearch.py grep`: "transport|LeftProper|IsLeftQuillen" in
  AlgebraicTopology/ModelCategory returned four lines in Transport.lean. Its full
  declaration and docstring were read: it transports only the finite model axioms.
- `rg` in WeilConjectures and lean/Sheaf for model-transport phrases and the item id
  found unrelated transport constructions and no full statement. Searches for
  CombinatorialModelCategory, SimplicialTensorCotensor and pushout-product definitions
  found the reused modules above. Searches of Mathlib, WeilConjectures, lean/Sheaf
  and dag/lean_names_upstream.json for the proposed namespace and declaration names
  found no collisions. Inspection of MorphismProperty.Basic and IsSmall confirmed
  that the generator image must use the existing strictMap.

Validation: scompile.py compiled the sandbox module and its actual library path
successfully, with no errors or warnings. Five theorem proofs remain sorry as
required by stage 2. No statement dispute or source fault was found.

## Second reading by Q36

No independent worker reading: this dispatcher brief requires direct delivery and
forbids starting another agent; the maintainer supplies the independent review.
The author reread the node and module clause by clause as recorded above. This
caught the need to use literal `strictMap` for the small generator images, rather
than the iso-closed `map`. The final check retains all three transported classes,
both generator systems, normalized functorial factorizations, both simplicial
triviality cases, the entire pushout-product arrow, identity and opposite parameters,
and the concluding Quillen-adjunction clause. The original natural-language
statement and proof are unchanged.

### Independent second reading (maintainer reviewer, cc review service, 2026-10-18)

The paragraph above was the author's own reread, not an independent one (delivery-errors
H11). This subsection records an independent reading done with the node, the dependency
modules and the file open. No Lean was changed.

Node clauses and their Lean:

1. Ordinary categories, an equivalence `E` with chosen quasi-inverse `G`:
   `{C : Type u} {D : Type u'}`, `Category.{v}`/`Category.{v'}`, `E : C ≌ D`,
   `G = E.inverse`, unit/counit `E.unitIso`/`E.counitIso`. Correct, and all universes
   are independent.
2. `D` has a left proper combinatorial model structure: `[ModelCategory D]`,
   `hD : CombinatorialModelCategory.{u',v',w} D` (the landed interface of
   lem-coef-model-colimit-localization-comparison), and left properness
   `hproper : (weakEquivalences D).IsStableUnderCobaseChangeAgainst (cofibrations D)`,
   which is the project-wide convention. `HasLimitsOfSize/HasColimitsOfSize.{w,w} D`
   follow from local presentability, so they add no strength. Correct.
3. The inverse-image classes form a left proper combinatorial model structure:
   `∃ M : ModelCategory C` with three class equations, `@CombinatorialModelCategory C _ M`
   and the left-properness clause. Correct.
4. `E` detects fibrant and cofibrant objects: two clauses comparing `hT.from X` and
   `hA.to X` with `terminal.from (E X)` and `initial.to (E X)`, quantified over every
   terminal and initial object. Correct.
5. `G(I)` and `G(J)` generate: for every `w`-small `I` with `I.rlp` equal to the trivial
   fibrations (and `J` with `J.rlp` equal to the fibrations), `strictMap E.inverse` is
   small and has the transported right class. This is the generating convention of
   lem-coef-marked-point-cartesian-model, and the left classes are determined by these
   right classes. `strictMap` is needed: the iso-closed `map` need not be small. Correct.
6. Local presentability is preserved:
   `IsLocallyPresentable.{w} C ↔ IsLocallyPresentable.{w} D`. Correct.
7. Functorial factorizations come from `E`, `G`, unit and counit: `factorization_transport`
   asks for a middle object naturally isomorphic to `G ∘ Z ∘ E` and for both legs equal to
   `η_X ≫ G(i_{Ef})` and `G(p_{Ef}) ≫ η_Y⁻¹`. This is true, taking `ζ = id`. Its hypotheses
   `RespectsIso` hold for the model classes. Correct.
8. The simplicial hypotheses:
   - `[SimplicialCategory C/D]` are the given enrichments; `TC` and `TD` are the landed
     `SimplicialTensorCotensor` interface; `hD : TD.SatisfiesPushoutProductAxiom` is the
     landed simplicial axiom.
   - `R` is `R : SSet ≌ SSet` with `[R.functor.Monoidal]` (strong, cartesian) and
     `IsKanParameterEquivalence R`. That predicate requires preservation and reflection of
     monomorphisms and of `SSet.Enhanced.IsWeakHomotopyEquivalence`.
   - The three comparisons are `TwistedComparisons`. `mapping` goes in the forward
     direction; this is equivalent to the node's `R⁻¹` formula.
   - The `ordinary` and `composition` equations express respect for units and for
     enriched composition.
   - `tensor_unit` and `cotensor_counit` compare universal elements. `tensorMap` and
     `parameterMap` are defined from those elements, so these equations force the
     naturality the node assumes, and no more.
   - Typing was checked by hand. A shared hom universe `v` is forced by Mathlib's
     `SimplicialCategory`, since both mapping objects live in one `SSet`. This is not a
     silent restriction.
9. Conclusion of the simplicial clause: `TC.SatisfiesPushoutProductAxiom` for the
   inverse-image model structure, fixed by `hc/hf/hw`. Also, for all `i` and `j`, the
   canonical pushout products satisfy `Arrow.mk (E q) ≅ Arrow.mk r`, which is detection
   under `E`. Correct. The Lean does not repeat the combinatorial and left-proper
   hypotheses here. The argument does not use them, so this is a harmless generalisation
   that specialises to the node.
10. Identity and order-reversal parameters: `Equivalence.refl` and `SSet.opEquivalence`.
    `SSet.opEquivalence.functor = SSet.opFunctor` holds by `rfl` (checked by compiling).
    This is the involution of lem-coef-simplicial-opposite-homotopy-calculus. A
    `Nonempty` strong monoidal structure is enough, because a strong monoidal structure
    between cartesian categories is unique. Correct.
11. Quillen transport: `quillen_adjunction_transport` assumes both adjunctions, the
    comparison `L ⋙ E₂ ≅ E₁ ⋙ L'`, inverse-image cofibrations and weak equivalences, and
    `hQ` (L' is left Quillen). It concludes that `L` preserves cofibrations and trivial
    cofibrations. Neither Mathlib nor the project has a separate Quillen-adjunction
    notion. Correct.

Edge cases:
- Empty diagrams and initial/terminal objects: handled by quantifying over every such
  object.
- Empty generating sets are allowed.
- Non-skeletal `C`: `strictMap` keeps the generators small.
- Arrows that are not cofibrations are included in the detection clause.
- Both triviality cases of the pushout-product axiom are covered.
- The identity and `op` parameters are both covered.

Records:
- `lean.statement` equals the file signature up to whitespace.
- The three added `stmt_deps` are landed nodes with lean records, as STATE.md allows.
  None of them reaches the item, so there is no cycle.
- No other field of the node changed.

Compile: the snapshot module compiles with `nt_compile.py --json` against the local side
overlay, with rc 0 and no error or warning.

Mismatches found: none in the Lean. The only fault was that this section did not record an
independent reading (H11). It is repaired by this subsection.
