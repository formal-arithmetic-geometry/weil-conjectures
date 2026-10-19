## Worker report

Item: `lem-coef-brown-right-exact-extension`, group Q70, 2026-10-17.

The module `Sheaf.CategoryTheory.BrownRightExactExtension` states
`SSet.Enhanced.brown_right_exact_extension`, with its sole proof `sorry`.
There are no new definitions, dependency repairs, or statement corrections.
The theorem docstring supplies a source-based natural-language proof plan because
this newly split node has an empty proof array.

Source checked online: [Cisinski, Higher Categories and Homotopical Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
Definition 7.5.2 and Proposition 7.5.6, last assertion, printed pp. 372--373
(PDF pp. 387--388, zero-based). Take opposites in that assertion. The functor
conditions here are exactly its right exactness conditions when the target's
weak equivalences are equivalences and all target arrows are cofibrations.

Clause-by-clause correspondence:

- Ordinary category and size: `(A : Type u) [Category.{v} A]`, with independent
  object and arrow universes. `L`, `E`, and the diagram shapes live in
  `SSet.{max u v t}`. The extra `t` allows any larger ambient universe.
- Initial object: `(zero : A)` and
  `hzero : CategoryTheory.Limits.IsInitial zero`.
- Morphism classes: `(C W : MorphismProperty A)`; `hCiso` and `hWiso` say that
  each contains isomorphisms. `[C.IsStableUnderComposition]` gives composition
  closure for C; `[W.HasTwoOutOfThreeProperty]` includes composition closure
  for W and both cancellation implications.
- Retracts: `[W.IsStableUnderRetracts]` is closure under arrow-category retracts.
- All objects cofibrant: `hcof : ∀ X, C (hzero.to X)`. Initiality makes this
  equivalent to requiring every arrow from zero to X to belong to C.
- Factorization: `[MorphismProperty.HasFactorization C W]` means every arrow
  has a C-then-W factorization; no functoriality is imposed.
- Ordinary pushout existence: `hpush` gives `HasPushout i f` for every C arrow
  i and arbitrary f with the same domain.
- Pushout closure: `[C.IsStableUnderCobaseChange]` and
  `[(C ⊓ W).IsStableUnderCobaseChange]` give the two required membership
  assertions for the cobase-changed arrow in every pushout square.
- Localization: `(q : largeNerve A ⟶ L)` and `hq : IsLocalization W q`.
  This definition asserts that L is a quasicategory, q inverts W, and actual
  restriction on the ENTIRE internal functor simplicial set factors through
  the full subcategory of W-inverting diagrams as a coherent functor equivalence.
- Finite coherent colimits in L: `hL` ranges over every `K : SSet` with
  `K.Finite` and every `F : K ⟶ L`, and supplies a colimiting cocone vertex.
  Mathlib's `SSet.Finite` means finitely many nondegenerate simplices.
- Target: `[Quasicategory E]`; `hE` gives the same finite-colimit condition in E.
- The given coherent functor: `(T : largeNerve A ⟶ E)`.
- W-inversion: `hTW : Inverts W T` uses the existing two-triangle definition
  of equivalence edges from the recorded enhanced-diagram dependency.
- Initial-object preservation: `hTzero : IsInitial E (object T zero)` uses
  contractibility of every outgoing right-pinched mapping space.
- Pushout preservation: `hTpush` quantifies EVERY specified ordinary square
  `hP : IsPushout i f a b` with `C i`. Its conclusion is `IsColimitEdge`
  of the actual coherent span `diagram T (span i f)`, with apex `object T P`
  and coherent cocone `transformation T hP.cocone.ι`. Thus it preserves the
  square itself and its compatibility, not merely a colimit-shaped object.
- The factorization: `(Tbar : L ⟶ E)` and
  `hTbar : AreNaturallyEquivalent (q ≫ Tbar) T` specify any extension with
  its coherent natural comparison. This is the factorization already furnished
  by hq and hTW. Universally quantifying such extensions makes no arbitrary
  choice from an existence theorem and imposes no extra condition on T.
- Conclusion: for every finite K, diagram F, and colimiting cocone c in L,
  the existential cocone d in E is colimiting. Its apex is exactly
  `Tbar.app _ c.1.1`; its coherent-arrow coordinate is exactly
  `((ihom Δ[1]).map ((ihom K).map Tbar)).app _ c.1.2`.
  Those equations specify postcomposition of the full original cocone.
  They are the existing cocone-coordinate convention also used by
  `SSet.Enhanced.finite_colimit_approximation`.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, recorded by
  `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.coconeCategory`,
  `IsColimiting`, `IsInitial`, `AreNaturallyEquivalent`, and its underlying
  `IsEquivalenceEdge`, `diagramVertex`, `mappingSpace`, `IsContractible`, and
  coherent functor-equivalence/full-subcategory constructions. The recorded
  module's full definitions and docstrings were read.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`, recorded by the already
  landed `def-coef-coherent-localization-interface`, added to stmt_deps:
  `HomotopicalAlgebra.FiniteReedy.largeNerve`, `IsLocalization`, `Inverts`,
  `localDiagrams`, `object`. This same module supplies the canonical
  construction helpers `diagram`, `transformation`, `IsColimitEdge`.
  Their full signatures/docstrings were read; they have real definition data.
  Only these definitions are used, never `finite_reedy_localization`.
  Citing that theorem node would introduce an artificial DAG cycle through
  the downstream rectification proof, so the dedicated definition node is used.
- Mathlib: `SSet.Finite` from `Mathlib.AlgebraicTopology.SimplicialSet.Finite`;
  `MorphismProperty.HasFactorization` from `CategoryTheory.MorphismProperty.Factorization`;
  `IsStableUnderComposition` and `HasTwoOutOfThreeProperty` from
  `CategoryTheory.MorphismProperty.Composition`;
  `IsStableUnderCobaseChange` from `CategoryTheory.MorphismProperty.Limits`;
  `IsStableUnderRetracts` from `CategoryTheory.MorphismProperty.Retract`;
  `IsPushout.cocone` and the ordinary initial-object/pushout APIs.
  These instance fields were inspected, including the orientation of cobase change.

Edge cases checked before writing:

- Empty finite simplicial shapes are included; no inhabitedness assumption is
  present. Their cocones express preservation of initial objects.
- Discrete finite shapes, non-discrete shapes, and shapes with higher simplices
  all occur under `K.Finite`; finiteness is not restricted to finite categories.
- All square legs and choices of pushout apex are quantified; neither a chosen
  pushout nor an extra cofibrancy hypothesis on the second leg is imposed.
- Identity cofibrations, isomorphisms, and trivial cofibrations are covered by
  the same pushout hypothesis. The one-object terminal category satisfies the
  Brown conditions; no accidental nontriviality condition is present.
- An empty A cannot supply its required zero; an empty E cannot satisfy hE
  for the empty shape. These are consequences of the stated assumptions.
- The factorization comparison is a coherent equivalence in the functor
  quasicategory, not literal equality and not a comparison only on objects.
- The conclusion's existential d is tied to both coordinates of c. It cannot
  be satisfied by choosing an unrelated colimiting cocone.

Searches (raw msearch records are in sandbox `searches.jsonl`):

- `msearch.py leanfinder`: "A right exact functor from a Brown cofibration category
  extends to a functor preserving finite coherent colimits on the infinity localization".
  Eight hits, headed by `HomotopicalAlgebra.CofibrantObject` localization APIs;
  these require a model category and concern ordinary localization, so none match.
- `msearch.py loogle`: `"IsLocalization", "PreservesFiniteColimits"`.
  Zero hits.
- `msearch.py grep`: `PreservesFiniteColimits|preserves.*[Pp]ushout` in
  `CategoryTheory/Localization`. Zero hits.
- `msearch.py leansearch`: "A functor from a cofibration category to a finitely
  cocomplete quasicategory preserving initial objects and cofibration pushouts
  induces a finite colimit preserving functor from the infinity localization".
  Eight hits. The closest is
  `CategoryTheory.Limits.preservesFiniteColimits_of_preservesInitial_and_pushouts`,
  which states only an ordinary-category preservation criterion.
- `rg` on the read-only upstream `WeilConjectures` and project `lean/Sheaf`
  for the item id, Brown/right-exact-extension names, and preservation of
  coherent colimits: no existing theorem. The Brown-products file cites this
  node in its proof plan. `FiniteColimitApproximation` supplies a matching
  explicit preservation format but proves a different result.
- `rg` on Mathlib, upstream, project, and `dag/lean_names_upstream.json` for
  `brown_right_exact_extension|BrownRightExactExtension`: no conflicting name.

No STATEMENT-DISPUTED issue or node fault was found.

Validation: prescribed `scompile.py Q70 lem-coef-brown-right-exact-extension`
compiled both the sandbox and library-path versions cleanly (1.3 s / 1.4 s),
with no errors or additional warnings. All universes and variables are explicit;
`autoImplicit` is disabled. No live source was modified and no global build ran.
The prescribed delivery dry run uses `deliver2.py --no-push`; the second reader delivers.

## Second reading by Q70

Independent second reading, 2026-10-17. Read the sandbox node, its complete five-step
proof, the delivered Lean file, both statement-dependency nodes and their actual
source declarations. No repair note exists for this item in the shared checkout.
The only node differences from the shared base are the added, already recorded
`def-coef-coherent-localization-interface` statement dependency and the Lean record.
There are no new nodes, dependency modules, or statement corrections to audit.

Source checked independently: [Cisinski, Higher Categories and Homotopical Algebra]
(https://cisinski.app.uni-regensburg.de/CatLR.pdf), Definition 7.5.2, Example 7.5.4,
Proposition 7.5.6 and its proof, printed pp. 370--373, with Definitions 7.4.6 and
7.4.12 for the standing axioms. This source is a PDF, not a Stacks tag. Taking
opposites gives the asserted extension property. The source permits the target's
weak equivalences to be equivalences and its cofibrations to be all arrows.
The ordinary all-cofibrant Brown hypotheses in the node supply the source axioms.
Retract closure is expressly required by this node; Lean retains it. No unstated
model-category, functorial-factorization, or cocompleteness hypothesis was added.

Node checklist, written before making the documentation repair:

| Object, hypothesis, or conclusion in the node | Lean rendering and verdict |
| --- | --- |
| Ordinary category A | `(A : Type u) [Category.{v} A]`; exact, independent object/arrow sizes. |
| Initial object 0 | `zero`, `hzero : CategoryTheory.Limits.IsInitial zero`; exact. |
| Classes C and W of arrows | `(C W : MorphismProperty A)`; exact. |
| Both classes contain isomorphisms | `hCiso`, `hWiso`; exact order inequalities on morphism predicates. |
| C and W closed under composition | `[C.IsStableUnderComposition]`; W composition is a parent of `[W.HasTwoOutOfThreeProperty]`; exact. |
| W has two-out-of-three | `[W.HasTwoOutOfThreeProperty]` includes both cancellation directions; exact. |
| W retract closed | `[W.IsStableUnderRetracts]` uses `RetractArrow`; exact. |
| All initial arrows are cofibrations | `hcof : ∀ X, C (hzero.to X)`; exact since every initial arrow is unique. |
| Every arrow factors C then W | `[MorphismProperty.HasFactorization C W]`; read `MapFactorizationData` and the `Nonempty` field; exact, no functoriality. |
| Pushouts along C exist | `hpush` quantifies every common-domain pair with `C i`; exact. |
| Such pushouts remain in C | `[C.IsStableUnderCobaseChange]`; its `IsPushout` field gives the opposite parallel leg, as required. |
| Pushouts along C intersect W remain there | `[(C ⊓ W).IsStableUnderCobaseChange]`; existence already follows from `hpush`; exact. |
| Localization q from the nerve into L | `q : largeNerve.{u,v,t} A ⟶ L`, `hq : IsLocalization W q`; exact enlarged nerve and full universal property. |
| L is a quasicategory | The first conjunct of `hq`; no extra instance assumption is needed. |
| L has finite coherent colimits | `hL`, over every `K.Finite` and every `F : K ⟶ L`, producing a vertex with `IsColimiting`; exact. |
| Finitely cocomplete quasicategory E | `[Quasicategory E]` and `hE` with the identical finite-shape condition; exact. |
| Coherent functor T from the nerve | `(T : largeNerve A ⟶ E)`; exact simplicial map. |
| T inverts W | `hTW : Inverts W T`; exact equivalence edges with both inverse triangles. |
| T sends zero to an initial object | `hTzero : IsInitial E (object T zero)`; exact actual image vertex. |
| T preserves every ordinary cofibration pushout square | `hTpush` quantifies `i,f,a,b,hP` and assumes only `C i`; `diagram T (span i f)` and `transformation T hP.cocone.ι` retain that square's two legs and commutativity. `IsColimitEdge` fixes its apex and transformation; exact. |
| Extension furnished by localization | `Tbar : L ⟶ E`, `hTbar : AreNaturallyEquivalent (q ≫ Tbar) T`; exact. Universally quantifying such an extension is independent of its choice, and localization already supplies its existence. |
| Preservation of every finite coherent colimit | Quantifiers are `K`, its finiteness proof, `F`, the actual cocone `c`, then `IsColimiting F c`; exact. |
| Image cocone, including its coherence, is colimiting | The witness `d` lies over `F ≫ Tbar`, with apex `Tbar.app _ c.1.1`, arrow coordinate `((ihom Δ[1]).map ((ihom K).map Tbar)).app _ c.1.2`, and `IsColimiting (F ≫ Tbar) d`; exact postcomposition of both coordinates. |

Dependency checks: opened `EnhancedDiagramsCones.lean` in full, including
`IsEquivalenceEdge`, `diagramVertex`, `constantDiagrams`, `mappingSpace`,
`AreNaturallyEquivalent`, `IsFunctorEquivalence`, `commaSubcomplex`,
`coconeCategory`, `IsInitial`, and `IsColimiting`. The cocone is the specified
degreewise comma construction; its vertices have exactly the two coordinates
used in the conclusion. Opened `FiniteReedyLocalization.lean`, in particular
`largeNerve`, `Inverts`, `localDiagrams`, `IsLocalization`, `comparison`,
`diagram`, `transformation`, `object`, and `IsColimitEdge`. These have actual
construction data, and restriction in `IsLocalization` is the actual
precomposition map with a factorization through the full W-inverting subcategory.
Only its helpers are used; the finite-Reedy theorem supplies no premise here.
The added interface dependency already owns the localization notion, so no
duplicate definition or new definition node is needed. Mathlib's composition,
factorization, cobase-change, retract, and simplicial-finiteness fields were
also inspected directly.

Edge cases: the empty simplicial set is permitted by `K.Finite`, and tests
preservation of initial objects; no inhabitedness assumption occurs. Degree
zero shapes, finite discrete shapes, and shapes with higher nondegenerate
simplices are all included. `SSet.Finite` means finitely many nondegenerate
simplices, not degreewise finiteness or a finite ordinary index category.
All choices of ordinary pushout and all second legs are quantified, including
identity and trivial-cofibration cases. A one-object category is allowed;
an empty A cannot have the required initial object, and hE excludes an empty
target through the empty diagram. No ring, characteristic, scheme, or numerical
degree hypothesis occurs. Universes `u`, `v`, and `t` are explicitly bound;
`max u v t` contains both category sizes and allows arbitrary enlargement.
The extension is compared coherently, and the output cocone cannot be replaced
by an unrelated colimit with the same apex.

Independent searches, recorded by the prescribed wrapper in `searches.jsonl`:

- LeanFinder: `Homotopy finite colimits preserved by the derived functor of a
  cofibration category exact functor`. Eight hits about ordinary derived
  categories, model-category derivability, and homotopy categories; none has
  this quasicategorical conclusion.
- Loogle: `"Cofibration", "Localization"`. Zero hits.
- LeanSearch: `An exact functor of Brown cofibration categories induces a finite
  colimit preserving functor of quasicategorical localizations`. Eight hits,
  principally `CategoryTheory.ExactFunctor` and `rightExactFunctor_iff`.
  Opened `Mathlib/CategoryTheory/Limits/ExactFunctor.lean`: these notions use
  ordinary functors and ordinary finite colimits, so they do not match.
- `rg` in upstream `WeilConjectures`, shared `lean/Sheaf`, upstream Mathlib,
  and `dag/lean_names_upstream.json`, using Brown/right-exact/localization and
  cofibration/finite-colimit terminology and the declaration name: no existing
  theorem. Opened the nearby ordinary criterion
  `preservesFiniteColimits_of_preservesInitial_and_pushouts` in Mathlib's
  `LimitsOfProductsAndEqualizers.lean`; its type is `C ⥤ D`, so it does not
  replace this coherent statement. Project Brown localization and finite-direct
  rectification modules only cite this node as a proof dependency.

Mismatches repaired: H8, the original theorem docstring incorrectly said the
node had no proof steps and omitted the five-step proof now recorded in the
node. Replaced that paragraph with the five steps and their named dependencies:
opposite localization, coherent span rectification, preservation of specified
pushouts/initial objects, finite coproducts, then the finite-limit criterion on
opposites. H9/stage-2 rule 7, the six recorded statement proof-dependency modules
were not imported. Added their non-public imports. The two proof nodes without
Lean records (`lem-coef-infinity-terminal-pullback-criterion` and
`lem-coef-infinity-limits-products-pullbacks`) have no module to import yet.
Checked the source import graph: the added imports introduce no cycle.
The worker report's earlier assertion of an empty proof array is superseded
by this reading. No mathematical statement mismatch was found or changed.

Validation: prescribed `scompile.py Q70 lem-coef-brown-right-exact-extension`
compiled the required Brown-left-fractions overlay, the sandbox module, and the
library-path module cleanly (each 1.3 seconds), with no errors or warnings.
Checked every binder and both output coordinates by eye. The Lean signature
is verbatim equal to `lean.statement`; all lines are at most 100 characters.
There is exactly one named theorem and one whole-proof `sorry`, no definitions,
no proved lemmas, and no hollow data. Source/blueprint docstrings are present.
