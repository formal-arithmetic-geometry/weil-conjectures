## Worker report

The interrupted retained sandbox contained only dispatcher dotfiles: no module, node copy,
report, or second-reading section survived. Reconstructed the delivery from the unchanged
repository node and its actual dependencies, then performed the source/signature review below.
There is no surviving first-worker statement to compare or preserve.

Module: `Sheaf.AlgebraicTopology.SimplicialSpaceLocalizationIntervalCriterion`.
Main declaration: `SSet.SegalSpace.localization_interval_criterion`.
Helpers: `SSet.SegalSpace.IsLocalFor` and `SSet.SegalSpace.localWeakEquivalences`.
These are the two tests explicitly introduced in the item's own statement, not independent
new notions or private copies of its dependencies. Both have real predicate bodies.
The only postponed theorem is `localization_interval_criterion`, with proof `by sorry`.
The docstring follows all nine steps of the DAG proof, including the bounded lifting step,
the small-object argument, the functorial systems, the unconditional simplicial axiom,
the exact fibrant-object identification, and the interval argument down to the ordinary
pullback calculation. No auxiliary theorem or construction has been proved here.

The node is unchanged except for its `lean` record. There is no `statement_change`, no
new node, and no dependency module. There is no repair note for this item.

The source is Rezk, *A model for the homotopy theory of homotopy theory*, Propositions
9.1 and 9.2, printed pp. 21--22, with cartesian compatibility interpreted as Section
2.5(1). The source was read directly at the URL recorded in the node:
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf
No Stacks tag claims this result. Sections 2.3--2.5 supply the ambient conventions of
small simplicial sets, simplicial spaces, Reedy fibrancy and cartesian enrichment;
there is no ring, field, characteristic, Noetherian or nonemptiness assumption.

Dependency signatures and implementations read:

- `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`:
  `mappingSpace`, `mappingSpacePre`, `mappingSpacePost`, `mappingPullback`,
  `IsReedyCofibration`, `IsReedyWeakEquivalence`, `reedy_cartesian_simplicial`.
  In particular, `mappingSpace` is outer-degree-zero evaluation of the actual internal
  hom, and `mappingPullback` is the canonical pullback lift with its naturality equation.
- `Sheaf.AlgebraicTopology.SegalCartesianExponent`, imported by that dependency:
  `SimplicialSpace := SimplexCategoryᵒᵖ ⥤ SSet`, `instMonoidalClosed`,
  `discreteRepresentable`, `constant`, `IsReedyFibration`, `IsReedyFibrant`.
  The downstream `cartesian_exponent` theorem is not used: importing its file for the
  already shared definitions does not assume the theorem this item will help prove.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `leftClass`, `rightClass`, `model_structure` and `simplex_reedy_structure`.
  Fibrancy is the actual relative matching condition for the terminal map;
  weak equivalences are levelwise. No arbitrary old model record is supplied as a binder.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `weakEquivalenceStructure` and `right_proper_kan_quillen`. Kan fibrations are the
  existing horn-lifting class; weak equivalences use `Enhanced.IsWeakHomotopyEquivalence`.
  Its definition in `EnhancedDiagramsCones` was also opened: geometric realization,
  path components and all based homotopy groups are retained.
- Proof-only Mathlib imports serve the recorded nodes `lem-coef-lifting-class-closure`
  and `lem-coef-small-object-cell-factorization`: `MorphismProperty.rlp` and its
  retract/cobase-change/multiplicative lemmas; `SmallObject.functorialFactorizationData`.
  `lem-coef-simplicial-local-bounded-lifting` has neither `lean` nor `mathlib_match` on
  the base, so there is no proof-dependency module available to import for it. Its
  exact role remains in proof step 3. No unstated proof prerequisite is assumed in
  the Lean theorem; stating this item does not require proving the boundedness lemma.

Searches (2026-10-17), using `/home/ubuntu/weil-launcher-nt/msearch.py Q118
lem-coef-simplicial-space-localization-interval-criterion`:

- `leanfinder "Bousfield localization simplicial spaces interval cartesian model structure"`:
  eight hits, including `SSet.cosk`, standard Kan cofibration/fibration structures and
  `SSet.instCartesianMonoidalCategory`; none is the localization or interval criterion.
- `leansearch "Localization model structure on simplicial spaces with fibrant local objects"`:
  eight hits on the ground Kan classes and generic model-category consequences;
  none gives this statement.
- `loogle "ModelCategory"` did not resolve the unqualified name. The corrected query
  `loogle "HomotopicalAlgebra.ModelCategory"` returned the record and its projections;
  opened its source to check the exact axioms. It only requires ordinary factorizations,
  so this delivery explicitly includes both functorial factorization conclusions.
- `rg` over Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json`, with `Bousfield`, `localEquival`, `localObject`,
  `localization_interval`, and simplicial-space localization phrases. No exact theorem
  or existing simplicial-space locality test was found. Also checked each proposed full
  declaration name to avoid a name collision.
- Opened Mathlib `CategoryTheory/Localization/Bousfield.lean`: its `isLocal` tests
  bijections of ordinary Hom sets, so it is not the simplicial mapping-space predicate.
- Opened `Sheaf.CategoryTheory.BousfieldLocalFibrations`: its `IsLocal` and
  `localEquivalences` require an original model instance, a simplicial enrichment and
  cofibrant replacement. They concern general derived mapping spaces. They do not
  supply the present actual `mappingSpacePre` test on the recorded simplicial spaces.
  No duplicate model structure or mapping-space construction is introduced here.

Validation: `scompile.py Q118 lem-coef-simplicial-space-localization-interval-criterion
lean/Sheaf/AlgebraicTopology/SimplicialSpaceLocalizationIntervalCriterion.lean` passed
on the sandbox source and library path, with no errors or warnings. Both checks took
under two seconds of compiler time. The initial call from the shared-directory cwd
could not locate the sandbox-relative file; rerunning from the sandbox fixed the path.
No compiler settings or timeout limits were changed. The node signature is extracted
verbatim from the module. All Lean lines are at most 100 characters.

## Second reading by Q118

This is the resumed second-reading task. The first action was to inspect the retained
sandbox: the prior failure report was accurate, and no mathematical artifact or review
section existed there. The following is the source-to-node-to-Lean audit of the
reconstructed delivery, rather than a claim to have read a missing first-worker file.
The original repository node, source, dependency declarations and final module were
kept open for this audit. No changes to the mathematical node were needed.

Objects, hypotheses and conclusions, listed before checking their Lean rendering:

| Node item | Final Lean rendering | Verdict |
| --- | --- | --- |
| Small simplicial spaces, in any fixed universe | `SimplicialSpace.{u}` and explicit `universe u` | Same recorded functor category; arbitrary universe, no additional instance binder. |
| Two spaces P,Q and their monomorphism f | `{P Q : SimplicialSpace.{u}} (f : P ⟶ Q) (_hf : Mono f)` | Exact. Twice applying `NatTrans.mono_iff_mono_app`, then the Type mono/injectivity criterion, gives precisely injectivity in every bidegree. |
| Reedy fibrancy in the definition of f-locality | First conjunct `IsReedyFibrant W` in `IsLocalFor` | Exact recorded relative matching condition. |
| Locality mapping test Map(Q,W) to Map(P,W) | Second conjunct `Enhanced.IsWeakHomotopyEquivalence (mappingSpacePre f W)` | Exact map and direction; actual mapping spaces, no derived replacement added. |
| Test a completely arbitrary g:A to B against every local W | `localWeakEquivalences f := fun _ _ g ↦ ∀ W, IsLocalFor f W → ... (mappingSpacePre g W)` | Same quantifiers; no cofibrancy/fibrancy assumption on g's endpoints. |
| Existence of a model structure | First conclusion `(∃ m : ModelCategory SimplicialSpace.{u}, ...)` | Genuine model record; its classes cannot be chosen unrelated to the statement because all three are fixed below. Small completeness/cocompleteness are inherited from the ambient functor category. |
| Cofibrations exactly the monomorphisms | `m.categoryWithCofibrations.cofibrations = monomorphisms SimplicialSpace.{u}` | Equality, not merely inclusion. |
| Weak equivalences exactly the local equivalences | `m.categoryWithWeakEquivalences.weakEquivalences = localWeakEquivalences f` | Equality, using the same predicate throughout. |
| Fibrations exactly RLP against local-equivalence monomorphisms | `m.categoryWithFibrations.fibrations = (monomorphisms ... ⊓ localWeakEquivalences f).rlp` | Exact Mathlib diagonal-lifting definition; no chosen generating subset replaces all tests. |
| Model-category convention of functorial factorizations | Two explicit `HasFunctorialFactorization` conjuncts, for C against F intersect W and C intersect W against F | Necessary supplement to Mathlib's weaker record convention, as the model-axioms dependency stipulates. |
| Fibrant objects exactly f-local | `∀ W, m.categoryWithFibrations.fibrations (terminal.from W) ↔ IsLocalFor f W` | Both directions; terminal map uses the ambient terminal object. |
| For every monomorphism i and localized fibration p the specified mapping corner is Kan | Quantifiers `∀ (A B X Y) (i : A ⟶ B) (p : X ⟶ Y), Mono i → m... p → Fibration (mappingPullback i p) ∧ ...` | Same four objects and hypotheses; `Fibration` here is the fixed Kan class on SSet, never a localized-space fibration. |
| The corner is trivial if either i or p is a local equivalence | Conditional on `localWeakEquivalences f i ∨ localWeakEquivalences f p`, both `Fibration` and `Enhanced.IsWeakHomotopyEquivalence` of the same corner | Exact disjunction and triviality condition. There is no interval assumption on this conclusion. |
| Every old Reedy weak equivalence is local | Separate conjunct `∀ (A B) (g : A ⟶ B), IsReedyWeakEquivalence g → localWeakEquivalences f g` | Every g, with no local/fibrant endpoint condition. |
| Extra interval hypothesis for every local W | Antecedent `∀ W, IsLocalFor f W → IsLocalFor f ((ihom (discreteRepresentable 1)).obj W)` | F(1) is the existing outer representable, discrete internally, not a constant interval. This hypothesis occurs only after the first two conclusions. |
| Two arbitrary monomorphisms i:A to B and j:C to D | Final `∀ (A B C D) (i : A ⟶ B) (j : C ⟶ D), Mono i → Mono j → ...` | No endpoints or index set excluded. |
| Either input locally weak implies its cartesian pushout product locally weak | Final disjunction followed by `localWeakEquivalences f (((...Arrow.pushoutProduct.obj (Arrow.mk i)).obj (Arrow.mk j)).hom)` | Mathlib's actual Leibniz pushout-product map. Opened its definition: domain is the pushout of A×D and B×C over A×C, target B×D. The ambient tensor is the recorded cartesian tensor. |

Source check: read Rezk Sections 2.3--2.5 and Propositions 9.1--9.2 directly. The node
correctly isolates the interval assumption from the localization/simplicial assertions.
The source also discusses cofibrant generation and detection of old weak equivalences
between local objects, but this node does not claim those additional conclusions, and
the Lean does not add them. There is no source-based correction to make, hence no
statement-change/citer-audit packet. The sole direct citer is
`lem-coef-segal-cartesian-exponent`; its existing proof uses exactly the localization
and interval conclusions now supplied. Read its node and module while checking the
shared definitions and the direction of the F(1)-exponent hypothesis.

Edge cases checked:

- Empty spaces are allowed for every space variable, including P, Q, W and all four
  pushout-product endpoints; there is no inhabitedness or nonempty-index hypothesis.
  In particular f from empty P, and the unique empty-to-empty f, remain included.
- A mapping space may be empty. The weak-equivalence predicate uses bijectivity on
  path components, so empty/nonempty distinctions are retained, not silently ignored.
- With f an identity the mapping test is an identity: locality reduces to Reedy
  fibrancy. This recovers the expected old-model case without a new assumption.
- The pushout product includes empty-source inclusions and identity inputs. It is the
  canonical map, not an arbitrary map with the same source and target.
- n = 0 is not quantified away: the proof explicitly handles F(0), the empty product
  retract, and boundary lifting in degree zero. The theorem puts no positive-degree
  restriction on its model or mapping-corner conditions.
- The terminal simplicial space is included; there is no additive zero object in this
  category. Schemes, rings and characteristic do not occur in the node.
- All spaces use the fixed small-set universe u, as the node requires, and the model
  record lives in the larger category universe automatically. No equality between
  independent universes, smallness instance, cardinal bound or additional hypothesis
  is imposed. No variable or universe is left auto-implicit.

Mismatches found and repairs:

1. The retained delivery was absent, so a dry run could only find zero item node files.
   Added the node copy (unchanged except `lean`), the module, and this report. There was
   no prior statement to retain and no prior review section to overwrite.
2. A bare `ModelCategory` conclusion would omit the project's functorial-factorization
   convention. Included both explicit functorial factorization properties in the
   reconstructed signature after reading Mathlib's record and the dependency signature.
3. Guarded against accidental scope changes by keeping the interval condition only in
   the last implication and using explicit model-class projections. No input instance
   equates the new model with the old Reedy structure or with Kan simplicial sets.
4. Reused all existing maps, fibrancy tests, exponents, F(1), and pushout products.
   No hollow definition, arbitrary comparison, private duplicate, additional axiom,
   proved theorem, local notation or file-local instance is present.

Searches above were performed during this resumed reading, including opening the
apparently similar ordinary Bousfield and derived-enrichment declarations rather than
accepting their names as matches. The item is not an `existing: true` case.

Validation: the final file compiles through the required `scompile.py` wrapper without
warnings. Only the named theorem has `sorry`. The `lean.statement` exactly matches the
file signature, and no protected node field or target/unit statement was changed.
