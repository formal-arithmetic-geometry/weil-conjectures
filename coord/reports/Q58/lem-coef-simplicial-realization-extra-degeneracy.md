## Worker report

The item is stated in `Sheaf.CategoryTheory.SimplicialRealizationExtraDegeneracy` as
`CategoryTheory.simplicial_realization_extra_degeneracy`. Its proof is `sorry`, as required
in stage 2. The item's natural-language statement is unchanged. Its only non-lean delta is
adding `def-coef-simplicial-model-realization` to `stmt_deps` for the explicit coequalizer
construction. The inherited `status: unsplit` is preserved rather than silently repaired.

Read the node, all three statement dependencies, their recorded source declarations and
relevant docstrings, the stage-2 brief, stages/2-statements, delivery-errors H, worker role,
SETUP/GOAL/STATE, tools README and the CompactObject example. There was no repair note for
this item. Source: Dugger, https://pages.uoregon.edu/ddugger/hocolim.pdf, Definition 3.11
and Proposition 3.12 (printed pp.12–13), and Section 19.1 (printed p.90). Definition 3.11
is precisely the terminal/sinklike convention in the node; Section 19.1 explicitly extends
the constructions and results to simplicial model categories. The coequalizer formula is
Section 3.1, and its collapse/augmentation is Section 3.7. No statement correction or
STATEMENT-DISPUTED flag is needed.

Hypotheses and clauses of the item, matched individually:

| Node text | Lean rendering |
| --- | --- |
| A category M | `{M : Type u} [Category.{v} M]`, with independent object and morphism universes |
| Complete and cocomplete model category | `[ModelCategory M] [HasLimits M] [HasColimits M]` |
| Functorial model factorizations in the inherited convention | Both `MorphismProperty.HasFunctorialFactorization` binders, respectively for `(cofibrations M, trivialFibrations M)` and `(trivialCofibrations M, fibrations M)` |
| Simplicial enrichment, tensor and cotensor | `[SimplicialCategory M] (T : SimplicialTensorCotensor M)` |
| Simplicial model compatibility axiom | `_hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`, the recorded corner-map condition |
| X is a functor from Δᵒᵖ | `X : SimplicialObject M`; this is Mathlib's functor abbreviation |
| An object Y and natural augmentation to const Y | `(Y : M) (ε : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Y)` |
| X Reedy cofibrant | `_hReedy : HomotopicalAlgebra.Reedy.leftClass (MorphismProperty.epimorphisms SimplexCategory).op (cofibrations M) (initial.to X)` |
| Degree-zero augmentation | `ε.app (op ⦋0⦌)` |
| t₋₁ and the tₙ | `tMinusOne : Y ⟶ X _⦋0⦌` and `t : ∀ n : ℕ, X _⦋n⦌ ⟶ X _⦋n + 1⦌` |
| dₙ₊₁ tₙ = 1 for every n | `_hterminal : ∀ n, t n ≫ X.δ (Fin.last (n + 1)) = 𝟙 _` |
| d₀ t₀ = t₋₁ ε | `_hzero : t 0 ≫ X.δ 0 = ε.app (op ⦋0⦌) ≫ tMinusOne` |
| dᵢ tₙ = tₙ₋₁ dᵢ for n ≥ 1, 0 ≤ i ≤ n | `_hfaces : ∀ (n : ℕ) (i : Fin (n + 2)), t (n + 1) ≫ X.δ i.castSucc = X.δ i ≫ t n`; the binder is the predecessor of the node's n |
| sᵢ tₙ = tₙ₊₁ sᵢ for 0 ≤ i ≤ n | `_hdegeneracies : ∀ (n : ℕ) (i : Fin (n + 1)), t n ≫ X.σ i.castSucc = X.σ i ≫ t (n + 1)` |
| ε t₋₁ = 1 | `_hsection : tMinusOne ≫ ε.app (op ⦋0⦌) = 𝟙 Y` |
| Δⁿ is HomΔ(-,[n]) | `SSet.stdSimplex.obj n`, the existing `uliftYoneda` functor with its universe lift |
| Realization is the displayed coend/coequalizer | `SimplicialModelRealization.realization`, with the two explicit coproduct arrows described below |
| The map is induced by the augmentation | `SimplicialModelRealization.augmentationMap T X ε`, constructed with `coequalizer.desc` from the transposed constant families of εₙ |
| That map is a weak equivalence | `WeakEquivalence (SimplicialModelRealization.augmentationMap T X ε)` |
| No fibrancy/nonemptiness assumption on Y | No such binder or instance occurs; the construction chooses no element of Y |

The positive arrows for Δᵒᵖ are the opposites of the surjections in Δ, hence exactly
`(MorphismProperty.epimorphisms SimplexCategory).op`. This is the opposite of the
simplex Reedy structure in the dependency, whose negative/positive classes on Δ are
respectively epimorphisms/monomorphisms. Using the dependency's `leftClass` on the
initial map therefore expresses the recorded relative-latching test, without assuming
an unrelated model structure on the functor category.

Dependency declarations actually used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7`. Read its full definition,
  the canonical `cornerMap`, and the theorem's complete model-category context.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.leftClass`, `relativeLatching`, and the interpretation supplied
  by `model_structure` and `simplex_reedy_structure`. Read their complete signatures and
  docstrings. The theorem itself does not require choosing a model structure as data.
- The mathlib match of `def-weil-pbc-simplicial-set`:
  `SSet`, `SimplicialObject`, `SimplexCategory`, their face/degeneracy operators, and
  `SSet.stdSimplex` from `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex`. Read also
  the matched `degenerate`, `nonDegenerate`, `Subcomplex` and `Finite` definitions;
  those four additional notions are not used by this statement.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor`, including `tensorUnit`, `tensor_isIso`,
  and the existing canonical `tensorMap`.
- `Sheaf.CategoryTheory.SimplicialUndercategoryModel`:
  `CategoryTheory.SimplicialUndercategory.tensorTranspose`. Its source and full signature
  were read; it is generic in an enriched category and does not require an undercategory,
  a model structure, or a chosen point. It is reused rather than copied.
- `Sheaf.CategoryTheory.SimplicialModelRealization`, the new definition node below:
  `CategoryTheory.SimplicialModelRealization.augmentationMap` and its concrete source.

Edge cases checked before writing:

- At n = 0 the two faces are exactly d₀ and d₁: `_hzero` supplies the former and
  `_hterminal 0` the latter. The degeneracy condition includes s₀ at n = 0.
- At the first positive face degree, `_hfaces 0` includes both i = 0 and i = 1 for
  t₁. `castSucc` excludes only the final identity face, which `_hterminal` covers.
- At every n, `_hdegeneracies` ranges over precisely i = 0,...,n. It adds no relation
  involving the unlisted final degeneracy or a composite of two extra-degeneracies.
- If Y is initial, empty in a concrete model, or has no selected point, all types and
  maps remain meaningful. Only the required section is assumed; no `Nonempty`,
  `Inhabited`, fibrancy or terminal-object condition is added.
- Constant simplicial objects satisfy the displayed identities with identity maps.
  Reedy cofibrancy is still required, as the node states.
- The coequalizer ranges over every simplex operator, including identity maps and
  degeneracies, rather than only injections (which would give fat realization).
- Object universe u is independent of hom/enrichment universe v. Standard simplices
  use the existing universe-lifted representables in SSet.{v}; the simplex/operator
  indices themselves are small. No equality of universes is imposed.

Searches made for the item:

- `msearch.py leansearch`: “realization augmented simplicial object extra degeneracy weak
  equivalence simplicial model category” returned `ExtraDegeneracy` and its constructors,
  not a realization weak-equivalence theorem.
- `msearch.py leanfinder`: “Geometric realization of an augmented Reedy cofibrant simplicial
  object with extra degeneracy is a weak equivalence” returned cofibrant replacement
  weak-equivalence facts and `ExtraDegeneracy.homotopyEquiv`.
- `msearch.py loogle`: `"ExtraDegeneracy"` returned its structure, section, and alternating
  face complex homotopy equivalence. Read ExtraDegeneracy.lean:72–83 and the homotopy
  equivalence signature. It uses the sourcelike/initial convention, not these terminal
  equations; its final equivalence is for chain complexes in a preadditive category.
- `msearch.py grep`: `realization|Realization|coend|Coend` in AlgebraicTopology returned
  topological realization of simplicial sets, not general simplicial-model realization.
- `rg` in upstream `WeilConjectures` for `ExtraDegeneracy`, realization/weak-equivalence
  combinations and `SimplicialTensorCotensor`: no matching theorem or construction.
  Searching for this item's exact blueprint id also returned no upstream declaration.
- `rg` in project `lean/Sheaf` found the existing tensor and transpose API and specialized
  constructions such as pinched simplicial-set realization, but no general tensor coend.
- `rg` of `dag/lean_names_upstream.json`, Mathlib and upstream found neither proposed full
  declaration name, so the names do not collide with an existing declaration.

Validation: scompile.py compiled both delivered files separately in dependency order,
including its private overlay/library checks. Final results were clean, about 2.0 seconds
for the construction and 1.3 seconds for the theorem; no warning other than expected
sorry warnings. Only the prescribed wrapper was used. The first attempt exposed an
unqualified `epimorphisms` name; it was replaced by `MorphismProperty.epimorphisms` and
both files were recompiled successfully. All Lean lines have at most 100 characters;
`set_option autoImplicit false` is present and universes are explicitly declared.

The only postponed proofs are `SimplicialModelRealization.augmentation_condition`, the
naturality equality explicitly included in the new definition node, and the item's
`simplicial_realization_extra_degeneracy` theorem. Both have complete source/proof docstrings.
All objects and morphisms are concrete constructions; no existence choice supplies data.

## New nodes

`def-coef-simplicial-model-realization` introduces the general tensor realization and its
canonical augmentation, from Dugger Sections 3.1, 3.7 and 19.1. It cites the existing
simplicial-set, tensor/cotensor and transpose nodes. Its module is
`Sheaf.CategoryTheory.SimplicialModelRealization`. `parameterMap` transposes the actual
composite with the universal tensor element. `summand` and `relationSummand` implement
Dₙ and Rα; `Operator` retains all triples (m,n,α). `relationLeft` applies X(α) and
`relationRight` applies Δα on the simplex parameter. `realization` is their existing
Mathlib coequalizer, not an abstract object with a universal-property hypothesis.
`augmentationLeg` transposes the constant families of εₙ; `augmentation_condition`
states a∘l = a∘r with the complete naturality proof in its docstring. Finally
`augmentationMap` is the unique Mathlib coequalizer descent of those specified legs.
Thus its use of the postponed compatibility proof does not leave its data undetermined.

New-node hypotheses and clauses: `[Category M] [SimplicialCategory M]` are the enriched
category, `T` is the recorded chosen tensors/cotensors, `[HasColimits M]` is cocompleteness,
`X` is the simplicial diagram, and `ε` is any natural augmentation. The individual
construction clauses are exactly the ten declarations just listed, each in the node's
`lean.declarations`. This is a definition node; its only helper theorem is the explicitly
stated naturality identity required to form that definition. The module has no model,
SM7, cofibrancy, fibrancy or nonemptiness hypothesis.

Duplicate search: `tools/blueprint_refs.py search 'simplicial realization'` found no
blueprint definition. DAG text searches found the unstated theorem
`lem-coef-reedy-realization-homotopy-invariance`, which describes this same coequalizer
in its statement but has no Lean record; it does not provide a separate definition node
or a usable declaration. No existing definition node owns this notion. The current item
also spells out this coequalizer. The common definition is now supplied once for both
the item and future consumers, with no dependency on that downstream theorem.

The new node records the actual output of three additional `msearch.py` searches:
LeanSearch “geometric realization simplicial object tensor coend coequalizer”, LeanFinder
“Tensor coend realization of a simplicial object in a simplicially enriched category”,
and grep `SimplicialTensor|coend|Coend` in CategoryTheory. Hits include the generic Mathlib
`coend` and `coequalizer`, `SSet.toTop`, enriched Hom functors and monoidal bimodule
coequalizers. These do not supply the present bifunctor or its augmentation. The
construction reuses `coequalizer`, coproducts and the already defined tensor transpose.
Additional direct `rg` searches of Mathlib, upstream WeilConjectures and project lean/Sheaf
confirmed that no general tensor realization exists. `CosimplicialFrameMapping` mentions
a tensor coend in its proof docstring but has no such definition. The chosen definition
id and module namespace are absent from the DAG and Lean libraries.

No dependency module or dependency node repair was needed. No unit, citer or target
statement was edited. The independent second reader must add their own reading; none is
claimed in this worker report.

## Second reading by Q58

I read the item node in `dag/nodes/sec-six-functors/lem-coef-simplicial-realization-extra-degeneracy.json`,
the source place in Dugger, *A Primer on Homotopy Colimits*, Definition 3.11 and
Proposition 3.12 (printed pp. 12--13), and Section 19.1 (printed p. 90), then matched
each item of the statement with the delivered Lean declaration.

Statement list and Lean match (verdict for each item 1--20: exact):

1. The category `M` is rendered by `{M : Type u} [Category.{v} M]`; the object and
   morphism universes remain independent.
2. Completeness, cocompleteness, and model-category structure are rendered by
   `[ModelCategory M] [HasLimits M] [HasColimits M]`.
3. The two functorial model factorizations are rendered by
   `HasFunctorialFactorization (cofibrations M) (trivialFibrations M)` and
   `HasFunctorialFactorization (trivialCofibrations M) (fibrations M)`.
4. The simplicial enrichment and chosen tensor/cotensor are rendered by
   `[SimplicialCategory M] (T : SimplicialTensorCotensor M)`.
5. The SM7 compatibility axiom is the explicit hypothesis
   `_hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`.
6. The simplicial object is `X : SimplicialObject M`, i.e. a functor
   `Deltaᵒᵖ -> M`.
7. The augmentation object and natural augmentation are `(Y : M)` and
   `ε : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Y`.
8. Reedy cofibrancy is the displayed relative-latching condition
   `HomotopicalAlgebra.Reedy.leftClass (MorphismProperty.epimorphisms
   SimplexCategory).op (cofibrations M) (initial.to X)`. This is the opposite
   simplex Reedy positive class, as established by the dependency's
   `simplex_reedy_structure`.
9. The degree-zero augmentation is `ε.app (op ⦋0⦌)`.
10. The extra maps are `tMinusOne : Y ⟶ X _⦋0⦌` and
    `t : ∀ n : ℕ, X _⦋n⦌ ⟶ X _⦋n + 1⦌`.
11. The terminal-face equation is `_hterminal`, namely
    `t n ≫ X.δ (Fin.last (n + 1)) = 𝟙 _` for every `n`.
12. The degree-zero equation is `_hzero`, namely
    `t 0 ≫ X.δ 0 = ε.app (op ⦋0⦌) ≫ tMinusOne`.
13. The remaining face equations are `_hfaces`; with its binder
    `i : Fin (n + 2)` and `i.castSucc`, it says
    `d_i t_(n+1) = t_n d_i` for every `0 ≤ i ≤ n+1`, exactly the node's
    `n ≥ 1` clause after replacing the node's index by `n+1`.
14. The degeneracy equations are `_hdegeneracies`; `i : Fin (n + 1)` gives
    `s_i t_n = t_(n+1) s_i` for `0 ≤ i ≤ n`.
15. The section equation is `_hsection`, namely
    `tMinusOne ≫ ε.app (op ⦋0⦌) = 𝟙 Y`.
16. The standard simplex `Delta^n = Hom_Delta(-,[n])` is `SSet.stdSimplex.obj n`.
17. The realization coend/coequalizer is the explicit
    `SimplicialModelRealization.realization T X`; its relation index is
    `Operator = Σ m n, m ⟶ n`, its summands are `X_n ⊗ Delta^m`, and its two
    legs are `relationLeft` and `relationRight`, induced respectively by
    `X(alpha)` and the standard-simplex map.
18. The augmentation-induced map is
    `SimplicialModelRealization.augmentationMap T X ε`, obtained by the
    specified coequalizer descent of the transposed constant augmentation
    families.
19. The conclusion is exactly
    `WeakEquivalence (SimplicialModelRealization.augmentationMap T X ε)`.
20. The source's explicit absence of fibrancy and nonemptiness assumptions on `Y`
    is respected: neither is present in the Lean binders.

The source's Definition 3.11 uses a map in every degree `n ≥ -1`, with the sinklike
identities `d_i S = S d_i` for `i ≤ n`, `d_{n+1}S = 1`, and `s_iS = Ss_i`; the
Lean equations `_hterminal`, `_hzero`, `_hfaces`, `_hdegeneracies`, and `_hsection`
are exactly this convention after separating the `n=-1` and degree-zero cases.
Proposition 3.12 states that either contracting convention makes the realization map
a homotopy equivalence; Section 19.1 explicitly carries the construction to arbitrary
simplicial model categories with tensors and SM7. The node uses the terminal convention,
as does the Lean statement.

Edge cases checked: `n = 0` gives both faces `d_0` (from `_hzero`) and `d_1` (from
`_hterminal 0`), and includes the sole degeneracy `s_0`; `_hfaces 0` includes both
face indices for `t_1`. The coequalizer includes identity operators and all
degeneracies, so it is the stated coend. Empty or zero objects and an augmentation
object without a chosen point remain admissible; no `Nonempty`, `Inhabited`, terminal,
or fibrancy hypothesis was introduced. Universes `u` and `v` are independent, and the
standard simplex uses the existing universe-lifted Mathlib representable.

I reread the recorded declarations for `lem-coef-simplicial-model-nerve-localization`,
`lem-coef-reedy-model-structure`, `def-weil-pbc-simplicial-set`,
`def-coef-simplicial-tensor-cotensor`, and
`lem-coef-simplicial-undercategory-model`. The supplied realization node is the one
explicit construction needed by this statement; its summands, two
relation legs, coequalizer, augmentation leg, compatibility theorem, and descent map
all have source and blueprint docstrings and use the recorded tensor transpose.
The redundant `parameterMap` helper was removed in this second reading, as explained below.

I repeated the three searches for an existing realization theorem or definition:
LeanSearch and LeanFinder queries for an extra-degeneracy realization weak equivalence,
Loogle for `ExtraDegeneracy`, and `rg` searches of Mathlib, upstream `WeilConjectures`,
and project `lean/Sheaf` for realization/coend/extra-degeneracy names. They found only
Mathlib's generic extra-degeneracy homotopy and unrelated simplicial-set or topological
realizations. No declaration duplicates either delivered full name. The additional
realization construction likewise has no existing match.

No theorem-signature mismatch was found. The worker's only existing-node change, adding
`def-coef-simplicial-model-realization` to `stmt_deps`, is required to make the explicit
coequalizer and augmentation construction canonical and is consistent with the node's
statement. The hypotheses, conclusion, and citers remain unchanged.

Two presentation/interface defects were repaired. First, the theorem docstring
previously sketched a direct prism proof instead of carrying all four current node
steps. I replaced it with the node's order reversal, the Mathlib first-face prism and
reversed indices, the cofibrancy of both `Y` and its constant diagram, and the
realization homotopy-invariance and constant-realization isomorphism. I added the
proof-only import `Mathlib.AlgebraicTopology.ExtraDegeneracy`, the exact Mathlib
match of the prism proof dependency. The other realization-homotopy proof dependency
has no recorded Lean declaration, so there is no module to import yet.

Second, project search found `HomotopicalAlgebra.barTensorParameterMap` in the
downstream `SimplicialBarProjectiveResolution` module. This is the same elementary
parameter-map helper as the new node's `parameterMap`, although its bar realization
only applies to chain diagrams and is not a realization of arbitrary simplicial
objects. To avoid another exported helper or an import of a downstream consumer, I
removed `parameterMap` and built `relationRight` directly from the already shared
`SimplicialUndercategory.tensorTranspose` and the universal tensor element. I removed
its entry from the new node's `lean.declarations`; all its mathematical construction
clauses are retained. There are now nine declarations, not the worker report's ten.
The source-level new-node construction and its naturality theorem are unchanged.

The worker report's `status: unsplit` observation is historical: the current node has
`status: split`; delivery preserves the current base metadata. No dependency repair
or statement correction was required. Compilation with `scompile.py` checks both
sibling modules separately; the only postponed proofs are the named `sorry`
declarations required by stage 2.

Second-reader search details (the wrapper appended their actual results to
`searches.jsonl`): LeanSearch "realization of split augmented simplicial object in
model category" found `SimplicialObject.Split` constructors and splittings; LeanFinder
"Weighted colimit of a simplicial diagram by representable simplices and contraction
to an augmented object" found ordinary augmentations and standard simplices; Loogle
`"ExtraDegeneracy"` found the extra-degeneracy structure, section, and chain-complex
homotopy equivalence. I opened `ExtraDegeneracy.lean` lines 68--192 and the
`SimplicialObject.Homotopy` structure: its general-category prism is usable as a
proof dependency but does not assert the model-category realization conclusion.
Direct `rg` using "tensor.*coend", "coend.*tensor", "extra.?degeneracy", and the
proposed namespaces over all three named Lean source roots found the bar helper
above, the bar-specific realization, and unrelated constructions. The exact generic
realization and augmentation are absent.

I also repeated LeanSearch with "coequalizer construction of the weighted geometric
realization of a simplicial object in a category with simplicial tensors", which
returned the generic coequalizer and `SSet.toTop`; a wrapper grep for
`realization|Realization|coend|Coend` in AlgebraicTopology found only simplicial-set
topological realization and its properties. None supplies the general construction.
For the new node I checked `kind: definition`, `status: split`, the self-contained
construction statement and all three dependencies, source places, three search kinds,
empty proof fields, null Mathlib match, worker creation record, ancestor and via route,
chapter/unit, both `lean_audit` states, complete Lean record and declarations list.
Its named compatibility theorem states the equality explicitly asserted by the
construction and has the naturality argument in its docstring; every definition
contains actual data, and the descent is determined uniquely by its summand maps.
I added the required main-definitions overview to its module docstring.
