## Worker report

The module `lean/Sheaf/CategoryTheory/EquivalenceAnodyneFactorization.lean` states
`SSet.Enhanced.equivalence_anodyne_factorization`. It uses the fixed universe `u` for
all simplicial sets. Its hypotheses are `[Quasicategory L]`, `[Quasicategory M]`, an
enhanced functor `e : L ⟶ M`, and `he : IsFunctorEquivalence e`, rendering the node's
assumption that `e` is an equivalence between small quasicategories. The conclusion is
`∃ N i r`, with `N : SSet.{u}`, `i : L ⟶ N`, and `r : N ⟶ M`; the conjunctions render,
in order, that `N` is a quasicategory, `i ≫ r = e` strictly, `i` is a monomorphism
(degreewise injective), `SSet.rightAnodyneExtensions i`, and
`SSet.modelCategoryQuillen.I.rlp r`. The last predicate is Mathlib's right lifting
property against every boundary inclusion `∂Δ[n] ↪ Δ[n]`, including `n = 0`, hence is
the recorded trivial Kan fibration notion.

The statement dependency declarations used are:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.IsFunctorEquivalence` and `SSet.Quasicategory`;
* `Sheaf.CategoryTheory.RightAnodyne`, `SSet.rightAnodyneExtensions`;
* Mathlib `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`,
  `SSet.modelCategoryQuillen.I` and its `MorphismProperty.rlp`.

The proof-plan imports (without using them in the postponed proof) are
`Sheaf.CategoryTheory.RightFibrationExponentiation`,
`Sheaf.CategoryTheory.RightFibrationFibers`,
`Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`, and
`Sheaf.CategoryTheory.RightFibrationContractibleFibers`. The small-object
factorization and the right-fibration definition are recorded as Mathlib or unstated
proof dependencies and therefore introduce no additional imports here.

I checked the identity equivalence, the case `L = M = Δ[0]`, empty simplicial sets where
allowed by the quasicategory hypotheses, and the dimension-zero boundary lifting clause.
No nonemptiness or equality of universes beyond the fixed `u` was added. `Mono i` is the
categorical monomorphism predicate on simplicial sets, which is the degreewise injective
condition used by the source proof.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "factorization of an equivalence of quasicategories into
  right anodyne map and trivial Kan fibration"`: returned ordinary
  `SSet.modelCategoryQuillen.I/J`, quasicategory horn filling, and model-category
  declarations, with no exact factorization theorem;
* `msearch.py ... loogle "SSet.modelCategoryQuillen.I.rlp,
  SSet.rightAnodyneExtensions, Quasicategory"`: no hit (the compound query was
  rejected as an unknown identifier, while direct source search found the component
  declarations);
* `msearch.py ... grep "right.?anodyne|equivalence_anodyne_factorization"
  AlgebraicTopology`: no exact existing statement;
* `rg` over `WeilConjectures/` and the project's `lean/Sheaf/`: found the component
  declarations and related anodyne/fibration lemmas, but no declaration of this
  factorization.

The source is Kerodon Corollary the project server (Tag 02NE), right-handed version via
Corollary the project server (Tag 02NC). The proof is postponed with `sorry` exactly as required;
there is no `STATEMENT-DISPUTED` flag and no node correction.

## Second reading by Q124

I independently read the node's statement and six proof steps, its three statement
prerequisites and their actual declarations, the sandbox module, and the relevant
Mathlib definitions. The source is Kerodon, not the unrelated Stacks tags 02NE/02NC.
I opened https://kerodon.net/tag/02NE, https://kerodon.net/tag/02NC and
https://kerodon.net/tag/02ND. Corollary the project server states the left-cofinal factorization;
taking simplicial opposites gives the right-cofinal version, and the project server says a
categorical equivalence is cofinal on both sides. There is no additional standing
fibrancy, nonemptiness, or finiteness assumption in these source statements.
The quasicategory hypothesis on M implies the intermediate N is a quasicategory by
lifting inner horns. Thus the node is a faithful specialization of the source.
I also read Stacks `simplicial.tex` lines 5520–5545, including Definition 08NL,
for the dependency's boundary-lifting definition.

The list of objects, hypotheses, and conclusion clauses, matched independently:

1. Small simplicial sets L and M in a fixed arbitrary universe: `{L M : SSet.{u}}`
   and the explicitly bound `universe u`. Correct; neither is a nerve of an ordinary
   category or restricted to finite simplicial sets.
2. Both L and M are quasicategories: `[Quasicategory L] [Quasicategory M]`.
   Correct; this is Mathlib's inner-horn filler class, imported by the recorded
   `Sheaf.CategoryTheory.EnhancedDiagramsCones` prerequisite.
3. A coherent functor e from L to M: `(e : L ⟶ M)`, a simplicial natural
   transformation. Correct; no monomorphism or fibration assumption on e is added.
4. e is a functor equivalence: `(he : IsFunctorEquivalence e)`. Correct. I opened
   `EnhancedDiagramsCones.lean` lines 222–235: the predicate asks for a simplicial
   quasi-inverse and coherent natural equivalences of both composites with the
   identities. `AreNaturallyEquivalent` is an equivalence edge in the internal
   functor simplicial set, using the recorded inverse-triangle definition.
   This is the dependency node's precise notion, not merely a weak homotopy equivalence.
5. There exists a small intermediate N in the same universe: `∃ (N : SSet.{u})`.
   Correct, and its existential follows all the input hypotheses.
6. The maps have the prescribed endpoints: `(i : L ⟶ N) (r : N ⟶ M)` inside
   that existential. Correct; no arbitrary replacement of an input map is used.
7. N is a quasicategory: the first conjunct `Quasicategory N`. Correct; N is
   existentially quantified without presupposing a class instance.
8. The composite is exactly e: `i ≫ r = e`. Correct; categorical composition
   has the order r after i, and this is equality of simplicial maps, not a homotopy.
9. i is degreewise injective: `Mono i`. Correct by Mathlib
   `NatTrans.mono_iff_mono_app` and `CategoryTheory.mono_iff_injective`; I checked
   these uses in the simplicial-set sources and the latter declaration in
   `CategoryTheory/Types/Basic.lean`.
10. i is right anodyne: `rightAnodyneExtensions i`. Correct. I read the recorded
    `RightAnodyne.lean` definition: the infimum of properties containing isomorphisms
    and horns with `0 < i`, closed under pushouts, small transfinite compositions
    and retracts. Since `i : Fin (n+1)`, this is exactly `0 < i ≤ n`; n=0 has
    no positive index. There is no extra zero-dimensional generator.
11. r is a trivial Kan fibration: `modelCategoryQuillen.I.rlp r`. Correct. I read
    `CategoryWithFibrations.lean` lines 35–42: I is `ofHoms (fun n ↦ ∂Δ[n].ι)`
    for every natural n. I read `MorphismProperty/LiftingProperty.lean` lines 38–41:
    `rlp` quantifies over all members of that family. `Boundary.lean:92` gives
    `boundary_zero = ⊥`, so n=0 enforces vertex surjectivity exactly as in 08NL.
    This uses the dependency's recorded Mathlib match and introduces no duplicate.

Edge cases were checked mathematically against the actual signature. The identity
map can factor through itself. Empty L=M is allowed (vacuous inner horns); there is
no `Nonempty` hypothesis. An empty source with nonempty target fails the equivalence
hypothesis, as it should. The point and a non-injective equivalence of groupoids are
covered; `Mono` is required only of i. The dimension-zero boundary condition is
present in I.rlp and is not replaced by positive-dimensional lifting. The last horn
index n is included in the right-anodyne definition, whereas index zero is excluded.
There are no ring, characteristic, scheme, or numerical parameters. The universe u
is arbitrary, and the node itself asks that L, M and N fit in that same fixed universe.
No edge case of the node is removed.

Independent duplicate searches used different language from the first worker:

* LeanSearch via msearch: "A simplicial equivalence admits a factorization by final
  horn attachments and a boundary lifting map". Eight results concerned the
  epi/mono factorization in the simplex category and all-horn Quillen fibrations;
  their returned types give no one-sided factorization of functor equivalences.
* LeanFinder via msearch: "One sided horn cellular factorization of a categorical
  equivalence with contractible right fibration fibers". Eight results were the
  all-horn J generators, Kan fillers, and inner-horn quasicategory fillers. None
  states this theorem.
* Loogle via msearch: `"SSet", "factor"` returned zero hits.
* `rg` in Mathlib AlgebraicTopology, the whole upstream WeilConjectures tree and
  the project's lean/Sheaf used `right.?anodyne|final.?horn|anodyne.*factor|factor.*anodyne`,
  and a separate exact-name search used `equivalence_anodyne_factorization` and
  `EquivalenceAnodyneFactorization`. No exact theorem exists. Nearby project
  results concern exponentiation, fibers, or marked anodyne maps, not this statement.
  Mathlib's abstract model-category factorization or all-horn anodyne predicate
  does not supply the one-sided assertion. The three notions used are reused from
  the recorded declarations, with no private copies.

No new nodes or dependency modules were delivered. There is no statement_change,
no statement correction, and no repair-note file for this item. The source, node
and Lean agree, so no citer audit for a correction is needed.

Mismatches found and repaired:

* The old proof docstring said the right map lifts "all positive horns". That
  incorrectly suggests all horns in positive dimensions. I replaced it with the
  precise right-horn bounds `d ≥ 1`, `0 < j ≤ d`.
* The old proof paragraph compressed the six DAG steps, omitted their exact node
  references and finite-smallness checks, and blurred the section-space homotopy
  with the boundary-lift homotopy. I expanded it to six numbered steps matching
  the node, including the strict section, P, the prescribed endpoints for H,
  the fiber contraction, and the final all-boundary conclusion.
* The recorded proof dependencies `def-coef-infinity-fibrations`,
  `def-weil-pbc-category-colimit`, and the Mathlib small-object factorization leaf
  lacked their direct imports. I added `Sheaf.CategoryTheory.InfinityFibrations`,
  `Mathlib.CategoryTheory.Limits.HasLimits`, and
  `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument` as
  proof-only imports. The boundary-family import is now public because the
  statement uses that recorded statement prerequisite.

The signature and node lean.statement are unchanged and verbatim equal (checked
by extracting the text before `:= by`). No definition or extra theorem was added;
the sole theorem proof remains `sorry`. All lines are at most 100 characters, every
universe and variable is explicitly bound, and the namespace/source/blueprint
conventions are satisfied. The repaired module compiled through the prescribed
`scompile.py Q124 lem-coef-infinity-equivalence-anodyne-factorization` wrapper:
both sandbox and library-path checks returned exit 0, no warnings or errors, each
in 1.9 seconds. No global build or direct git command was run.
