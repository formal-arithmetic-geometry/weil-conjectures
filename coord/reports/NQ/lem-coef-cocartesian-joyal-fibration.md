## Worker report

The module `Sheaf.AlgebraicTopology.CocartesianJoyalFibration` states
`SSet.cocartesian_joyal_fibration`. Its only theorem proof is `sorry`; no new definitions,
new nodes, dependency repairs, or statement corrections are needed. The item node changes
only in `lean`.

Source checked: [HTT Proposition the project server](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
printed p. 209, with self-duality of categorical fibrations immediately following on p. 210.
The proposition states the cartesian assertion for simplicial sets, with arbitrary base;
reversing simplex orders gives its cocartesian dual. The explicit lifting formulation is
also the one used in the source proof. This agrees with the node as written.

Clause-by-clause correspondence:

- “In a fixed universe” and “simplicial sets” are `{X S : SSet.{u}}`,
  `(A B : SSet.{u})`; the simplicial map is `(p : X ⟶ S)`.
- “Either a cartesian fibration or a cocartesian fibration” is
  `_hp : Marked.Over.relativeFibration false p ∨ Enhanced.cocartesianFibrationOver p`.
  The first predicate includes `InnerFibration p` and cartesian edge lifts with prescribed
  target, without quasicategory parameters. The second includes the same inner-fibration
  condition and cocartesian edge lifts with prescribed source, again over arbitrary bases.
  Both use the existing final/initial outer-horn edge predicates for dimensions at least 2.
- “Every degreewise injective” map is `(i : A ⟶ B)` with
  `_hi : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (i.app n)`.
  This includes degree zero.
- “Categorical equivalence” is `_he`, literally the `hoFunctor`/internal-functor test of
  `SSet.exists_joyal_model_structure`: for every `C : SSet.{max u v}` satisfying
  `Quasicategory C`, restriction along `uliftFunctor.{v, u}.map i` induces an ordinary
  categorical equivalence. The universe `v` is explicit; `max u v` admits every enlargement
  and includes tests of the input size. There is no new private equivalence predicate.
- The top and bottom maps are `(f : A ⟶ X)` and `(g : B ⟶ S)`.
  The square `p f = g i` is `_comm : f ≫ p = i ≫ g`, using Lean's diagrammatic composition.
- The diagonal is `∃ h : B ⟶ X`; its two required strict equations are
  `i ≫ h = f ∧ h ≫ p = g`. These are precisely `h i = f` and `p h = g`.
- “Fibration in the Joyal model structure” is rendered by this explicit right lifting
  property against every degreewise injective categorical equivalence, exactly the
  fibration characterization in `exists_joyal_model_structure` and in the node.
- There is no `Quasicategory`, `Nonempty`, or other condition on `X`, `S`, `A`, or `B`.
  The only quasicategory condition concerns the test object `C`, as prescribed by the
  definition of categorical equivalence.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.JoyalModelStructure`, `SSet.exists_joyal_model_structure`:
  supplies the exact categorical-equivalence universe convention and Joyal lifting meaning.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`,
  `SSet.Enhanced.cocartesianFibrationOver`, publicly reexporting the original
  `Sheaf.CategoryTheory.InfinityFibrations`: supplies the recorded dependency interface,
  `SSet.Enhanced.IsCartesianEdge`, and `SSet.Enhanced.IsCocartesianEdge`.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`,
  `SSet.Marked.Over.relativeFibration` and `SSet.Marked.Over.IsDistinguishedEdge`:
  supplies the arbitrary-base cartesian condition; its Boolean conventions were inspected.
  The node's `marked_relative_cartesian_model` theorem supplies relative model data in
  the proof plan, without being made an extra hypothesis of this theorem.
- The stated proof dependencies
  `Sheaf.AlgebraicTopology.CartesianBaseEquivalenceInvariance` and
  `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus` are ordinary imports, providing
  `SSet.Marked.Over.cartesian_base_equivalence_invariance` and
  `SSet.Marked.Over.relative_marked_anodyne_calculus` for stage 3. All six proof steps
  of the node are retained in the theorem docstring, including the strict lift over the
  replacement base and final relative Kan homotopy correction.

Edge cases checked before writing:

- Identity `p` over an arbitrary, possibly non-quasicategorical `S`: its edge lifts and
  lifting diagonal are the given base maps. No fibrancy of `S` has slipped into the type.
- Empty `S`: any displayed map to it forces its source empty; the square has its unique
  empty diagonal. Empty `B` similarly forces `A` empty.
- Empty `X`: the square forces `A` empty. A categorical equivalence from the empty
  simplicial set forces `B` empty (test against the empty quasicategory), so a diagonal
  exists; no nonemptiness hypothesis is needed. The same test handles empty `A` generally.
- A point base gives the usual quasicategory/fibrant-object case; the statement still
  allows every arbitrary-base case.
- The injectivity condition quantifies all simplex degrees and the edge predicates retain
  their exact `n ≥ 2` range. All simplicial objects in the square are in `u`, while only
  categorical-equivalence test objects may be enlarged. No universe equality is imposed.

Searches for existing statements (2026-10-17):

- `msearch.py grep` query `Joyal|categoricalFibration|cartesian.*[Ff]ibration|[Ff]ibration.*cartesian` in `AlgebraicTopology`: 5 hits; returned `Mathlib/AlgebraicTopology/ModelCategory/JoyalTrick.lean`, `Mathlib/AlgebraicTopology/ModelCategory/JoyalTrick.lean`, `Mathlib/AlgebraicTopology/ModelCategory/JoyalTrick.lean`, `Mathlib/AlgebraicTopology/ModelCategory/JoyalTrick.lean`, `Mathlib/AlgebraicTopology/ModelCategory/JoyalTrick.lean`.
- `msearch.py loogle` query `"InnerFibration", "fibration"`: 12 hits; returned `SSet.instIsMultiplicativeInnerFibrations`, `SSet.instIsStableUnderBaseChangeInnerFibrations`, `SSet.instIsStableUnderRetractsInnerFibrations`, `SSet.instRespectsIsoInnerFibrations`, `SSet.innerFibrations`, `SSet.InnerFibration`, `SSet.mem_innerFibrations`, `SSet.quasicategory_of_innerFibration`.
- `msearch.py leanfinder` query `Every cartesian or cocartesian fibration over an arbitrary simplicial set is a Joyal categorical fibration`: 8 hits; returned `SSet.modelCategoryQuillen.instCategoryWithFibrations`, `SSet.modelCategoryQuillen.fibrations_eq`, `SSet.modelCategoryQuillen.fibration_iff`, `SSet.modelCategoryQuillen.instCategoryWithCofibrations`, `SSet.modelCategoryQuillen.instHasLiftingPropertyιHornHAddNatOfNatOfFibration`, `CategoryTheory.Nerve.quasicategory`, `SSet.Quasicategory`, `SSet.modelCategoryQuillen.J`.
- `msearch.py leansearch` query `Every cartesian or cocartesian fibration of simplicial sets is a Joyal fibration`: 8 hits; returned `SSet.modelCategoryQuillen.fibration_iff`, `SSet.modelCategoryQuillen.fibrations_eq`, `SSet.modelCategoryQuillen.instCategoryWithFibrations`, `SSet.modelCategoryQuillen.instHasLiftingPropertyιHornHAddNatOfNatOfFibration`, `CategoryTheory.Functor.IsFibered.toIsPreFibered`, `HomotopicalAlgebra.ModelCategory.hasLiftingProperty_of_joyalTrick`, `HomotopicalAlgebra.ModelCategory.hasLiftingProperty_of_joyalTrickDual`, `CategoryTheory.Functor.IsFibered`.

The returned Mathlib declarations concern all-horn Kan–Quillen fibrations, plain inner
fibrations, nerves, abstract model-category Joyal tricks, or ordinary fibered categories;
none gives this arbitrary-base cartesian/cocartesian-to-Joyal assertion. Read the defining
signatures in `Mathlib.AlgebraicTopology.Quasicategory.InnerFibration` and
`Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations` to check that distinction.

Direct `rg` searches used `Joyal|categoricalFibration|cartesian.*[Ff]ibration|[Ff]ibration.*cartesian`
in the upstream `WeilConjectures` source (no hits), and this node id in that source (no hits).
The same concept search in `lean/Sheaf` found the existing dependency interfaces and
quasicategory-base characterizations, but no arbitrary-base theorem; exact searches for
`cocartesian_joyal_fibration|cocartesian_joyal_lifting|CocartesianJoyalFibration` in Mathlib,
upstream, side sources and `dag/lean_names_upstream.json` found no declaration. The consumer
`FilteredFiberSmallConeLifting` mentions the node only in its proof docstring. No duplicate
notion or theorem is introduced. No repair note exists for this item.

Validation: the prescribed `scompile.py NQ lem-coef-cocartesian-joyal-fibration`
compiled this module cleanly in both sandbox and library modes (1.9 s and 2.1 s),
with no errors or warnings. Delivery dry run is the remaining check.
No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by NQ

I independently read the sandbox node and module, the three statement-dependency nodes
and their recorded declarations, and the signatures of both additional proof dependencies.
No repair note exists. The delivered node has no `statement_change`, new nodes, or
new dependency modules. Its only changed field against the shared node is `lean`.

Source reading: the source of this item is HTT, not a Stacks tag. I opened
[HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), Proposition the project server
(printed p. 209; PDF page index 226), its proof, the following self-duality observation
(p. 210), Definition the project server, and Remark the project server. The proposition applies to simplicial
sets without fibrant or nonempty bases. Its proof starts with the same inclusion and
categorical-equivalence lifting square and replaces the base by a quasicategory only
inside the proof. Definition the project server likewise requires an inner fibration and cartesian
edge lifts, without a quasicategory hypothesis on the original base. The cocartesian
case follows by reversal. There is no source-wide geometric or finiteness hypothesis.

Here is my item-by-item inventory and comparison with the Lean:

1. Objects: a map of simplicial sets in a fixed universe. The binders
   `{X S : SSet.{u}} (p : X ⟶ S)` introduce exactly those objects and that map.
   Verdict: exact; neither object has an extra instance parameter.
2. Hypothesis: `p` is either cartesian or cocartesian over that arbitrary base.
   `_hp : Marked.Over.relativeFibration false p ∨ Enhanced.cocartesianFibrationOver p`
   renders the two alternatives. I unfolded the dependency definitions in
   `MarkedRelativeCartesianModel`, `InfinityFibrationsOverSimplicialBases`, and the
   publicly imported `InfinityFibrations`. The Boolean `false` selects final-horn
   cartesian edges and `δ 0`, the target; its existential edge has the prescribed
   target and maps to the given base edge. The cocartesian predicate selects initial
   outer horns and `δ 1`, the source. Its extra quantified target vertex `b` is simply
   the endpoint of the given edge, not an added constraint. Both predicates include
   `InnerFibration p`. The edge conditions quantify dimensions at least two and
   require strict horn fillers over the base. Verdict: exactly the node's horn
   conventions; the old quasicategory-only fibration predicates are not substituted.
3. Objects quantified in the conclusion: every `A`, `B` and map `i : A ⟶ B` in
   the input universe. These are `(A B : SSet.{u}) (i : A ⟶ B)`, after `_hp`.
   Verdict: correct objects and quantifier order; there is no extra marked structure.
4. Hypothesis on `i`: degreewise injective. This is
   `_hi : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (i.app n)`.
   Verdict: all degrees, including vertices, and no additional cofibration condition.
5. Hypothesis on `i`: categorical equivalence with the dependency's precise meaning.
   `_he` requires equivalence of the ordinary categories produced by `hoFunctor`
   from restriction on internal functor simplicial sets, for every quasicategory
   `C : SSet.{max u v}`. This is literally the weak-equivalence test in
   `SSet.exists_joyal_model_structure`, with `f` there replaced by `i`.
   I also read Mathlib's homotopy-category construction: it is the category generated
   by vertices and edges modulo degenerate identities and triangle relations.
   Verdict: the same equivalence notion, not Kan weak homotopy equivalence or
   equivalence merely of the homotopy categories of `A` and `B`.
6. Square objects and hypothesis: maps `f : A ⟶ X`, `g : B ⟶ S` and `pf = gi`.
   The binders `(f : A ⟶ X) (g : B ⟶ S)` and
   `_comm : f ≫ p = i ≫ g` render them exactly, using diagrammatic composition.
   Verdict: strict equality, with the correct domains and codomains.
7. Conclusion: a simplicial diagonal `h : B ⟶ X` with both strict triangle identities.
   `∃ h : B ⟶ X, i ≫ h = f ∧ h ≫ p = g` says exactly this; it imposes no
   marking preservation, uniqueness, chosen lift, or homotopy-only replacement.
   By the fibration characterization in `exists_joyal_model_structure`, this is
   precisely being a Joyal fibration. Verdict: all clauses present, none added.
8. Explicit absence of assumptions on `X`, `S`, `A`, `B`: no `Quasicategory`,
   `KanComplex`, `Nonempty`, or finite-size typeclass occurs for these objects.
   `Quasicategory C` is only the required categorical-equivalence test premise.
   Verdict: the source's full scope is retained.

Edge cases: identity maps over a non-quasicategorical base are allowed. If the base
is empty, every simplicial set mapping to it is empty. If `B` is empty, `A` is empty
and the diagonal is the empty map. If `X` is empty, the given `f` forces `A` empty;
testing the categorical equivalence against the empty quasicategory then forces `B`
empty as well. Empty `A` is therefore also handled without a hidden nonemptiness
premise. A point base specializes to the usual fibrant-object case. There is no
external index set, ring, characteristic, or scheme parameter. Simplicial degree zero
is explicitly included in `_hi`; the edge predicates start at their correct degree
two. `u` and `v` are declared, and all variables are bound under `autoImplicit false`.
`max u v` is never smaller than the input universe; specializing `v` to zero includes
the original-universe test, and the recorded Joyal interface covers every enlargement.
No equality of unrelated universes has been added.

Independent duplicate searches (2026-10-17), with different queries from the author:

- LeanFinder: `Cartesian fibration has right lifting property with respect to
  categorical equivalence monomorphism` returned eight ordinary fibered-category
  declarations, including `CategoryTheory.Functor.IsFibered.isStronglyCartesian_of_isCartesian`
  and `HasFibers.fiber_factorization`. Their types concern ordinary categories,
  not arbitrary simplicial maps; none is this statement.
- Loogle: `"HasLiftingProperty", "InnerFibration"` returned no hits.
- LeanSearch: `An inner fibration with cartesian edge lifts is a categorical
  fibration over any simplicial base` returned eight hits: ordinary fibered-category
  declarations, abstract model-category fibration fields, and
  `SSet.modelCategoryQuillen.fibration_iff`. I read the latter interface and
  `Mathlib.AlgebraicTopology.Quasicategory.InnerFibration`: the former is the
  all-horn Kan–Quillen fibration and the latter supplies only inner horns.
- `msearch.py grep` for `cocartesian|categoricalFibration|joyal_fibration` returned
  ordinary cocartesian morphisms and monoidal-category commentary, not this theorem.
  Direct `rg` for `categorical.{0,25}fibration`, cartesian/cocartesian near Joyal,
  and this node id covered Mathlib, upstream `WeilConjectures`, side `lean/Sheaf`,
  and `dag/lean_names_upstream.json`. There was no upstream or Mathlib match.
  The side results were the recorded dependencies and distinct interfaces. I opened
  `IsLMCategoricalFibration` (restricted to the fixed LM-operad base),
  `isofibration_pullback_limit`, and `isofibration_base_change`; the latter two
  concern pullback comparisons and do not assert this lifting theorem.

H4–H9 checks: no definition is introduced, so there is no hollow data or private copy.
The only theorem has proof `sorry`. Both docstrings give the source and this blueprint
id, and the theorem docstring renders each of the node's six proof steps: fibrant base
replacement; relative-model extension; marked inverse and sharp path; strict lift over
the replacement base; relative Kan path correction; and the opposite dual. All five
imports serve the recorded statement/proof dependencies. No local notation, local
instance, hidden `let`, or unbound variable occurs. Every Lean line is at most 100
characters. The node's `lean.statement` is verbatim the signature before `:= by`.

Mismatches found: none. I left the correct node record and Lean module untouched and
added this independent reading only. No source-based correction or citer audit is
needed. The prescribed `scompile.py` compiled the delivered file in sandbox and library
modes cleanly (1.6 s and 1.8 s), without errors or warnings. An initial invocation with
a relative path from the read-only repository failed before compilation; rerunning with
the absolute sandbox path produced these successful results.
