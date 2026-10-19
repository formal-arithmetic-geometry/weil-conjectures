## Worker report

The module `Sheaf.AlgebraicTopology.JoyalCartesianPushoutProduct` states
`SSet.joyal_cartesian_pushout_product`.  It uses the chosen cartesian monoidal
structure on simplicial sets: the pushout is formed from
`a ⊗ₘ 𝟙 C` and `𝟙 A ⊗ₘ b`, and the displayed map is the pushout desc map to
`B ⊗ D`.  The binders `M`, `hcof`, and `hweak` identify the supplied model
category with the Joyal model structure from the dependency node.  The
hypotheses `ha` and `hb` render degreewise injectivity of `a` and `b`.
The first conclusion renders degreewise injectivity of the pushout-product map.
The second and third conclusions render categorical-equivalence preservation
when `a`, respectively `b`, is a weak equivalence of `M`.

The pushout compatibility proof supplied to `pushout.desc` is rendered by
`MonoidalCategory.tensorHom_def` and `MonoidalCategory.whisker_exchange`.
All universes are explicit (`u`, `v`), and the testing simplicial sets have
universe `max u v` exactly as in the Joyal model-structure and functor-test
nodes.  Empty simplicial sets and identity maps are included by the universal
quantifiers; no nonemptiness or fibrancy assumptions are added.

Dependency declarations used:

- `Sheaf.AlgebraicTopology.JoyalModelStructure`,
  `SSet.exists_joyal_model_structure` (the Joyal model structure, its
  degreewise-injective cofibrations, weak-equivalence test, and factorization
  properties).
- `Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest`,
  `SSet.joyal_functor_equivalence_test` (quasicategory internal-homs and the
  equivalence of Joyal testing formulations used in the product argument).

Searches made:

- `msearch.py ... leanfinder "Cartesian pushout product of degreewise injective
  simplicial maps in the Joyal model structure"`: hits were ordinary
  simplicial-set monomorphism/cobase-change, cartesian monoidal, and Kan model
  declarations; no Joyal pushout-product theorem.
- `msearch.py ... loogle '"CategoryTheory.Limits.pushout", "equivalence"'`:
  zero hits (the query was accepted but no matching declaration was returned).
- `msearch.py ... grep "Joyal|categoricalEquivalence|pushout" AlgebraicTopology`:
  hits were generic pushout/model-category and `JoyalTrick` declarations; no
  specialized Joyal cartesian pushout-product result.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` for
  `joyal_cartesian_pushout_product` and the phrase “Cartesian pushout-product”:
  no existing declaration.

Edge cases checked: `a` or `b` an identity, empty simplicial sets among
`A,B,C,D`, and the degree-zero component of the pushout.  The statement keeps
all constructions in `SSet.{u}` and tests categorical equivalences in every
`SSet.{max u v}`.


## Second reading by NB

I independently read the unchanged node statement and its four proof steps, the
sandbox theorem, both dependency nodes and their actual source declarations.
There is no repair note for this item, no statement_change, no new definition
node and no dependency module in this delivery.

Source check: the source is HTT, not a Stacks tag. I opened
https://people.math.harvard.edu/~lurie/papers/HTT.pdf and read Theorem the project server
(printed p. 89), Corollary the project server (printed p. 92, PDF zero-based page 109),
and the discussion and Proposition the project server (printed pp. 94--95).
The corollary applies to any categorical equivalence and any simplicial set K;
there is no fibrancy, nonemptiness or finiteness assumption. The model structure
has monomorphism cofibrations. The hFun testing convention is identified with
its weak equivalences in Proposition the project server. Cobase change of a trivial
cofibration followed by two-out-of-three gives exactly this node's conclusion.
The source's product-preservation result is being used with the model axioms,
not asserted to be a verbatim pushout-product statement in that corollary.

Object/hypothesis/conclusion checklist (H3):

1. Fixed universe of small, unmarked simplicial sets: `{A B C D : SSet.{u}}`.
   Verdict: exact. Mathlib's SSet is the simplex-category presheaf in Type u;
   no marked structure, Kan condition or quasicategory condition is imposed on
   A, B, C or D.
2. The Joyal model structure and categorical equivalences of the dependency:
   `M : HomotopicalAlgebra.ModelCategory SSet.{u}`, `hcof` and `hweak`.
   Verdict: exact interface. I read `SSet.exists_joyal_model_structure` in
   `Sheaf.AlgebraicTopology.JoyalModelStructure`: hcof and hweak reproduce its
   first two conjuncts, including `uliftFunctor.{v, u}` and `max u v`.
   They identify the model structure whose existence that dependency supplies,
   rather than add an assumption about the input maps. All weak-equivalence
   occurrences use M's explicit projection, so they do not pick up a Kan model
   instance. Mathlib's ModelCategory itself supplies the model axioms.
3. Two simplicial maps: `(a : A ⟶ B) (b : C ⟶ D)`.
   Verdict: exact, with the node's order of domain and codomain.
4. Both maps degreewise injective: `ha` and `hb` quantify over every
   `n : SimplexCategoryᵒᵖ` and assert `Function.Injective (a.app n)` and the
   corresponding property of b. Verdict: exact, including degree zero.
5. Products and the specified pushout: `tensorHom a (𝟙 C)` and
   `tensorHom (𝟙 A) b` have common domain A tensor C and targets B tensor C
   and A tensor D. I read Mathlib's simplicial-set Monoidal module:
   `tensorHom_app_apply` is the pair of the component maps. Thus these tensors
   are the node's degreewise cartesian products. Verdict: exact.
6. Canonical map to B times D: `pushout.desc` uses
   `tensorHom (𝟙 B) b` on B times C and `tensorHom a (𝟙 D)` on A times D.
   Its compatibility proof is tensor functoriality. Verdict: the actual
   canonical pushout-product map, with neither an arbitrary comparison map
   nor an additional commutative-square hypothesis. Each repeated term has
   the same span, legs and target.
7. Degreewise injective pushout-product: the first conjunct quantifies over
   all simplex objects and asserts injectivity of this desc map's component.
   Verdict: exact, unconditional once ha and hb hold.
8. Categorical-equivalence clause if a is one: the second conjunct is
   `M.categoryWithWeakEquivalences.weakEquivalences a →` the same property
   of the displayed desc map. Verdict: exact.
9. Categorical-equivalence clause if b is one: the third conjunct is the
   corresponding implication for b. Verdict: exact. Together the two
   implications are equivalent to the node's either/or condition; they do
   not require both a and b to be equivalences.
10. Every construction stays in the input universe: all four objects, their
    tensor products and the pushout live in SSet u. Only the testing object
    in hweak is in SSet (max u v). Verdict: exact, with independent u and v;
    v = 0 permits tests in u, and larger v permits arbitrary enlargements.

Dependency reading: `SSet.joyal_functor_equivalence_test` in
`Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest` accepts the very same
M and hweak interface. Its first conjunct supplies quasicategories for the
internal homs into every larger quasicategory, including on an identity map
of any K, as needed in the proof's currying step. It is a proof-only import;
the model-structure dependency is publicly imported. Both interfaces are
usable without repair. The theorem docstring covers all four DAG proof
steps: degreewise union/intersection, currying/product preservation,
cobase-change lifting, and two-out-of-three/symmetry with universe closure.
There are no new definitions or hollow data. The main proof is only sorry;
the inline simp terms merely type the canonical pushout map.

Edge cases: empty A or C gives the same set pushout and union description;
empty B forces A empty and likewise for D and C. When a or b is an identity,
the canonical pushout-product is an isomorphism. At n = 0 no positive-degree
horn assumption occurs. Arbitrary nonfibrant inputs are included. There is
no index family, ring, characteristic or scheme in this statement. The
universes impose no equality u = v or extra smallness beyond the node.

Independent duplicate searches (H4):

- LeanFinder via msearch: "Leibniz tensor of simplicial monomorphisms preserves
  Joyal weak equivalences". Eight hits: Kan/Quillen generators and
  cofibrations, hoFunctor monoidality and ordinary products; no match.
- Loogle via msearch: `"pushout", "trivialCofibrations"`. Zero hits.
- LeanSearch via msearch: "The cartesian model category axiom for categorical
  equivalences of simplicial sets". Eight hits, generic model-category
  declarations or Kan/Quillen cofibrations; no match.
- Grep via msearch: `pushoutProduct|IsPushoutProduct|trivialCofibrations`
  in AlgebraicTopology. Twenty-five hits, all generic model-category
  infrastructure; no Joyal pushout-product theorem.
- Direct rg searches over the upstream WeilConjectures tree, project
  lean/Sheaf and Mathlib AlgebraicTopology used Joyal, categorical equivalence,
  Leibniz, pushout-product and IsPushoutProduct. I opened Mathlib's
  SimplicialSet/PushoutProduct.lean: it identifies subcomplex unions with the
  existing generic pushout product but does not state the Joyal axiom.
  Inner/PushoutProduct treats inner anodyne maps, a narrower hypothesis.
  I also opened the project's JoyalHomotopyExponentials.lean: its conclusions
  concern the localization, rigidification and exponentials, not this map.
  MarkedPointCartesianModel and the Segal/local model results concern different
  categories. No existing declaration supplies this theorem.

Mismatch repaired: the recorded lean.statement differed from the file in the
indentation of two compatibility-proof terms. I replaced that record with
an exact extraction of the theorem signature. The Lean source and the
mathematical statement were correct and remain unchanged. Only the item's
lean field changes against the repository node.

Validation: scompile.py compiled the sole delivered module cleanly, both in
the sandbox (1.5 s) and library context (2.0 s), with no errors or warnings.
The recorded lean.statement is byte-for-byte equal to its source signature.
deliver2.py --no-push printed OK: commit f315d89c92 passes preflight and
compiles; nothing pushed by the dry run. The final delivery repeats preflight.
