## Worker report

The module `Sheaf.CategoryTheory.FlatSemisimplicialDerivedHom` states
`CategoryTheory.SemisimplicialRingedTotal.flat_semisimplicial_derived_hom` with one
`sorry`. There are no new definitions, dependency repairs, or statement changes.

The source was read in `literature/stacks-project/spaces-simplicial.tex`, labels
`lemma-nullity-cartesian-modules-derived` and `lemma-hom-cartesian-modules-derived`
(Tags 0D9R and 0D9S), together with the full proofs of their abelian-object analogues
`lemma-nullity-cartesian-objects-derived` and `lemma-hom-cartesian-objects-derived`.
The DAG explicitly supplies the face-only adaptation and imposes all-negative Hom
vanishing, which includes each of the degree-dependent vanishings in these proofs.
The Lean docstring carries all seven proof steps of the item, including the first
obstruction calculation, telescope factorization, and the shifted-coproduct argument
needed to rule out phantom morphisms.

Hypotheses and clauses, matched with the node:

- The semisimplicial ringed total category and its derived evaluations are the
  dependency's `RingDiagram D`, total sheaf proof `h`, and `P : Presentation R h`.
  The explicit `F` and `D` binders describe the coherent diagram of small sites;
  `Cat.{u,u}` and the total/fibre categories use precisely the dependency's size
  convention. No separate choice of derived categories or ringed pullbacks is made.
- Exactness of every transition module pullback is `exact`, quantifying over all
  `a : i ⟶ j` in `SemiSimplexCategoryᵒᵖ` and requiring preservation of finite
  limits and finite colimits by `(P.pullback a).ordinary`. The dependency supplies
  additivity. For additive functors between these abelian module categories this
  is exactly exactness, as in the recorded free-adjoint dependency.
- `B C : (R.total h).D` are objects of the actual unbounded derived total category.
  Both cartesian assumptions appear unchanged as `hB : P.IsCartesian B` and
  `hC : P.IsCartesian C`. Their predicate requires invertibility of every specified
  derived transition; it is not an independently chosen system.
- `B_n` and `C_n` are `(P.evaluation i).derived.obj B` and its counterpart for C.
  Objects of `SemiSimplexCategoryᵒᵖ` correspond exactly to all natural-number
  degrees, including zero.
- All-negative vanishing is `negative : ∀ i (t : ℤ), t < 0 → Subsingleton (...)`,
  where the Hom type is from the evaluated B to the evaluated C shifted by t.
  Since these categories have zero morphisms, subsingleton means exactly the zero
  Hom group; it neither adds nor removes the zero-degree condition.
- The displayed evaluation map is the explicit function taking `w : B ⟶ C` to
  the family `fun i ↦ (P.evaluation i).derived.map w`, valued in the subtype of
  compatible families. The subtype proof is the existing derived transition's
  naturality, so the function is canonical. `Function.Bijective` asserts precisely
  the node's bijection, without choosing an arbitrary equivalence.
- A morphism `a : i ⟶ j` in the opposite category is the injection from degree j
  to degree i. The subtype equation is
  `(P.pullback a).derived.map (v j) ≫ (P.derivedTransition a).app C =
  (P.derivedTransition a).app B ≫ v i`.
  Lean uses diagrammatic composition, so this is exactly
  `theta_C Lf^*(v_m) = v_n theta_B`, the symmetric ordering of the displayed
  compatibility equation in the node. It quantifies over every injection,
  including identities and composites.
- The final conjunct quantifies over every `w : B ⟶ C` and asserts that
  `(P.evaluation (op (SemiSimplexCategory.mk 0))).derived.map w = 0` implies
  `w = 0`. This is the node's final degree-zero assertion, under the same hypotheses.

Dependency declarations used:

- Public import `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`:
  `CategoryTheory.SemisimplicialRingedTotal.RingDiagram`, `.RingDiagram.total`,
  `.Presentation`, `.Presentation.IsCartesian`, `.Evaluation.derived`, and
  `.Presentation.derivedTransition`, together with the dependency's actual
  pullback and site categories. The entire module and these signatures/docstrings
  were read, including the representative normalization and derived transition laws.
- Proof import `Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint`:
  `CategoryTheory.SemisimplicialRingedTotal.semisimplicial_evaluation_free_adjoint`
  and `EvaluationFreeExtension`, read with its labelled-summand, adjunction, and
  exactness clauses.
- Proof import `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂` and `yoneda_exact₃`,
  the two exactness clauses of `lem-weil-pbc-hom-out-of-triangle-exact`; their
  signatures were read in Mathlib.
- `lem-sfb-semisimplicial-cartesian-simplex-filtration` has no Lean record in the
  read repository. It is a proof-only dependency and no part of its statement is
  needed to type this item. Its import is deferred until it is stated; the entire
  proposed proof and every use of the filtration remain in the docstring. No
  missing statement notion is omitted or replaced.

Edge cases checked before writing:

- Degree zero is present; t = 0 is excluded from the vanishing assumption exactly
  as required. All negative integers, with no lower bound, are included.
- Identity injections and arbitrary compositions are included in the compatibility
  predicate. Injections from [0] to every [n] exist, supporting the degree-zero
  conclusion; the index is face-only, with no degeneracy assumption.
- Zero B or zero C gives singleton Hom types and compatible zero families; the
  final assertion retains the expected meaning. The empty site and zero ring are
  not excluded by the binders.
- No boundedness, finite amplitude, separate countability, augmentation, or chosen
  global morphism is assumed. Arbitrary u remains as in the existing small-site
  interface, and its actual derived-category universe is inherited.

Searches actually run:

- `msearch.py ... leanfinder` with query “Morphisms between cartesian derived objects
  on a flat semisimplicial ringed site are compatible families of morphisms if all
  negative Hom vanish”: 8 hits, concerning ordinary sheaf compatibility and Hom
  extensionality, including `compatiblePreservingOfFlat` and
  `Presheaf.IsSheaf.hom_ext`; no derived-total-category morphism descent theorem.
- `msearch.py ... loogle` with query `Functor.map, Function.Bijective`: 0 hits.
- `msearch.py ... grep` with query `semisimplicial|Semisimplicial` in
  `CategoryTheory`: 0 hits.
- `msearch.py ... leansearch` with query “Maps of cartesian derived objects on a flat
  semisimplicial ringed total site correspond bijectively to compatible component
  maps under negative Hom vanishing”: 8 hits; component and homotopy results,
  including `AlgebraicTopology.DoldKan.MorphComponents.a`; no exact match.
- Direct `rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for
  `semisimplicial.*hom|hom.*semisimplicial` (case-insensitive): only the downstream
  `SpaceNegativeExtHyperdescent` proof docstring mentions this input. No declaration.
- Direct searches for the item id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json`: no hits. Searches for
  `flat_semisimplicial_derived_hom|FlatSemisimplicialDerivedHom` in those directories,
  Mathlib, and `lean/Sheaf` also found no existing declaration.
- Read Mathlib's `SemiSimplexCategory` definition and `homEquiv`: its objects are
  finite nonempty ordinals and its morphisms exactly order embeddings. No new
  ordinal or injection notion is needed.

Validation: the prescribed `scompile.py` compiled the module in sandbox and library
modes on the server with no errors or warnings. The Lean source has no line over
100 characters and sets `autoImplicit false`. Only this node's `lean` field is
changed. There is no disputed statement or node fault.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
