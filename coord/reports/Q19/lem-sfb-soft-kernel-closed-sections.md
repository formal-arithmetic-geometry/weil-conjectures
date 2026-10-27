## Worker report

The module `Sheaf.Topology.SoftKernelClosedSections` states
`TopCat.Sheaf.surjective_closedSections_and_soft_of_soft_kernel`, with its only
proof `sorry`. It is the two-clause assertion of Demailly IV Proposition (4.14),
printed p.205. The source PDF was read online at
https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf,
including Definition (4.9), the standing paracompactness convention, and the
closed-cover argument in Proposition (4.13). There is no statement correction,
new definition, dependency repair, or disputed statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The topological space is `{X : TopCat.{u}}`. `[ParacompactSpace X]` means every
  open cover has a locally finite open refinement, exactly as defined in Mathlib
  `Topology/Compactness/Paracompact.lean`. `[T2Space X]` is Hausdorffness.
- The abelian category of abelian sheaves on the opens site is
  `X.Sheaf AddCommGrpCat.{u}`, Mathlib's notation for
  `CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}`.
- `K : ShortComplex (X.Sheaf AddCommGrpCat.{u})` supplies the three objects
  `K.X₁ = A`, `K.X₂ = B`, `K.X₃ = C`, arrows `K.f` and `K.g = p`, and their
  zero composite. `hK : K.ShortExact` supplies exactness and the two endpoint
  conditions; it is not an assumption of objectwise surjectivity.
- Every occurrence of `(S : Set X), IsClosed S → ...` quantifies over every
  closed subset, with no nonemptiness or compactness condition.
- The inclusion is exactly
  `TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩`.
  `S` carries its induced topology. `pullback AddCommGrpCat.{u}` is Mathlib's
  inverse-image sheaf construction, namely presheaf pullback followed by
  sheafification (`TopCat.Sheaf.pullbackIso`). It therefore gives the sheaf of
  locally represented germs along S, rather than an evaluation at S as an open.
- `hA` states surjectivity of the adjunction unit at `op (⊤ : Opens X)` for
  `K.X₁`. Its source is Γ(X,A), and its target is Γ(S,i_S⁻¹A): pushforward
  evaluates the latter on the inverse image of the top open, definitionally
  the top open of S. This is exactly the node's definition of softness.
- The first conjunct is `Function.Surjective` for the top-open component of
  `(pullback ... inclusion).map K.g`. This is precisely
  Γ(S,B|_S) → Γ(S,C|_S) induced by p, for every closed S.
- The second conjunct is an implication. Its antecedent is the same softness
  expression for `K.X₂`; its conclusion is the same expression for `K.X₃`.
  Together with `hA`, this says that A and B soft imply C soft. Softness of B
  is not imposed on the first conjunct.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`, is the recorded statement
  dependency. Its docstring retains Mathlib `Sheaf` for the sheaf component;
  the opens site is already canonical, so no extra site-axiom binder is added.
  The module is publicly imported as required.
- `Mathlib.Topology.Sheaves.Functors`: `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackIso`, `TopCat.Sheaf.pushforward`, and
  `TopCat.Sheaf.pullbackPushforwardAdjunction` give the actual inverse image
  and the canonical restriction of global sections.
- `Mathlib.Topology.Sheaves.Abelian` supplies the abelian sheaf category;
  `CategoryTheory.ShortComplex.ShortExact` supplies short exactness.
- Proof dependencies are imported privately:
  `WeilConjectures.Topology.AbelianSheafShortExactStalkwise`,
  `TopCat.shortExact_iff_stalkFunctor_map_shortExact`;
  `Mathlib.Topology.ShrinkingLemma`, `exists_subset_iUnion_closure_subset`;
  and `Mathlib.Order.Zorn`, `zorn_subset`. These declarations and their full
  signatures/docstrings were read. The latter two nodes have `mathlib_match`
  records, so no replacement records or modules are needed.
- The landed `Sheaf.Topology.SoftAbelianSheafAcyclic` was read for compatibility:
  its `TopCat.Sheaf.subsingleton_H'_top_of_soft` uses exactly the same inline
  inverse-image-unit expression for softness. It is a downstream consumer, so
  it is not imported here. No independent softness predicate is introduced.

Edge cases checked mathematically before writing: S empty has the unique
section of the sheaf on the empty space; X empty is allowed by all binders;
S = X is included by taking `Set.univ` with its closedness proof, and inverse
image along that inclusion canonically recovers the original sheaf. Zero
sheaves, the identity quotient with zero kernel, and the zero quotient have
exactly their expected lifting behavior. No finiteness, local compactness,
countability, nonempty-space, or additional exactness hypothesis is present.
The universe u is explicit and arbitrary, matching the existing topological
abelian-sheaf API; every variable is explicitly bound.

Searches for existing notions/statements (2026-10-24):

- `msearch.py ... leanfinder` query: "A short exact sequence of abelian sheaves
  on a paracompact Hausdorff space with soft kernel is surjective on sections
  along every closed subset". Eight results, including
  `CategoryTheory.ShortComplex.ShortExact.surjective_g`, sheaf local
  surjectivity, and Mayer-Vietoris short exactness. None states this theorem.
- `msearch.py ... loogle` query: `"Sheaf", "surjective"`. Twelve results,
  primarily presheaf-of-modules epimorphism criteria. No soft-kernel result.
- `msearch.py ... leansearch` query: "Soft kernel sheaves give surjective maps
  on sections along closed subsets and soft quotients". Eight results,
  including `TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective`
  and local-surjectivity criteria. No soft-kernel lifting theorem.
- `msearch.py ... grep` query: `\bsoft\b|IsSoft|softSheaf`. Only the style
  linter's unrelated phrase "soft upper bound" appeared in Mathlib.
- `rg -n -i '\bsoft\b|IsSoft|sectionsAlong' lean/WeilConjectures lean/Sheaf`
  found the acyclicity theorem with its inline softness hypothesis, not a
  predicate or the assigned statement. The specific new declaration name
  was also searched in both roots, Mathlib, and `dag/lean_names_upstream.json`:
  no collision. `grep -rn 'lem-sfb-soft-kernel-closed-sections'
  lean/WeilConjectures` found no implementation.
- A DAG concept search found only the item and the two acyclicity consumers.
  `python3 tools/blueprint_refs.py search 'soft'` returned zero blueprint nodes.
  The compact-object example was opened, but its current module is withdrawn
  and contains no declarations; the standing brief's module conventions and
  the landed acyclicity module supply the applicable format.

Validation: `scompile.py Q19 lem-sfb-soft-kernel-closed-sections
<.../SoftKernelClosedSections.lean>` passed in both sandbox and library modes
(1.8 seconds each), with no compiler errors or unexpected warnings. The node
copy changes only `lean`; its signature is extracted verbatim from the module.

## Second reading by Q19

Self-check by the author; no independent worker is claimed, since the dispatcher
brief prohibits starting agents and assigns independent review to the maintainer.
Reopened the node and the completed file and compared both conclusions and each
binder. The first conjunct depends only on A being soft, not on B being soft;
the second adds B's softness and concludes C's softness. All three occurrences
of softness use the same canonical unit at the ambient top open, and the lifting
map instead uses the inverse-image functor on p at the subspace top open. The
subspace inclusion uses the actual subtype topology, not an open-subset coercion.
The closed-set quantifier includes the empty and whole subsets. The proof
paragraph preserves all seven DAG steps and the four available proof imports.
No mismatch was found and no source statement was changed.
