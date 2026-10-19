## Worker report

The new module `Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent` states
`AlgebraicGeometry.Scheme.Modules.finitePresentation_descent_affineLimit` with one
`sorry`. It is precisely the three clauses of Stacks Project, Limits, Tag 01ZR,
`lemma-descend-modules-finite-presentation`, read in `literature/stacks-project/limits.tex`.
The node's statement, dependencies and proof plan are unchanged. No new nodes or dependency
repairs are needed. The only other declaration is the fully constructed canonical comparison
`AlgebraicGeometry.Scheme.Modules.affineLimitTensorPullbackComparison`, listed in
`lean.declarations`; it introduces no new pullback notion and contains no postponed proof.

Hypotheses and clauses, checked against the node and the Stacks source:

- A small nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. The preorder convention includes partially ordered sets and
  follows the current directed-set convention. The index universe is the scheme universe.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. Functoriality supplies identity and composition
  of transitions. For `hij : i ≤ j`, its transition is `D.map (homOfLE hij).op`.
- Affine transitions are exactly `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`.
- Every stage is quasi-compact by `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]`.
- Every stage is quasi-separated by `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`.
  Mathlib's `quasiSeparatedSpace_iff_quasiSeparated` identifies this with quasi-separatedness
  of the terminal morphism, as specified in the dependency record.
- The scheme limit with its projections and its universal property is `(c : Cone D)
  (hc : IsLimit c)`. Its scheme is `c.pt` and its projections are `c.π.app (op i)`.
  The cone equation is `c.w (homOfLE hij).op`; `IsLimit` supplies unique factorization
  of every cone through `c`, not merely projection compatibility.
- Modules are `X.Modules`, definitionally `SheafOfModules.{u} X.ringCatSheaf`, the
  Zariski specialization of the recorded general-site module category. Morphisms are
  the same sectionwise linear sheaf morphisms. No second category is introduced.
- Local finite presentation is the existing `SheafOfModules.IsFinitePresentation`:
  locally the cokernel of a map between finite sums of the ring sheaf. This is exactly
  the local finite free exact sequence in the node. No separate quasi-coherence, rank,
  flatness, or Noetherian hypothesis is imposed.
- All object and map pullbacks are `Scheme.Modules.tensorPullback`, never the distinct
  Mathlib `Modules.pullback` functor.
- Clause (1) is the first conjunct: every `F : c.pt.Modules` with `F.IsFinitePresentation`
  admits `i : I` and `F_i : (D.obj (op i)).Modules`, with `F_i.IsFinitePresentation` and
  `Nonempty ((tensorPullback (c.π.app (op i))).obj F_i ≅ F)`. This is an isomorphism of
  module sheaves, not an equality of isomorphism classes.
- Clause (2) is the second conjunct: arbitrary `i`, arbitrary finitely presented `F_i,G_i`,
  and arbitrary morphism `u` between their limit pullbacks admit `j`, `hij : i ≤ j`, and
  `u_j` between their transition pullbacks. Its equality is
  `comparison(F_i).inv ≫ (tensorPullback p_j).map u_j ≫ comparison(G_i).hom = u`.
  The comparison is constructed as the inverse component of the recorded normalized
  `tensorPullbackSectionComp p_j p_ji`, followed by `eqToIso` of the actual cone equation.
  Thus it is the canonical iterated-pullback identification; it is neither an arbitrary
  existential isomorphism nor an extra comparison hypothesis.
- Clause (3) is the third conjunct: arbitrary `i`, finitely presented `F_i,G_i`, and
  arbitrary maps `u_i,v_i` with equal maps under `tensorPullback p_i` admit `j ≥ i`
  with equal maps under `tensorPullback p_ji`.

Dependency declarations used, after reading their signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff condition).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`
  and `quasiSeparatedSpace_iff_quasiSeparated`, with `QuasiSeparatedSpace` from topology.
  These geometric dependencies are exposed through `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently
  the Mathlib `SheafOfModules` category, specialized by the existing `Scheme.Modules`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and
  `tensorPullbackSectionComp`; the public import retains the upstream `tensorPullback`.
  The upstream source absent in the older checkout was read using `scompile.py --source
  WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation`, the existing local finite presentation notion.

The proof docstring contains all nine steps of the DAG proof, including descending inverses,
forcing both inverse identities, stabilizing overlap equations and cocycles before gluing,
and separately treating map descent and equality descent. Recorded proof dependencies are
imported: `Sheaf.Algebra.FinitePresentationColimit` for the three affine module clauses;
`WeilConjectures.AlgebraicGeometry.Descent` for effective fpqc gluing and full faithfulness;
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSectionsBijective` and
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` for the affine comparisons;
`Mathlib.AlgebraicGeometry.Modules.Tilde` for the tilde adjunction; and
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` for affine-open descent, restricted limits,
eventual open equality and the global-sections colimit. No unstated proof interface is
asserted as a hypothesis of the new statement.

Edge cases checked before writing:

- Empty index types are excluded exactly by the node's nonempty hypothesis; a singleton
  index and identity transitions remain allowed. The comparison is still the canonical one
  when `i = j`; no strict inequality is imposed.
- Empty schemes and zero module sheaves are allowed. Finite presentations may have rank zero.
  If the limit is empty, the eventual-equality assertion is still the Stacks assertion:
  quasi-compact affine-transition inverse systems eventually detect the relevant finite data.
- Non-affine, non-separated qcqs stages are allowed; neither affineness of the stages nor
  separatedness is imposed. Only the transition morphisms must be affine.
- No finiteness of the directed set, no chosen least stage, no field characteristic, and
  no Noetherian condition appears. The same universe `u` for indices and schemes avoids
  an unsupported larger-index limit assertion.
- The comparison orientation was checked: its source is `p_j^*(p_ji^*M)` and target
  `p_i^*M`; inverse, pulled-back map, and forward comparison therefore compose to exactly
  the domain and codomain of `u`.

Searches for an existing exact statement (all through the prescribed search wrapper or
read-only source searches):

- LeanFinder query: "Finitely presented sheaves of modules and morphisms descend along
  inverse limits of quasi compact quasi separated schemes with affine transition maps".
  Eight hits: local finite-presentation definitions and a structure-sheaf section equality
  theorem (`exists_app_map_eq_zero_of_isLimit`); no three-clause sheaf-module descent theorem.
- Loogle query: `SheafOfModules.IsFinitePresentation`. Five hits, giving the exact existing
  definition and its quasi-coherence consequences, but no limit descent theorem.
- LeanSearch query: "Finitely presented sheaves of modules descend along inverse limits of
  quasi compact quasi separated schemes with affine transition morphisms". Eight hits on
  finite-presentation predicates and local data; no descent statement.
- Mathlib grep wrapper query: `IsFinitePresentation|descend.*[Mm]odule`, restricted to
  `AlgebraicGeometry`: zero hits. The separate source inspection found the finite-presentation
  definition in `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` and reused it.
- Read-only `rg` over Mathlib AlgebraicGeometry, upstream WeilConjectures AlgebraicGeometry
  and `lean/Sheaf/AlgebraicGeometry` for affine-limit/finite-presentation descent: results
  include scheme-morphism descent, flat/complex descent, and the consuming invertible-module
  descent theorem, but no theorem saying these three clauses for arbitrary finitely
  presented module sheaves. `grep -rn` of the exact item id in upstream WeilConjectures
  returned no occurrence.
- Exact declaration-name search for `affineLimitTensorPullbackComparison` and
  `finitePresentation_descent_affineLimit` in Mathlib, upstream, the shared Lean tree,
  and `dag/lean_names_upstream.json`: no existing names.

No disputed statement or node fault was found. No source-based correction is needed.
The only field changed in the copied node is `lean`.

Validation: `scompile.py Q153 lem-trf-fp-modules-affine-limit-descent` compiled the delivered
file both in its sandbox and at its library path, with no errors or warnings. Both checks
finished within four seconds under the wrapper's unchanged 60-second per-file limit.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
