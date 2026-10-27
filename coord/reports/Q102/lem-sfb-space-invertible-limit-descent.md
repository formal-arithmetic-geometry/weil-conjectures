## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceInvertibleLimitDescent` states
`AlgebraicGeometry.AlgebraicSpace.lineModule_descent_affineLimit`, with one whole-proof
`sorry` and no new definitions. The statement is Stacks Tag 0D2X(2), read in
`literature/stacks-project/spaces-limits.tex`, lemma-descend-invertible-modules,
together with the system hypotheses of Tag 07SK, lemma-descend-finite-presentation.
The declaration docstring contains all four accepted DAG proof steps, including
finite presentation of the tensor, descent of both inverse maps and both equations,
and the second tensor-pullback comparison at the final stage.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The base scheme is `{S : Scheme.{u}}`; no finiteness or separation assumption on S.
- The small nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. The index universe is the scheme universe, following
  the project's index-size convention. A preorder is the directed-set convention.
- The inverse system over S is `D : Iᵒᵖ ⥤ AlgebraicSpace S`; its arrows go from
  later stages to earlier stages, including all identity and composition equations.
- Quasi-compactness is `hqc`: at every stage there is a scheme `U : Over S` and
  `a : yoneda.obj U ⟶ (D.obj i).obj.obj` with `CompactSpace U.left`, `IsEtale a`
  and `IsSurjective a`. This is exactly the node's quasi-compact surjective etale chart.
- Quasi-separatedness is `hqs`: for every pair of affine scheme tests U,V mapping
  to a stage, their fibre product is represented by W and is quasi-compact.
  `IsPullback (yoneda.map p) (yoneda.map q) a b` gives the actual representing
  square; `CompactSpace W.left` expresses quasi-compactness of that inverse image
  of the diagonal. Affine rectangles form an affine basis of the product, so this
  is equivalent to quasi-compactness of the diagonal. The same formulation is used
  by the recorded finite-presentation descent theorem. In particular it does not
  replace absolute quasi-separatedness by separation relative to the possibly
  non-quasi-separated base S.
- Affine transition morphisms are `haff`, using the existing `IsRepresentableWith`
  applied to `IsAffineHom p.left`. This expresses actual scheme-test base changes
  with affine projections. Over affine test schemes their sources are affine,
  equivalently the node's definition. No representability witness is arbitrary.
- The specified limit and its projections are `c : Cone D`, `hc : IsLimit c`,
  and `c.π.app (op i)`, respectively. No globally chosen limit or extra
  existence hypothesis is required.
- A line module on the limit is `L : c.pt.Modules` and `hL : c.pt.IsLineModule L`.
  `Modules` is the existing category of modules over the regular-functions structure
  sheaf, and `IsLineModule` is the existing covering-sieve condition of local
  isomorphism with its unit module on the small etale site.
- The conclusion quantifies `∃ (i : I) (L_i : (D.obj (op i)).Modules)` and requires
  `(D.obj (op i)).IsLineModule L_i`. Thus the model is itself a line at a finite stage,
  rather than merely a finitely presented model.
- `Nonempty ((moduleTensorPullback (c.π.app (op i))).obj L_i ≅ L)` is precisely
  existence of the required module-linear pullback isomorphism. The pullback is
  the recorded canonical tensor pullback, not an independently supplied functor.
- The explanatory scheme convention uses the existing Zariski/small-etale
  quasi-coherent equivalence and its invertibility clauses; no extra scheme-only
  hypothesis or conclusion is introduced into the general space theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `EtaleSite`, `structureSheaf`,
  `Modules`, `etalePullback`, `IsLineModule`, in the AlgebraicSpace namespace.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentRingMap`, together
  with its publicly imported enlarged-site construction; this is the dependency's
  current recorded module, imported directly as required.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `AlgebraicGeometry.Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`;
  its local-unit clauses identify scheme invertibility with small-etale line modules.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, the ordinary scheme convention.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  defined as left adjoint to the chart-normalized canonical `moduleDirectImage`,
  with `moduleTensorAdjunction` retaining its normalization. Its already-landed
  owning node `def-trf-space-etale-module-functors` is added to `stmt_deps` to cite
  this exact existing pullback interface. No existing node is repaired or redefined.

All available proof dependencies are plain imports: the cochain tensor-universe
module, line-evaluation inverse-pair module, finite-presentation module continuity
module and ringed-topos tensor-pullback module. The proof dependency
`lem-sfb-space-tensor-inverse-line` has no recorded Lean module on the read base;
it remains explicitly named in the proof docstring. It introduces no object needed
in this theorem's signature, so no separate statement is invented here.

Edge cases checked before writing: the empty index type is excluded exactly by
Nonempty, as required; a singleton directed system and identity transitions are
included; non-antisymmetric directed preorders are included. Empty spaces and the
zero module on an empty space remain included (line triviality is local and permits
the zero-ring case). No nonemptiness of the base or limit, characteristic, nonzero
ring, noetherian, properness, flatness or base quasi-separatedness hypothesis is added.
The isomorphism is existential and need not be chosen as data. Both source and
conclusion use the same existing module categories and coefficient universe.

Searches for an existing statement:

- `msearch.py ... leanfinder "An invertible module on the limit of a directed
  inverse system of quasi compact quasi separated algebraic spaces with affine
  transition maps descends to an invertible module on some stage"`: eight hits,
  all scheme affine-transition limit results about global sections or affine loci;
  none states line-module descent for algebraic spaces.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace, IsInvertible, IsLimit"`:
  zero hits, unknown identifier AlgebraicGeometry.AlgebraicSpace in Mathlib.
- `msearch.py ... grep "AlgebraicSpace|invertible.*[Ll]imit|[Ll]imit.*invertible"
  AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for IsLineModule and invertible/line
  limit-descent names, plus the exact node id, and the upstream-name table: no exact
  statement. The closest is `AlgebraicGeometry.invertible_affine_limit_descent` in
  `Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent`; its full signature was read
  and quantifies schemes with ordinary Zariski modules, so it does not state this
  algebraic-space theorem. `SpaceFinitePresentationModuleLimit` concerns finitely
  presented objects and does not guarantee an invertible model.
- Searched the proposed new declaration and module name in the upstream-name table
  and both source trees: no existing declaration.

Validation: the delivered module compiled through the prescribed `scompile.py`,
which compiled both its sandbox and library module modes in 1.7 seconds each,
with no errors or non-sorry warnings. No global build or direct git command was run.
No statement fault or STATEMENT-DISPUTED issue was found; the statement, proof and
proof-dependency list are unchanged.

## Second reading by Q102

A separate second pass by this worker reread the node, source 0D2X(2)/07SK, the
full signature and docstring of the finite-presentation descent dependency, and
this file. No other agent was started, as the dispatcher's explicit instruction
prohibits that; independent delivery review belongs to the maintainer.

Checked every binder against the bullets above: S is unrestricted, I is explicitly
small/nonempty/directed, D is over S, hqc gives the specified atlas, hqs tests the
actual diagonal via affine pairs, haff gives representable affine transitions, c/hc
give the given limit, and L/hL give an arbitrary line. Checked each conclusion:
i is a real stage, L_i belongs to its module category and satisfies IsLineModule,
and the isomorphism uses the cone projection's canonical moduleTensorPullback.
No mismatch or correction was found. The existing scheme comparison imports cover
the explanatory scheme convention without restricting the theorem to schemes.
The proof records all four DAG steps and both inverse equations; the only postponed
proof is the named theorem itself. No duplicate notion, hidden local notation,
local instance, unbound implicit, additional theorem or hollow definition is present.
