## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent` states
`AlgebraicGeometry.invertible_affine_limit_descent`, with the sole proof `sorry`.
The node is Stacks Project, Limits, Tag 0B8W (lemma-descend-invertible-modules),
clause (2). I read the full source lemma and proof in `literature/stacks-project/limits.tex`.
Only the item's `lean` record changes. There are no new definitions, dependency repairs,
or statement corrections.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A small directed nonempty set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Directed sets here are preorders, as specified
  in the project convention. The index lives in the scheme universe, not an unrelated one.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. For `h : i ≤ j`, the transition
  `q_ji` is `D.map (homOfLE h).op`; functoriality supplies all system identities.
- Every stage is quasi-compact by `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]`.
  This notion imposes no separation axiom.
- Every stage is quasi-separated by `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`.
  Mathlib's `quasiSeparated_iff_quasiSeparatedSpace` identifies this with the
  terminal morphism being `AlgebraicGeometry.QuasiSeparated`.
- Affine transitions are `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`.
  They impose no affineness or Noetherian condition on any stage.
- The limit scheme is `c.pt` of `c : Cone D`, with projections `c.π.app (op i)`.
  The cone's naturality is precisely the compatibility equations in the node.
- `(hc : IsLimit c)` is the full categorical universal property: every compatible
  family, encoded by a cone with vertex `T`, has a unique lift to `c.pt`.
  No chosen construction of the limit or extra hypothesis on its projections is used.
- An arbitrary invertible module is `(L : c.pt.Modules) [L.IsInvertible]`, using
  exactly the recorded scheme-module invertibility predicate.
- `∃ i : I, ∃ L_i : (D.obj (op i)).Modules` gives a stage and a module there.
- `L_i.IsInvertible` is the required invertibility of the descended module.
- `Nonempty (((Scheme.Modules.tensorPullback (c.π.app (op i))).obj L_i) ≅ L)`
  is the required existence of an isomorphism from its tensor pullback to `L`.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`. Its local trivializations use the
  structure module on an open neighbourhood of each point.
- `def-pc-module-pullback`: `WeilConjectures.AlgebraicGeometry.TensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`. The file is absent from the older
  local checkout; I read it with `scompile.py --source`. It explicitly constructs the
  inverse-image/change-of-rings tensor formula, and is available in the live library.
  An initial sandbox alias was discarded after this source check; none is delivered.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated`, used via its scheme specialization
  `QuasiSeparatedSpace` and the recorded Mathlib equivalence above.
- `pqf-def-affine-morphism`: its `mathlib_match` is
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `AlgebraicGeometry.IsAffineHom`.

The available proof modules are imported without `public`: Modules.Dual,
TensorPullbackFinitePresentation, ModulePullbackTensor, SiteTensorFunctoriality,
and RingedSiteModules. The proof-only dependency
`lem-trf-fp-modules-affine-limit-descent` has no recorded declaration and hence no
module to import; its three clauses are named explicitly in the six-step proof docstring.
It is not a notion required to type the statement, so it is not restated here.

Edge cases checked: the empty indexing set is expressly excluded, as in the node;
singleton and constant systems are included. Empty schemes and an empty limit remain
allowed, and no nonzero-module condition is added. Invertibility over an empty scheme
is the ordinary vacuous local condition. Non-affine and non-Noetherian qcqs stages
remain included. The universes of schemes and index agree under the project convention;
there is no independent index-universe restriction, and all universes and variables
are bound explicitly. No finite trivializing cover is assumed in the signature.

Searches executed through `msearch.py`, group Q124 and this item:

- LeanFinder: `An invertible sheaf on an inverse limit of quasi compact quasi separated
  schemes with affine transitions descends to a finite stage`. Eight hits, all about
  global sections, affine opens or morphism factorization in AffineTransitionLimit;
  none descends an invertible module.
- LeanSearch: `Line bundles descend to a stage of a directed inverse limit of qcqs schemes
  with affine transition maps`. Eight hits, about sections, affine opens, affine limits,
  and an unrelated first-order direct limit; no matching line-bundle statement.
- Loogle: `"IsInvertible", "IsLimit"`. Zero hits.
- Mathlib grep: `(invertible|line.bundle).*(descen|limit)|(descen|limit).*(invertible|line.bundle)`.
  Three unrelated hits: spectrum non-invertibility, topology of a module, group-object limits.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and in
  `lean/Sheaf`, for invertibility/descent/limits and the exact node id. The invertibility
  definitions, dual and Picard descent results are present, but no general qcqs
  affine-transition inverse-limit theorem for invertible modules was found.
- `rg` in `dag/lean_names_upstream.json` and upstream sources for the proposed name
  `invertible_affine_limit_descent`: no collision.

No STATEMENT-DISPUTED finding. `scompile.py` compiled the theorem without errors or warnings;
the final import adjustment is validated again by the dry run.

## Second reading by Q124

This is a single-worker consistency rereading; the dispatch assigns the independent
review to the maintainer. I reopened the node and final module and checked each binder
and conclusion against the correspondence above. In particular, the direction of the
opposite indexing category gives maps from later to earlier stages, the cone projections
have the correct direction for tensor pullback, and `Nonempty` quantifies over actual
isomorphisms. `IsLimit` includes both existence and uniqueness for every compatible
cone, rather than merely the projection equations. Both stage compactness hypotheses,
affine transitions, and the required invertibility at the descended stage are retained.
The preliminary concern about a missing tensor-pullback source was resolved by reading
the live source, and the duplicate draft alias was removed. No mathematical mismatch
or statement correction was found. The final file has one theorem with `sorry`, no
helper definitions or local notation, and all binders and the universe are explicit.

## Second reading by Q44

I independently reopened the current node and the landed module. The theorem uses a small nonempty directed preorder, an inverse diagram in the opposite category, compact and quasi-separated stage hypotheses, affine transition maps, an actual limit cone with `IsLimit`, and an invertible module on its apex. The conclusion provides a stage, an invertible module there, and a `Nonempty` isomorphism from its tensor pullback to the original module. Every hypothesis and conclusion clause is represented by the corresponding explicit Lean binder or conjunct; no extra Noetherian, affine-stage, or nonzero assumption appears. The module's only proof is `sorry`, and all variables and universes are explicit. This matches the node and the already landed declaration exactly.
