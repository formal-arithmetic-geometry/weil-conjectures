## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition` states
`AlgebraicGeometry.exists_etale_closed_immersion_decomposition_of_unramified_at_points`.
Its proof is `sorry`; no definition or auxiliary theorem is added.

Hypothesis and clause correspondence:

- Schemes and the morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Separatedness: `[IsSeparated f]`, without any global finite-type assumption.
- Base point and the list of points: `(s : S) (n : ℕ) (x : Fin n → X)`.
- All listed points lie over s: `hx : ∀ i, f.base (x i) = s`.
- Unramified at each listed point: `hunramified` gives an open `O` containing
  `x i`, `LocallyOfFiniteType (O.ι ≫ f)` and
  `IsOpenImmersion (pullback.diagonal (O.ι ≫ f))`, exactly the recorded conjunction.
- Étale neighbourhood: existential `U`, `g`, `u`, with `Etale g` and `g.base u = s`.
  No residue-field isomorphism is imposed.
- The fibre product is the actual chosen `pullback f g`, with `pullback.fst` and
  `pullback.snd` its projections to X and U.
- Nonnegative integers m_i: `m : Fin n → ℕ`; the pieces are indexed by
  `Σ i : Fin n, Fin (m i)`.
- W and the pieces are open subschemes: `W` and `V a` belong to
  `(pullback f g).Opens`. The subscheme and inclusion are Mathlib's
  `Scheme.Opens.toScheme` and `Scheme.Opens.ι`.
- Closedness: `IsClosed` of the underlying set of W and each `V a`.
- Pairwise disjointness: `Pairwise (fun a b ↦ Disjoint (V a) (V b))`, together
  with `∀ a, Disjoint W (V a)`.
- Covering: `W ⊔ iSup V = ⊤`. Disjoint open subschemes covering the scheme
  express exactly the disjoint union decomposition, without a separate chosen coproduct.
- Clause (1): each `(V a).ι ≫ pullback.snd f g` is an `IsClosedImmersion`;
  `u ∈ Set.range` of its underlying map says its image contains u.
- Clause (2): for every `p : ↥(pullback f g)` in W with second projection u, its first projection
  differs from every `x i`.
- The in-particular clause: if `∀ y, f.base y = s ↔ ∃ i, y = x i`, then
  every `p : ↥(pullback f g)` in W has second projection different from u. This is emptiness of W_u.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-proper-morphism`: its recorded `IsSeparated` component in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`. Properness is not assumed.
- `def-weil-unramified-morphism`: its mathlib_match is the conjunction of
  `AlgebraicGeometry.LocallyOfFiniteType` (Morphisms.FiniteType) and
  `AlgebraicGeometry.IsOpenImmersion` (OpenImmersion) of the diagonal.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in Morphisms.Etale.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd` in
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; the Scheme instance
  comes from Mathlib.AlgebraicGeometry.Pullbacks.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, imported by Separated.

Edge cases checked: n = 0 permits the empty V-family and W = the whole pullback;
all exclusion quantifiers are vacuous. The in-particular clause then applies exactly
when the original fibre is empty. The list need not be injective: repeated points
are allowed, and some m_i can be zero. An empty X is allowed. The chosen point s
rules out empty S, and u rules out an empty neighbourhood. No characteristic,
Noetherian hypothesis or residue-field equality is imposed. Scheme and point universes
are shared and the finite index types exclude no finite cardinality.

Searches (2026-10-11):

- msearch LeanFinder: "separated morphism unramified at finitely many fibre points
  etale locally decomposes into clopen closed immersions and a remainder".
  Eight hits on general étale and formally unramified APIs; no decomposition theorem.
- msearch Loogle: "AlgebraicGeometry.Etale, AlgebraicGeometry.IsClosedImmersion".
  Zero hits.
- msearch grep: "unramified.*(decomp|local)|closed.*immersion.*decomp" in
  AlgebraicGeometry. Seven hits concerning general morphism properties; no match.
- msearch LeanSearch: "unramified separated morphism etale local decomposition closed
  immersions". Service unavailable (Internal Server Error).
- rg in WeilConjectures and lean/Sheaf: "unramified.*(decomp|local)|etale.*local.*(split|decomp)|04HI|lem-weil-pbc-unramified-etale-local-decomposition".
  General unramified results and the finite-unramified/finite-étale specializations;
  no theorem with this statement. The finite-unramified specialization assumes global
  finiteness and cannot replace this theorem about arbitrary separated morphisms.
- rg of the proposed declaration name in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no existing declaration.

Source checked: [Stacks Tag 04HI](https://stacks.math.columbia.edu/tag/04HI),
Lemma 41.17.2. The local `literature/stacks-project/etale.tex` is absent, so the
published tag was opened online. It agrees with the node; no correction, disputed
statement, new node or dependency module is needed. The proof docstring carries all
four DAG proof steps and their named inputs.

Validation: server scompile completed with exit code 0, 1.9 seconds, no errors or
warnings. Point binders and set carriers explicitly use `↥(pullback f g)` to avoid
Lean inferring a pullback in Type instead of the underlying points of a scheme.

## Second reading by F1

I independently opened the sandbox node and Lean module, all six statement-dependency
nodes, and their recorded declarations in the pinned Mathlib source. I read Stacks
`etale.tex`, section `section-unramified-etale-local`, the preceding lemma, and
`lemma-unramified-etale-local-technical` from the upstream raw TeX (the local file is
absent). The published [Tag 04HI](https://stacks.math.columbia.edu/tag/04HI) agrees.
The section imposes no additional standing assumptions. The node matches the source;
there is no `statement_change`, new definition node, or dependency module to review.

Object, hypothesis, and conclusion checklist, in the node's order:

1. Schemes X and S, and a scheme morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   PASS. `Scheme` is the locally affine locally ringed space of def-pc-scheme;
   its coercion to a type is its actual carrier, not geometric points.
2. Separatedness of f: `[IsSeparated f]`. PASS. I read `IsSeparated` in
   Morphisms/Separated.lean: its field is `IsClosedImmersion (pullback.diagonal f)`.
   This uses the separated component of def-weil-proper-morphism, not properness.
3. A point s, a finite list of n points with n nonnegative, all over s:
   `(s : S) (n : ℕ) (x : Fin n → X)` and `hx : ∀ i, f.base (x i) = s`.
   PASS. No injectivity or distinctness is assumed of the list.
4. Unramifiedness at each listed point: `hunramified : ∀ i, ∃ O : X.Opens,
   x i ∈ O ∧ LocallyOfFiniteType (O.ι ≫ f) ∧
   IsOpenImmersion (pullback.diagonal (O.ι ≫ f))`. PASS. This is exactly the
   conjunction recorded by def-weil-unramified-morphism, restricted to an open
   neighbourhood. I read the affine-local finite-type class and the open restriction
   declarations; no global finite-type assumption is introduced.
5. An étale neighbourhood and point over s: `∃ (U : Scheme.{u}) (g : U ⟶ S)
   (u : U), Etale g ∧ g.base u = s ∧ ...`. PASS. `Etale` is the recorded
   affine-local étale-ring-map class. Its `iff_flat_and_formallyUnramified`
   also gives the flat, unramified, locally finitely presented formulation of the
   dependency node. There is no unjustified residue-field isomorphism.
6. The actual fibre product X_U and its projections: `pullback f g`,
   `pullback.fst f g`, `pullback.snd f g`. PASS. I read their signatures in
   HasPullback.lean and the unconditional `HasPullbacks Scheme` instance in
   AlgebraicGeometry/Pullbacks.lean. No existence instance is added as a hypothesis.
7. Nonnegative m_i and open pieces W, V_ij: `m : Fin n → ℕ`,
   `W : (pullback f g).Opens`, and
   `V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens`. PASS. The dependent
   finite sum has exactly the requested index pairs. `Scheme.Opens.toScheme`
   in Restrict.lean is the restriction to the open subset; `.ι` is its actual
   inclusion. There are no arbitrary substitutes for these open subschemes.
8. Closedness of every piece: `IsClosed (W : Set ↥(pullback f g))` and
   `∀ a, IsClosed (V a : Set ↥(pullback f g))`. PASS. Openness is already carried
   by `Opens`. Thus these are exactly clopen subschemes of X_U.
9. Pairwise disjointness and covering: `Pairwise (fun a b ↦ Disjoint (V a) (V b))`,
   `∀ a, Disjoint W (V a)`, and `W ⊔ iSup V = ⊤`. PASS. In the lattice of
   opens these express disjoint subsets whose union is the whole space. Their
   open restrictions consequently express the specified disjoint union decomposition;
   no additional choice of a categorical coproduct is required by this node.
10. Clause (1), closed immersions to U passing through u:
    `∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f g) ∧
    u ∈ Set.range (((V a).ι ≫ pullback.snd f g).base)`. PASS. I read
    `IsClosedImmersion`: closed embedding and surjective stalk maps, exactly the
    dependency's notion. The range is the underlying topological image, as intended.
11. Clause (2), no point in W over u maps to a listed point:
    `∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p = u →
    ∀ i, (pullback.fst f g).base p ≠ x i`. PASS. The carrier is explicitly that
    of the scheme pullback; quantification is over all its topological points.
12. In particular, the exhaustive-fibre implication:
    `(∀ y : X, f.base y = s ↔ ∃ i, y = x i) →
    ∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p ≠ u`.
    PASS. The antecedent is precisely equality of the original fibre with the listed
    finite set, and the conclusion is precisely emptiness of W's fibre at u.
    The same witnesses U, u, m, W, V serve this clause. No witness is reselected.

Edge cases: n = 0 makes the dependent V index empty, permits W = top, and makes
all listed-point exclusions vacuous. The last clause then has exactly the empty
original fibre as its antecedent. Individual m_i = 0 are allowed. Repetitions
in x are allowed (indices with zero pieces can handle repetitions); no hidden
nonemptiness or distinctness constraint appears. Empty X is allowed; s rules out
empty S and u rules out an empty neighbourhood, as in the source. There is no
characteristic, field, Noetherian, quasi-compactness, or global finiteness binder.
The single arbitrary universe u is the standard Mathlib scheme universe for the
whole morphism diagram; no smaller test-scheme universe or bounded family is used.
Every variable in the signature is explicitly bound; the term u is the chosen
point, whereas the dotted universe notation `Scheme.{u}` names the universe.

Independent searches, with wording different from the first reading:

- LeanFinder via msearch: `clopen partition of a scheme after etale base change at
  unramified points`. Eight hits, including general étale APIs and the finite-algebra
  idempotent splitting theorem; none has this scheme statement.
- Loogle via msearch: `AlgebraicGeometry.IsSeparated, AlgebraicGeometry.IsClosedImmersion`.
  Nine hits, all diagonal, cancellation, and separatedness APIs; none is the decomposition.
  An earlier unqualified query was rejected for unknown `IsSeparated`; it was rerun
  with fully qualified identifiers, so its empty output was not used as evidence.
- msearch grep: `clopen|decomposition|unramified_at` returned general topology and
  unrelated decompositions. Targeted local rg in pinned Mathlib's Etale,
  FormallyUnramified, QuasiFinite, Finite, and Separated files for
  `partition|decompos|neighbou|04HI` found no matching theorem.
- Local rg in WeilConjectures and the project's lean/Sheaf for `04HI`,
  `closed.?immersion.*(split|decomp)`, `unramified.*(partition|neighbou|local)`,
  and `clopen.*(etale|étale)` found related files. I opened
  `WeilConjectures/AlgebraicGeometry/Morphisms/Finite/SplitNeighborhood.lean`:
  its SplitNbhd concerns finite morphisms and geometric points over a separably
  closed field, not these arbitrary separated morphisms and topological points.
  I also opened `Sheaf/AlgebraicGeometry/FiniteUnramifiedEtaleLocal.lean`:
  it assumes global `IsFinite f` and global unramifiedness and has no remainder.
  Neither is usable as an existing declaration for this item.
- LeanSearch via msearch was unavailable (Internal Server Error), recorded as
  unavailable rather than a negative search result. LeanFinder, qualified Loogle,
  and direct source searches supplied the independent checks.

H5/H6/H8/H9: there are no definitions, hollow data, auxiliary lemmas, or proofs
other than the single named theorem's `sorry`. The module and theorem docstrings
name Tag 04HI and the exact blueprint id. The proof docstring follows all four
node proof steps: finite pieces and stability, shrinking to closed immersions,
properness and closed intersections, then removal of intersection images and
clopen complement. Imports provide the three used APIs: étale morphisms,
separated/closed immersions, and scheme pullbacks. All lines are at most 100
characters. I mechanically checked `lean.statement` is verbatim equal to the
file signature, and checked bound variables by eye.

Mismatches and repairs: none. The mathematical statement and module are preserved;
only this independent second-reading section is added. The first compile invocation
used a repository-relative path for the sandbox-only module; I corrected the invocation
 to the absolute sandbox path, without changing any tool or source.

Validation: the absolute-path scompile invocation completed with exit code 0 in
1.9 seconds, with no errors or warnings printed. No module change was needed.
