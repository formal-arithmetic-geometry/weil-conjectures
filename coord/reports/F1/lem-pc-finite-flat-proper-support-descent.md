## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FiniteFlatProperSupportDescent.lean` states
`AlgebraicGeometry.finite_flat_proper_support_descent`. It introduces no definition and
leaves exactly this theorem's proof as `sorry`. The node is unchanged except for `lean`;
there are no new nodes, dependency modules, statement corrections or disputed statements.

Hypothesis and conclusion correspondence:

- Directed set: `{I : Type u} [PartialOrder I] [IsDirectedOrder I]`. The chosen `i : I`
  already ensures nonemptiness; no redundant `Nonempty I` hypothesis is imposed.
- Inverse system of affine schemes with Noetherian coordinate rings:
  `R : I ⥤ CommRingCat.{u}` and `[∀ k : I, IsNoetherianRing (R.obj k)]`.
  Contravariance gives `R.op ⋙ Scheme.Spec`. Its schemes are exactly `Spec (R.obj k)`;
  all are quasi-compact and quasi-separated, and their transition maps are affine.
  These are consequences of being spectra, rather than additional assumptions.
- Limit `S = lim S_i = Spec R`: `(c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c)
  [IsAffine c.pt]`. An affine cone point allows any chosen spectrum presentation of S;
  no particular coordinate-ring isomorphism is fixed. The cone supplies the compatible
  structure maps `c.π.app (op k)`. Index and ring/scheme universes agree.
- Finitely presented `S_i`-scheme `X_i`: `{Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))`
  with `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`, precisely
  the finite-presentation convention of `def-pc-morphism-conventions`.
- `X = X_i ×_{S_i} S`: `pullback f (c.π.app (op i))`; its morphism to S is
  `pullback.snd f (c.π.app (op i))`.
- Complex of O_X-modules: `G : CochainComplex (...).Modules ℤ`. Differentials and the
  relations that their consecutive composites vanish are part of the complex data.
- Boundedness: `hG_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n)`.
  This means bounded on both sides, including the zero complex.
- Finitely presented terms: `hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation`.
  Mathlib's definition is local finite presentation by free module sheaves; it already
  implies `IsQuasicoherent` and `IsFiniteType` (Quasicoherent.lean:280-289), so no independent
  quasi-coherence assumption is added.
- Flatness over S: `hG_flat : ∀ n, (G.X n).IsFlatOver (pullback.snd ...)`, using the
  source project's affine-local relative module-flatness predicate, not flatness of f.
- Every term has support proper over S: `hG_support : ∀ n,
  Scheme.Modules.HasSupportProperOver (pullback.snd ...) (G.X n)`. The predicate asserts
  closedness of the exact nonzero-stalk locus and properness of its reduced induced
  closed subscheme; it does not assume X itself proper.
- Later stage and its base-changed scheme: `∃ (j : I) (hij : i ≤ j)
  (Gj : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ)`.
  This is `j ≥ i` and `X_j = X_i ×_{S_i} S_j` with the correct direction of Spec.map.
- The first four conjuncts repeat boundedness, finite presentation, flatness over S_j,
  and proper support over S_j, term by term, with `Gj` and the projection to `Spec R_j`.
- Isomorphism of the base change with G: the existential family `e n` consists of
  isomorphisms from `(Scheme.Modules.moduleBaseChange f g).obj (Gj.X n)` to `G.X n`.
  Here `g` is `Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)` from S to S_j over S_i.
  The final `∀ n m` equation says these isomorphisms commute with every differential.
  This is exactly an isomorphism of the tensor-base-changed complexes, not merely
  isomorphic terms without compatibility. A family is used so no new map-of-complexes
  definition or preservation-of-zero theorem is required in stage 2.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, the
  locally ringed space definition with local affine charts and locally ringed space maps.
- `def-pc-morphism-conventions` is explicitly a convention node (`lean.convention = true`)
  with no single declaration. Its relevant Mathlib notions are
  `AlgebraicGeometry.LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`
  in Morphisms.FinitePresentation, Morphisms.QuasiCompact and Morphisms.QuasiSeparated.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`:
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`, whose full definition is
  `Scheme.Modules.tensorPullback (baseChangeMap f g)`. Scheme base changes use the
  recorded convention `CategoryTheory.Limits.pullback` and its projections.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `AlgebraicGeometry.Scheme.Modules.HasSupportProperOver`, using
  `Scheme.IsClosedSubsetProperOver` and the nonzero-stalk support locus.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`, with its full affine-open section
  flatness definition read at lines 186-197.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation`, read with its docstring and quasi-coherence
  and finite-type consequence instances. It is available through the imports above.

The two proof dependencies remain natural-language inputs: descend the flat bounded
complex with `lem-pc-flat-bounded-complex-descent`, then apply
`lem-pc-proper-support-descent` to finitely many nonzero terms and choose a common upper
bound. The full proof is in the theorem docstring. Neither proof lemma is assumed as a
binder, and no proof is supplied in this delivery.

Edge cases checked before writing: a zero complex permits any interval and empty support;
`a > b` forces all terms zero without inconsistency; an empty source scheme is allowed;
zero coordinate rings and hence empty stages and limit are allowed; a singleton directed
set allows `j = i`; an empty index set has no chosen i and hence no instance of this
statement; no condition on characteristic appears. Arbitrarily shifted finite intervals
are allowed, not only nonnegative degrees. Properness is only imposed on each support,
so nonproper ambient X is allowed. The final equation checks the actual differentials,
not just termwise isomorphism. All variables and the universe are explicitly bound.

Searches for existing statements (2026-10-11):

- `msearch.py ... leanfinder "descent of bounded finitely presented flat complexes of sheaves
  with proper support along inverse limits of affine schemes"`: eight hits, including
  `AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit`, the corresponding appTop results,
  and morphism flat descent. None states bounded-complex proper-support descent.
- `msearch.py ... loogle "SheafOfModules.IsFinitePresentation, AlgebraicGeometry.IsProper"`:
  zero hits.
- `msearch.py ... grep "proper.*support|support.*proper" AlgebraicGeometry`: one unrelated
  comment in Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:20; no theorem match.
- `msearch.py ... leansearch "descent of bounded flat finitely presented complexes with
  proper support over inverse limits of schemes"`: unavailable, Internal Server Error;
  no result or mathematical verdict inferred from the failure.
- `rg` of the node id and `proper.*support|support.*proper` in the source project's
  WeilConjectures: no id match and only unrelated proper/compact-support discussion,
  not this theorem. Source DirectImage supplies IsFlatOver.
- `rg` of proper/support and descent modules under this project's lean/Sheaf: found the
  dependency ClosedSubsetProperOverBase and sibling FlatBoundedComplexDescent, but no
  theorem combining descent with proper support. Read the sibling signature in full.
- `rg "finite_flat_proper_support_descent"` in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no match for the proposed declaration name.

Source checking: the local Stacks checkout is absent on this machine, so read the official
pages [01ZR](https://stacks.math.columbia.edu/tag/01ZR),
[05LY](https://stacks.math.columbia.edu/tag/05LY),
[081G](https://stacks.math.columbia.edu/tag/081G), and
[0CYS](https://stacks.math.columbia.edu/tag/0CYS). These give module/map descent,
eventual flatness, eventual proper scheme-theoretic support, and the equivalence between
proper support and proper scheme-theoretic support for finite-type quasi-coherent modules.
The node's combination uses precisely these inputs; no source-imposed extra hypothesis
is missing from its finitely presented affine setting.

Validation: `scompile.py F1 lem-pc-finite-flat-proper-support-descent` compiled the module
on the server in 3.8 seconds, exit 0, with no warnings.
`deliver2.py F1 lem-pc-finite-flat-proper-support-descent --no-push` printed OK: the
module compiles and passes preflight except for the independent second-reading section,
which the second reader supplies. Nothing was pushed.

## Second reading by F1

I independently read the item node, its two proof steps, the delivered module, all four
statement dependency nodes, and the dependency declarations. The statement below matches
the node after one binder repair; the natural-language node statement was not changed.

Source check: the local Stacks checkout is absent. I read the official .tex sources directly
from https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex and
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex, together with
https://stacks.math.columbia.edu/tag/01ZR, /tag/05LY, /tag/081G and /tag/0CYS.
The actual TeX labels are lemma-descend-modules-finite-presentation,
lemma-descend-module-flat-finite-presentation, lemma-eventually-proper-support and
lemma-module-support-proper-over-base. I also read lemma-descend-finite-presentation
(the assumptions inherited by 05LY) and situation-descent-property (inherited by 081G).
The former assumes affine transitions and qcqs stages; the latter additionally assumes
qcqs initial source and target schemes. Here the stages are affine and the source is
finitely presented over an affine stage, so those conditions follow. For 081G and 0CYS,
local finite type follows from local finite presentation and finite-type quasi-coherent
terms follow from module finite presentation. No extra source hypothesis is missing.
The node's reference to cohomology.tex denotes the Cohomology of Schemes chapter whose
current Stacks source file is coherent.tex.

Object/hypothesis/conclusion checklist, in the node's order:

1. Directed set I: `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
   PASS after repair. The original `[PartialOrder I] [IsDirectedOrder I]` unnecessarily
   required antisymmetry, contrary to STATE's DIRECTED SETS convention. Replaced both
   binders with the convention's preorder form. A chosen `i : I` supplies nonemptiness.
2. Affine inverse system with Noetherian coordinate rings: `R : I ⥤ CommRingCat.{u}`,
   `[∀ k : I, IsNoetherianRing (R.obj k)]`, and diagram `R.op ⋙ Scheme.Spec`.
   PASS: Spec reverses the ring maps; qcqs stages and affine transitions are automatic.
   This encodes every system with the spectrum presentations specified by the node.
3. Affine limit S with compatible maps to all stages: `(c : Cone (R.op ⋙ Scheme.Spec))`,
   `(hc : IsLimit c)`, `[IsAffine c.pt]`. PASS: the cone point is S, its components are
   the projections, and IsAffine gives the stated spectrum presentation without fixing
   a coordinate-ring isomorphism. No Noetherian condition is imposed on the limit.
4. Chosen stage and finitely presented scheme over it: `(i : I) {Xi : Scheme.{u}}`,
   `(f : Xi ⟶ Spec (R.obj i))`, `[LocallyOfFinitePresentation f] [QuasiCompact f]
   [QuasiSeparated f]`. PASS: precisely the convention node's finite presentation,
   with schemes and morphisms from `Mathlib.AlgebraicGeometry.Scheme`.
5. X and its projection to S: `pullback f (c.π.app (op i))` and `pullback.snd`.
   PASS: the fibre product and projection specified by def-pc-base-change.
6. Complex G of O_X-modules: `G : CochainComplex (...).Modules ℤ`.
   PASS: genuine complexes with their differentials and square-zero relations,
   not derived objects or complexes of abelian sheaves.
7. Boundedness: `hG_bounded : ∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (G.X n)`.
   PASS: termwise boundedness on both sides in arbitrary integer degrees.
8. Finitely presented terms: `hG_fp : ∀ n, (G.X n).IsFinitePresentation`.
   PASS: Mathlib's local finite presentations by finite free sheaves. I read
   SheafOfModules.IsFinitePresentation and its IsQuasicoherent/IsFiniteType instances
   in Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:268-289.
9. Terms flat over S: `hG_flat : ∀ n, (G.X n).IsFlatOver (pullback.snd ...)`.
   PASS: the source DirectImage.lean:186-197 defines relative module flatness through
   affine-open sections with restriction of scalars. It is not flatness of f or
   absolute flatness over O_X. For these quasi-coherent terms it is the usual notion.
10. Every term has support proper over S: `hG_support : ∀ n,
    Scheme.Modules.HasSupportProperOver (pullback.snd ...) (G.X n)`.
    PASS: I read ClosedSubsetProperOverBase.lean:30-56: the exact nonzero-stalk locus
    is closed and its reduced induced closed subscheme is proper over the base.
    This uses the dependency's two recorded predicates and does not require ambient
    X to be proper. The LocallyOfFiniteType instance is a consequence of f's binders.
11. Later stage j and scheme X_j: `∃ (j : I) (hij : i ≤ j)` and
    `pullback f (Spec.map (R.map (homOfLE hij)))`. PASS: the inequality and ring-map
    direction give the scheme map S_j → S_i and the required fibre product.
12. Descended bounded complex: `Gj : CochainComplex (...).Modules ℤ` and the first
    conjunct `∃ a b, ∀ n, n < a ∨ b < n → IsZero (Gj.X n)`.
    PASS: the same boundedness notion, with bounds allowed to change.
13. Descended finite presentation, relative flatness and proper support: the next
    three conjuncts quantify over all integer degrees, using Gj.X and the projection
    `pullback.snd f (Spec.map (R.map (homOfLE hij)))`. PASS: every property from the
    hypothesis survives, with base S_j rather than S and no added condition.
14. Base change is isomorphic to G: `∃ e : ∀ n, (moduleBaseChange f g).obj (Gj.X n)
    ≅ G.X n` followed by the differential equation for every n,m. PASS: I read
    BaseChangeConventions.moduleBaseChange, defined as tensorPullback (baseChangeMap f g),
    and TensorPullback's construction. The map g is `Over.homMk (c.π.app (op j))
    (c.w (homOfLE hij).op)` with T=S_j and T'=S over S_i. Thus the functor goes from
    modules on X_j to modules on X. The equation is F(d_j) ≫ e_m = e_n ≫ d_G;
    termwise inverses yield the inverse chain map. This is a complex isomorphism,
    not a quasi-isomorphism or merely a family of unrelated term isomorphisms.

Edge cases: an empty I admits no chosen i, so no assertion of an impossible stage is
made; a singleton allows j=i. Distinct mutually comparable indices are now allowed.
The zero complex and empty support are included, even when a>b; no nonempty scheme,
nonzero ring, separatedness of X over the base, characteristic, field, or domain
hypothesis is added. Degree 0 and negative degrees are treated uniformly. The common
universe u for I and schemes/rings follows the project's index-universe convention;
it is arbitrary. Every binder and universe is explicit, with no auto-implicit input.

Independent searches with different queries from the first worker:

- `msearch.py F1 lem-pc-finite-flat-proper-support-descent leanfinder
  "bounded cochain complex finite presentation relative flatness proper support descending
  to finite stage"`: eight results about derived truncation, resolutions and K-projectivity;
  none is this geometric descent theorem.
- Loogle `"CochainComplex, IsLimit"` first reported an unknown short identifier; repeated
  with `"CochainComplex, CategoryTheory.Limits.IsLimit"`: nine results on HomComplex
  cocycles and lifting, none about geometric descent.
- `msearch.py ... grep "proper.*support|support.*proper" AlgebraicGeometry`: only an
  unrelated Morphisms/Basic.lean comment.
- Independent rg of `complex.*descen|descen.*complex|support.*proper|proper.*support`
  in Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf found the existing proper
  support definition and weaker descent siblings, plus unrelated compact-support material.
  Read FlatBoundedComplexDescent's whole signature: it lacks the support hypothesis and
  support conclusion, so it does not state this item. Affine/ring perfect-complex descent
  has different objects and hypotheses. No duplicate found.
- Exact-name rg of finite_flat_proper_support_descent in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json returned no match.

There are no new definition nodes, delivered dependency modules, statement corrections,
or disputed statements to review. The only mathematical mismatch found was the stronger
index order binder; I changed it and refreshed lean.statement to the file's exact signature.
The worker report remains above as written; its old PartialOrder description is superseded
by this section. The already landed PartialOrder sibling is not rewritten: stage 3 may
pass to the posetal reflection before invoking it, or prove the preorder form directly
from the cited sources. The theorem docstring retains all node proof steps, source places
and blueprint marker. The module defines nothing, proves nothing, and leaves only its
named theorem as sorry; all imports serve the statement and all lines meet the width rule.

Validation after the binder repair: scompile.py with the sandbox module's absolute path
compiled cleanly on the server in 3.7 seconds (exit 0, no warnings). An initial call with
an unresolved relative path failed before compilation; using the absolute sandbox path
fixed the invocation. No repository git command was run directly by this reader.
