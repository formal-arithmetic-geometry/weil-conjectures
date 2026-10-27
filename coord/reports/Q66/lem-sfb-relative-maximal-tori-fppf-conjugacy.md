## Worker report

The module states `AlgebraicGeometry.relative_maximal_tori_fppf_conjugacy`, with one
`sorry` proof and no new definitions. The original node fields are unchanged except
for `lean`. The complete seven-step DAG proof, including its cited dependencies,
is included in the theorem docstring.

Source read: Brian Conrad, Reductive Group Schemes,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
proof of Theorem 3.2.6, printed pp.94--95 (the conjugacy argument after the explicit
reduction to an arbitrary smooth S-affine group); Proposition 2.1.2 and Corollary
2.1.5, printed pp.56--61. The parameter-scheme theorem's extra centralizer
hypothesis is not used in this conjugacy statement.

Clause-by-clause rendering:

- Any scheme S is `{S : Scheme.{u}}`; no Noetherian or nonemptiness assumption.
- A group scheme over S is `G : Grp (Over S)`, a bundled group object in S-schemes.
  Its structural arrow is `G.X.hom`. Smoothness and affineness are the instances
  `[Smooth G.X.hom]` and `[IsAffineHom G.X.hom]`.
- Finite presentation is explicitly the three instances
  `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` on that same
  structural arrow, as required by the scheme-conventions dependency.
- The two subgroup schemes are the family `T : Fin 2 → Grp (Over S)` and group
  morphisms `j : ∀ a, T a ⟶ G`. This is just T₀ and T₁ indexed by 0 and 1;
  `[∀ a, IsClosedImmersion (j a).hom.hom.left]` expresses closed subgroup inclusion.
- `hT : ∀ a, IsRelativeTorus (T a).X` uses the dependency's exact definition:
  local splitting as group-valued functors on an fppf covering, with ranks depending
  on the cover member, including rank zero.
- `hmax` quantifies over both tori, every algebraically closed field Ω and every
  geometric point `s : Spec (.of Ω) ⟶ S`. The functor
  `(Over.pullback s).mapGrp` is the group-object base change, built from the chosen
  scheme fibre products. A competitor `H` is required to be a closed subgroup of
  that geometric fibre and to have group-valued functor isomorphic to the recorded
  `relativeSplitTorusFunctor (Spec (.of Ω)) r`, for some `r : ℕ`.
  For every factorization `f ≫ i = (Over.pullback s).mapGrp.map (j a)`, `IsIso f`
  says this inclusion into H is equality. As both arrows into G are closed
  immersions, such a factorization is itself a closed immersion; no homomorphic
  images or merely pointwise subgroup inclusions replace inclusion of subgroups.
  Representable group-functor isomorphism is equivalent to group-scheme isomorphism
  by the fully faithful group Yoneda embedding.
- The conclusion chooses `I`, S-schemes `U i`, and sections `g i : U i ⟶ G.X`.
  `Presieve.ofArrows ... ∈ Scheme.fppfPrecoverage S` says exactly that the arrows
  are jointly surjective, flat and locally finitely presented.
- For every `V : Over S` and `v : V ⟶ U i`, the two displayed `Set.range`s are equal.
  The first is the conjugated image of `Hom_S(V,T₀)`, via
  `(v ≫ g i) * (t ≫ (j 0).hom.hom) * (v ≫ g i)⁻¹`; the second is the image of
  `Hom_S(V,T₁)`. Giving V together with v is exactly giving a scheme over Uᵢ.
  Thus this is equality of subgroup functors on all Uᵢ-schemes. The canonical
  pullback adjunction identifies these Hom sets with points of the base changes.
  Closed immersions are monomorphisms, so equality of these functors is equality
  as closed subgroups, retaining the scheme structure.
- No reductivity, connectedness, reducedness, characteristic restriction, or
  Noetherian hypothesis appears. No fixed rank is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`;
  the scheme-conventions node is convention-only and has no module of its own.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.RelativeTorus`: `IsRelativeTorus`,
  `relativeSplitTorusFunctor`, including their complete docstrings and signatures.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology` (the statement uses covering families, hence precoverage).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; used through `Over.pullback` and `mapGrp`.
- Group Yoneda and its group-valued functor are from
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`; the slice product and pullback
  API is from `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`, both exported by
  the relative-torus dependency.

All recorded proof-dependency modules are imported without `public`. The transporter
and identity-subgroup proof nodes currently have no recorded module, so those two
imports are omitted. Mathlib leaves are imported from their recorded source files.

Edge cases checked before writing and on rereading:

- Empty S: the empty cover is allowed (`I : Type u` has no Nonempty assumption).
- Rank zero: the relative torus uses `r : ℕ`, including zero, and `hmax` tests rank
  zero competitors as well. The zero-fold product is the trivial group.
- Disconnected S and variable rank: no shared rank occurs for T₀ or T₁, or between
  cover members. Their ranks become equal where conjugacy requires it.
- Nonreduced base and test schemes: V is an arbitrary scheme; no field-valued or
  reduced-only testing occurs in the conclusion. Geometric testing occurs only
  in the maximality hypothesis, as in the node.
- Disconnected and nonreductive G: the hypotheses impose neither condition.
- Field characteristic: arbitrary; Ω is any algebraically closed field in the
  scheme universe. All universes and variables are bound explicitly.
- Identical tori/inclusions: conjugation by the identity section satisfies the
  conclusion. General inclusions are tested as scheme morphisms, not point sets.

Searches actually run:

- msearch LeanFinder: “Geometrically maximal relative tori in a smooth affine group
  scheme are locally conjugate for the fppf topology”; eight unrelated hits on
  affine transition limits and Galois categories, no matching theorem.
- msearch Loogle: `GrpObj, IsRelativeTorus`; no hits, unknown identifier `GrpObj`
  in the remote index (the local declaration was then read directly).
- msearch grep, AlgebraicGeometry: `maximal.*[Tt]or|[Tt]or.*conjug|conjug.*[Tt]or`;
  one unrelated hit in Modules/Sheaf.lean about conjugate equivalences.
- msearch LeanSearch: “Two maximal tori in a smooth affine group scheme are
  conjugate on a faithfully flat locally finitely presented cover”; eight hits on
  smoothness, flatness, affine covers and abstract Iwasawa groups; none exact.
- rg in the source `lean/WeilConjectures` for maximal torus/conjugacy terms and
  the node id: no matching group-scheme statement. The targeted name search in
  `dag/lean_names_upstream.json` and Mathlib also has no hit.
- rg in `lean/Sheaf`: found relative tori, field maximal-torus terminology, the
  classical field conjugacy theorem and split-torus matrix classification; read
  those sources. None states fppf local conjugacy over an arbitrary base.

No statement correction, disputed statement, new node or dependency repair is needed.
Compilation: required scompile.py passed both the sandbox and library compile of
the delivered module, with no compiler diagnostics (2026-10-24).

## Second reading by Q66

A separate sequential rereading of the node, source passage and full Lean file
checked both directions of each translation above; no other agent was started,
in accordance with the dispatch brief. The maintainer performs the independent
review. In particular, `Fin 2` supplies exactly two tori; `hmax` tests actual closed
split-torus supergroups in each geometric fibre, and asks that the factorization
be an isomorphism. It does not merely test inclusions of Ω-rational points.
The conclusion's V,v range runs over the whole slice over Uᵢ; equality of image
sets on every test object is precisely subgroup-functor equality. Nilpotent tests
are retained. No assumption on G's connected component or centralizers leaked
from the stronger parameter-scheme theorem. No mismatch was found on this reading.
