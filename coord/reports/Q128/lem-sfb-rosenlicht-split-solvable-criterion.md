## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RosenlichtSplitSolvableCriterion`
states `AlgebraicGeometry.exists_split_series_of_dense_splitTorus` with one `sorry`.
There are no new definitions, auxiliary theorems, or statement corrections.
The node changes only in its Lean record and the addition of the already-landed
`def-sfb-tori-multiplicative-type` to `stmt_deps` for its canonical `splitTorus`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`; there is no characteristic or perfectness binder.
- A group scheme over k is `G : Grp (Over (Spec (.of k)))`, using the recorded
  Mathlib group-object interface and its actual over-scheme structure map.
- Affineness and finite type are `hG : SolvableGroupStructure.IsAlgebraic G`.
  Its definition is exactly `IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧
  QuasiCompact G.X.hom`; finite type has both required parts.
- Smoothness is `[Smooth G.X.hom]` and geometric connectedness is
  `[GeometricallyConnected G.X.hom]`. The latter tests connectedness after all field
  extensions, including nonemptiness, rather than just connectedness over k.
- Group-scheme solvability is `hsolv : SolvableGroupStructure.IsSolvable G`.
  The recorded predicate uses a finite closed subnormal series and factorization
  of all commutators on every k-algebra. For affine finite type groups this is the
  equivalent commutative represented-fppf-quotient formulation explicitly stated
  by the dependency node. It is not abstract solvability of just k-rational points.
- The integer N ≥ 0 is `(N : ℕ)`. The source of `f` is the underlying over-scheme
  `(MultiplicativeType.splitTorus k N).X`, the existing recursively constructed
  N-fold product of the recorded multiplicative group, with the tensor unit at N = 0.
- `f : (MultiplicativeType.splitTorus k N).X ⟶ G.X` is only an over-scheme
  morphism. It has no `IsMonHom` binder and is not a morphism in `Grp`.
  `hf : DenseRange f.left.base` is density of its underlying topological image.
- The finite descending series is `∃ (m : ℕ) (S : Fin (m + 1) → Grp ...)`.
  `Nonempty (S 0 ≅ G)` identifies its first group with G and
  `Nonempty (S (Fin.last m) ≅ Grp.trivial _)` identifies its last group with 1.
  Isomorphisms are group-scheme isomorphisms over k, not bare scheme isomorphisms.
- Every term, including both endpoints, has
  `Smooth (S a).X.hom ∧ GeometricallyConnected (S a).X.hom`.
- Each adjacent inclusion is `j : S a.succ ⟶ S a.castSucc`, with
  `IsClosedSubgroupScheme j.hom.hom ∧ IsNormalSubgroupScheme j.hom.hom`.
  Each term is therefore a closed k-subgroup of G by composing the inclusions and
  the first endpoint isomorphism. Normality is required in its predecessor only.
- Each adjacent quotient has a representing group Q and homomorphism
  `q : S a.castSucc ⟶ Q`, with the recorded
  `SolvableGroupStructure.IsFppfQuotient j.hom.hom q`.
  This predicate requires flatness, surjectivity, local finite presentation and
  an isomorphism of the specified inclusion with the scheme-theoretic kernel.
- The quotient alternatives are `Nonempty (Q ≅ Grp.mk (StandardGroupSchemes.additive k))`
  or the corresponding `multiplicative k` isomorphism, in the category of group schemes.
- The final clause at each step is `SolvableGroupStructure.IsUnipotent G →
  Nonempty (Q ≅ Grp.mk (StandardGroupSchemes.additive k))`.
  Unipotence is precisely the dependency's smooth faithful finite-dimensional closed
  matrix representation, with nilpotence of every geometric matrix minus identity.
  Placing this implication inside the existential series is equivalent to the two
  clauses of the node: classically choose an additive-only series when G is unipotent,
  otherwise any split series. It does not require an additive series for a general G.
- For m = 0 there is one term and no `a : Fin m`, so no quotient is demanded.
  This allows the empty series for G = 1.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, and the group-scheme
  isomorphism category, used through `Grp (Over (Spec (.of k)))`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (underlying the geometric condition).
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (inside IsAlgebraic).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative`, `multiplicativeGroup`,
  `additive`, `additiveGroup`, using the specified Laurent and polynomial Hopf laws.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `IsAlgebraic`, `IsSolvable`, `IsUnipotent`, `IsFppfQuotient`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.splitTorus`.

The public imports expose the statement's declarations. The plain proof imports include
all currently recorded modules of proof dependencies, plus the modules in the Mathlib
matches for the field tensor-injectivity/flatness and faithful-flatness inputs.
Proof prerequisites without a current declaration are named in the complete eleven-step
docstring and remain future proof work. No missing proof prerequisite is assumed as a new
hypothesis. The proof docstring follows all eleven DAG steps, including arbitrary-field
multiplicative descent, the Laurent/Frobenius module argument, strong dimension induction,
the derived commutator word, multiplication by p, and elimination of multiplicative
quotients in the unipotent case.

Source checked directly: `literature/milne-algebraic-groups_iAG2017.pdf`, PDF page 357
(printed p.345), Theorem 16.58, including the statement that the dominant map is only a
map of schemes; printed pp.343--344 give the split convention and unipotent series.

Edge cases checked before writing: G = 1 and m = 0; N = 0 (a dominant point forces this
smooth geometrically connected affine group to be trivial); G_a and G_m; the mixed
G_a × G_m case; positive characteristic over imperfect fields; and smooth unipotent
forms not dominated by a split torus (the dominance hypothesis must not be omitted).
The empty scheme cannot be a group scheme over a field because of its identity section.
The common universe u is that of the field and the recorded scheme/group interfaces;
there is no independent smaller test-algebra universe. No edge case is excluded.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "A smooth connected solvable algebraic group dominated by a
  split torus is split solvable Rosenlicht"`: eight hits about abstract solvable groups,
  Lie solvability and Galois solvability; no group-scheme Rosenlicht theorem.
- `msearch.py ... loogle "IsSolvable, GrpObj"`: no hits; Loogle reported unknown
  identifier GrpObj. The source search below independently checked the actual interface.
- `msearch.py ... grep "Rosenlicht|[Ss]plit[Ss]olvable|split_solvable"`: two unrelated
  differential-algebra references to Rosenlicht, no algebraic-group theorem.
- `rg -n -i "rosenlicht|split.?solvable|splitSolvable"` across Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf`: found the existing split-solvable series
  predicate in `SplitSolvableTorsorDefinitions`, split-solvable torsor results and
  references in proof plans, but no dominant-torus criterion.
  The existing predicate is not redefined. The conclusion is written directly as a
  finite series, retaining geometric connectedness and the additive-only option.
- `rg -n "lem-sfb-rosenlicht-split-solvable-criterion" lean/WeilConjectures` and
  the name-index query for Rosenlicht/split-solvable: no existing exact declaration.
- Read `ToriMultiplicativeType` and `StandardGroupSchemes` rather than constructing a
  second torus or a second additive/multiplicative group.

No `STATEMENT-DISPUTED` flag or node fault was found. Validation: `scompile.py` compiled both sandbox and library module modes cleanly
(3.7 s and 1.7 s). `deliver2.py --no-push` returned OK: preflight and per-file
compilation passed. The JSON signature was checked verbatim against the module;
only `lean` and the permitted landed-torus addition to `stmt_deps` differ from the base.

## Second reading by Q128

I performed a separate second pass over the node and the completed signature; this is a
self-check, not a claim of an independent worker review. The dispatcher forbids starting
other agents; the maintainer supplies the independent review after delivery.

The signature preserves the affine/finite-type predicate, smoothness, geometric
connectedness, scheme-theoretic solvability and dense arbitrary over-scheme map.
I checked `f` is deliberately not bundled in `Grp`, all series terms are geometrically
connected, the quotients use the specified inclusions as their kernels, isomorphisms
respect group laws, and the unipotent condition applies to every quotient of the chosen
series. `Fin 0` makes the quotient conditions vacuous only for a genuinely trivial
series, whose endpoint isomorphisms force G = 1. No mismatch or statement change was
needed. The added torus dependency records an existing notion already used transitively
by the solvable-structure module.
