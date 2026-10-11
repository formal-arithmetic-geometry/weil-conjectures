## Worker report

The module `Sheaf.AlgebraicGeometry.MixedCommutatorTangent` states
`AlgebraicGeometry.GeneralLinearGroup.mixedCommutator_tangent`, with its sole proof `sorry`.
No definitions, dependency modules, or new nodes are required. The node is unchanged except
for its `lean` record.

Hypotheses and clauses:

- A field k is `{k : Type u} [Field k]`.
- A finite-dimensional k-vector space V is `{V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]`. The arbitrary finite basis `b : Module.Basis n k V`, with
  `[Fintype n] [DecidableEq n]`, expresses endomorphisms as `LinearMap.toMatrix b b`.
  This is a coordinate choice, not a restriction to a special vector space: every V has
  such a basis, and the theorem works for any choice. GL(V) is expressed through its
  basis identification with `AlgebraicGeometry.GeneralLinearGroup n k`.
- The closed subgroup is `G : Over (Spec (.of k))`, `[GrpObj G]`, its inclusion `i`, and
  `[IsClosedSubgroupScheme i]`, using the dependency's exact recorded definition.
- `X Y : Module.End k V` are precisely the two endomorphisms. The points `x y` and
  equations `hx hy` witness membership of `1 + εX` and `1 + δY` in G's dual-number
  points. `dualUnit` includes the inverse `1 - εX`. Each separate parameter uses the
  same `DualNumber k`, as the two single-parameter rings are canonically identical.
- A is `DualNumber (DualNumber k)`: its four scalar coordinates are
  `inl (inl a)`, `inl (inr a)`, `inr (inl a)`, `inr (inr a)`. Accordingly epsilon is
  the inner nilpotent and delta the outer nilpotent. This is the full four-dimensional
  ring in the node, not a ring in which the mixed coefficient is killed.
- The existential G(A)-points `p q` and the first two equalities state both base changes,
  along `inlHom (DualNumber k) (DualNumber k)` and
  `DualNumber.mapRingHom (inlHom k k)`. These are the inner/outer inclusions respectively.
  Closed-subgroup injectivity makes these the unique base changes of x and y.
- The commutator belongs to G(A) because `p * q * p⁻¹ * q⁻¹` is itself a G(A)-point.
  The next equality gives exactly the four factors `1+εX`, `1+δY`, `1-εX`, `1-δY`
  as matrices, including the signs and order.
- The following equality gives `1+εδ(XY-YX)` using `(X * Y - Y * X)` in the endomorphism
  ring and the mixed scalar insertion `fun a ↦ inr (inr a)`.
- The hook arrow is `Function.Injective (DualNumber.mulRingHom (R := k))`; the existing
  homomorphism sends `a+ηb` to `inl(inl a)+inr(inr b)`, so sends η to εδ. It is also
  a k-algebra map: the formula fixes the scalar inclusions. We reuse its existing
  ring-hom packaging rather than define a duplicate algebra-map wrapper.
- The final existential point z and equality to `dualUnit` of the matrix of `XY-YX`
  state exactly `1+η(XY-YX) ∈ G(k[η]/η²)`.

Dependencies read and used:

- `def-sc-dual-numbers`: `Mathlib.Algebra.DualNumber`, `DualNumber` and `DualNumber.eps`
  (the dependency is Mathlib and has no lean record).
- `def-sc-group-scheme-subgroup`:
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`,
  `AlgebraicGeometry.IsClosedSubgroupScheme`, extending `IsSubgroupScheme` and `IsMonHom`.
- Existing supporting declarations (not new notions):
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`, `dualUnit`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`, `homMulEquiv`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie`, `AlgebraicGeometry.points`;
  `WeilConjectures.AlgebraicGeometry.DualNumbers`, `DualNumber.mapRingHom`,
  `DualNumber.mulRingHom`; Mathlib `TrivSqZeroExt.inlHom` and `LinearMap.toMatrix`.
  Their full declarations and docstrings were read. The two imports supply all of these.

Edge cases checked: the empty basis (V=0) is permitted; X=0, Y=0, and commuting X,Y
produce the identity commutator; characteristic 2 retains the same formula with the
usual characteristic-2 subtraction; no characteristic-zero, smoothness, reducedness,
algebraic-closedness, or positive-dimension hypothesis is introduced. Iterated dual
numbers retain all four independent coordinates even in characteristic 2. Objects and
rings share the scheme universe u as in the upstream point definitions; arbitrary u
is explicitly declared, with no auto-bound variables or file-local notation.

Searches:

- `msearch.py ... leanfinder "mixed commutator of infinitesimal matrix points in a closed
  subgroup scheme"`: eight unrelated special-linear/Geck-construction results; no match.
- `msearch.py ... loogle "DualNumber, Matrix.GeneralLinearGroup.map"`: zero hits.
- `msearch.py ... grep "mixed.*commutator|commutator.*dual" Algebra`: zero hits.
- `msearch.py ... leansearch "commutator of matrices over dual numbers"`: unavailable,
  Internal Server Error; no result or mathematical verdict inferred.
- `rg` over WeilConjectures for mixed/dual commutators found the general
  `GrpObj.commutator_mem_mixedPoints`, Lie bracket machinery, `dualUnit`, and closed-group
  Lie-range lemmas. None states all the node's matrix equality, base changes and descent.
  Searching the exact item id (also in `dag/lean_names_upstream.json`) found no declaration.
- `rg` over `lean/Sheaf` for dual numbers and commutators found tangent-space and
  dual-number scheme modules, no exact statement. Mathlib's dual-number, matrix and
  basis source files were opened to reuse their definitions.

Source reading: the local literature checkout has citation lists but no book or blueprint
text. Downloaded [Milne's 2017 book](https://www.jmilne.org/math/Books/iAG2017.pdf) into this
sandbox and read Chapter 10, especially 10.3 and 10.6–10.7 (pp. 187–189): endomorphism
commutators, infinitesimal points, and their matrix commutator interpretation. The node's
two-parameter expansion and coefficient descent are explicitly carried in the theorem
docstring, following its three proof steps. No statement correction or disputed claim.

Validation: server `scompile.py` compiled the module in 3.9 s with exit code 0 and no warnings.

## Second reading by R1

I independently opened the item node, both statement-dependency nodes, the sandbox module,
and the upstream declarations listed below. The source is Milne, not Stacks: I read the
sandbox's `milne.txt`, introduction conventions (pp. 3–4), Chapter 10 opening, Example
10.3, and 10.6–10.7 (pp. 187–189). The field is arbitrary; there is no smoothness,
algebraic-closedness or characteristic-zero assumption. The source's algebraic groups are
affine and finite type. These properties need no extra hypotheses here: a closed subgroup
of the finite-dimensional general linear group is affine and finite type over the field.
The iterated dual-number test algebra is commutative and finite-dimensional, hence meets
the source's finite-generation convention. The node gives the two-parameter version and
its coefficient-descent proof explicitly.

Object/hypothesis/conclusion checklist, with Lean rendering and verdict:

1. Field k: `{k : Type u} [Field k]`. Exact; arbitrary characteristic.
2. Finite-dimensional k-vector space V: `{V : Type v} [AddCommGroup V] [Module k V]
   `[FiniteDimensional k V]`. Exact after the universe repair below.
3. Coordinates for GL(V): `{n : Type u} [Fintype n] [DecidableEq n]`
   `(b : Module.Basis n k V)` and `LinearMap.toMatrix b b`. This is an arbitrary finite
   basis, not an additional mathematical constraint: any finite-dimensional V admits a
   basis indexed by `Fin (Module.finrank k V)`, even when V lives in a larger universe.
   `GeneralLinearGroup n k` is `Spec` of the matrix coordinate ring with determinant
   inverted (upstream GeneralLinear.lean, lines 40–72); `homMulEquiv` identifies its
   algebra-valued points with invertible matrices. Exact coordinate realization.
4. Closed subgroup G of GL(V): `(G : Over (Spec (.of k))) [GrpObj G]`, inclusion `i`,
   `[IsClosedSubgroupScheme i]`. I read Defs.lean lines 74–101: it extends the recorded
   `IsSubgroupScheme`, including `IsMonHom i` and injectivity on algebra-valued points,
   and requires `IsClosedImmersion i.left`. This is exactly the dependency node's
   closed-subgroup notion, without an extra geometric assumption.
5. Endomorphisms X,Y: `(X Y : Module.End k V)`. Their multiplication is composition;
   `LinearMap.toMatrix b b` respects its order, so `X * Y - Y * X` is XY minus YX. Exact.
6. Tangency hypotheses: `x y : points G (DualNumber k)` and `hx hy` identify their images
   with `dualUnit (LinearMap.toMatrix b b X/Y)`. I read `points` and `dualUnit`:
   the former is morphisms from Spec of the test algebra over k, and the latter is
   the unit with value `1 + X.map inr` and inverse `1 - X.map inr`. These witnesses
   express precisely membership of the two infinitesimal matrices. Universal binders
   for chosen witnesses and the node's membership hypotheses have the same content.
7. The algebra A and its four coordinates: `DualNumber (DualNumber k)`, whose carrier
   is the iterated `TrivSqZeroExt`. Its coordinates are the four copies of k; epsilon
   is inner `inl (inr 1)`, delta is outer `inr (inl 1)`, and their product is
   `inr (inr 1)`. The mixed coefficient survives. Exact, using def-sc-dual-numbers.
8. Base changes lie in G(A): existential `p q : points G A` and the first two image
   equations use `inlHom (DualNumber k) (DualNumber k)` and
   `DualNumber.mapRingHom (inlHom k k)`. I read their formulas: these send the original
   nilpotent to the inner and outer nilpotents respectively and fix k. The equations
   characterize the actual base changes uniquely because the closed-subgroup inclusion
   is injective on A-points; upstream `homMulEquiv_specMap_comp` gives naturality. Exact.
9. Commutator membership and four factors: `p * q * p⁻¹ * q⁻¹` has type `points G A`;
   its matrix is equated with the four displayed factors. The signs, order, and scalar
   insertions `inl (inr a)` / `inr (inl a)` match the node exactly.
10. Commutator value: the next equality is
    `1 + (LinearMap.toMatrix b b (X * Y - Y * X)).map (fun a ↦ inr (inr a))`.
    Exact coefficient, with no pure epsilon or delta term.
11. Injective eta map: `Function.Injective (DualNumber.mulRingHom (R := k))`.
    DualNumbers.lean lines 146–153 define it as
    `a + ηb ↦ inl (inl a) + inr (inr b)`. It is already a ring homomorphism, fixes k,
    and therefore is the stated k-algebra injection; no new wrapper is necessary.
12. Descended membership: existential `z : points G (DualNumber k)` with image
    `dualUnit (LinearMap.toMatrix b b (X * Y - Y * X))`. Exact final clause.

Edge cases: an empty n and the zero vector space are permitted (no `Nonempty n`);
all empty matrices are the unique invertible empty matrix. X=0, Y=0, and commuting
X,Y give the identity. Characteristic 2 is included: the same subtraction formula
works without dividing by 2. A nonempty-base group scheme cannot be the empty scheme,
so no possible closed subgroup is excluded by `GrpObj`. Both universes are explicitly
bound; the finite coordinate index and test rings use the scheme universe u, and the
vector space now has independent universe v. No index or positive-dimension restriction.

Independent searches, using different wording from the author:

- `msearch.py R1 lem-wf-mixed-commutator-tangent leanfinder
  "infinitesimal group elements bracket using two square zero parameters"`: eight hits,
  concerning manifold Lie algebras, Lie extensions, derivations and Jordan identities;
  none states this scheme-and-matrix assertion.
- `msearch.py ... loogle "DualNumber.mulRingHom"`: zero hits, unknown identifier in the
  search service. I opened the local upstream definition rather than infer its absence.
- `msearch.py ... grep "commutator.*infinitesimal|infinitesimal.*commutator" Algebra`:
  zero hits.
- `rg` on upstream WeilConjectures, Mathlib/Algebra and repository lean/Sheaf for
  `mixed.*commutator|commutator.*dual|dual.*commutator`, plus the exact theorem name:
  upstream GroupScheme/Lie has `commutator_mem_mixedPoints` and `mixedEquiv`;
  GeneralLinear/Lie has `toMatrixLieHom`. I opened these signatures. The first only
  gives membership in mixed points, and the latter is a bracket-compatible linear map;
  neither states the node's complete matrix expansion, base changes and descent.
  Mathlib's `DualNumber` and the existing ring maps are reused. The exact name and
  node-id searches in `dag/lean_names_upstream.json` find no attachment. No duplicate.

Mismatch repaired: the original binder `{k V n : Type u}` unnecessarily tied the vector
space's carrier universe to the field. I changed it to `{k n : Type u} {V : Type v}`,
added `v` to the universe declaration, and synchronized `lean.statement` verbatim.
No mathematical node statement changed. No new nodes or dependency modules were needed.
All other hypotheses and clauses were retained. There are no definitions or private
copies in the delivery; its sole theorem proof remains `sorry`. Both imports are used.
The source and blueprint docstrings are present; the theorem docstring follows all three
node proof steps (base change/subgroup closure, expansion, and coefficient descent).

Validation: the repaired module compiled through `scompile.py` in 5.0 seconds, exit code 0,
with no warnings. All variables and universes are bound and all Lean lines fit 100 columns.
