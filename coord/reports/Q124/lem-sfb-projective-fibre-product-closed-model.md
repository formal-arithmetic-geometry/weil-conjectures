## Worker report

Item: lem-sfb-projective-fibre-product-closed-model. The module is
`Sheaf.AlgebraicGeometry.ProjectiveFibreProductClosedModel`.
Its theorem `AlgebraicGeometry.projectiveFibreProductClosedModel` has proof `sorry`.
The auxiliary definition `AlgebraicGeometry.projectiveFibreProductComparison` constructs
exactly the canonical comparison named in the statement, using `WidePullback.lift`.
It contains real data: the base map is `WidePullback.base q ≫ f`, the components are
`WidePullback.π q`, and their compatibility follows by associativity and
`WidePullback.π_arrow`. It makes no existence choice and introduces no separate notion.

Hypothesis and clause correspondence (Lean writes composition from left to right):

- The field is `(k : Type u) [Field k]`; the base S is literally `Spec (.of k)`.
  `X : Scheme.{u}` and `f : X ⟶ Spec (.of k)` introduce the scheme and its structure map.
  `[IsSeparated f]` is the closed-diagonal hypothesis, not absolute separatedness of X.
- The finite nonempty set is `(I : Type u) [Fintype I] [Nonempty I]`.
  `Fintype` supplies an enumeration so that the finite wide-pullback category is a
  `FinCategory`; this is available on every finite set, without a mathematical
  restriction. The index universe equals the scheme universe and does not introduce a
  small-index restriction. `(n : ℕ)` is precisely n >= 0.
- `(Y : I → Scheme.{u}) (q : ∀ i : I, Y i ⟶ X)` are the given schemes and maps.
  `(e : ∀ i : I, Y i ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)))` gives their embeddings.
  `he` asserts every e_i is closed. `he_over` gives exactly
  `e i ≫ projection = q i ≫ f`; it imposes no additional property on q_i.
- P is `widePullback X Y q`. Its projections are `WidePullback.π q` and its common
  structure map r is `WidePullback.base q`. This is the limit of the wide cospan of
  the q_i, hence the finite fibre product built from the recorded fibre-product notion.
  The corresponding product over S is `widePullback S Y (fun i ↦ q i ≫ f)`.
- The first conjunct is closedness of `projectiveFibreProductComparison f Y q`,
  the map with precisely these projections, rather than an arbitrary map to that product.
- Throughout the theorem N is expanded as `(n + 1) ^ Nat.card I - 1`.
  Every projective ambient space has coordinate type
  `ULift.{u} (Fin ((n + 1) ^ Nat.card I - 1 + 1))`, thus exactly N+1 coordinates.
  The `∃ eP` conjunct asserts a closed immersion P into P^N_S and its equality over S.
- The next conjuncts assert `IsHProjective (r ≫ f)`, `IsProper (r ≫ f)`,
  `LocallyOfFiniteType (r ≫ f)`, and `QuasiCompact (r ≫ f)`.
  The final two predicates together are finite type in the recorded convention.
  `IsLocallyNoetherian P ∧ CompactSpace P` is exactly the specified Noetherianity.
- The last main conjunct universally quantifies over any scheme T, any map
  `c : T ⟶ P`, and the premise `IsClosedImmersion c`. In this conjunct the node's
  new q is expanded everywhere as `c ≫ WidePullback.base q` (where the Lean binder q
  still denotes the original family q_i).
- `∃ eT` and `∃ dT` give closed immersions into P^N_S and P^N_X, respectively.
  Their factorization equalities say their projections are `(c ≫ r) ≫ f` and `c ≫ r`.
  They use the same N as eP, with no increase in the dimension bound.
- The following eight morphism-property conjuncts give finite-space projectivity,
  properness and finite type for both `T → S` and `T → X`. Together with the P
  conjuncts, these are exactly all three maps named by the node.
- `IsLocallyNoetherian T ∧ CompactSpace T` gives both parts of Noetherianity of T.
- The final implication has premise
  `∃ V : X.Opens, Dense (V : Set X) ∧ IsIso (pullback.snd (c ≫ r) V.ι)`.
  Here the second pullback projection is precisely the restricted morphism
  `q⁻¹(V) → V`. Its conclusion `Surjective (c ≫ r)` is the node's surjectivity.
  There is no dense-open premise on the other conclusions.
- There are no integrality, group-action, finite-type or Noetherian hypotheses on X,
  and no nonemptiness hypothesis on T or P.

Dependency declarations read and used:

| Node | Module | Declaration / use |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs | `Field` |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | `Scheme`, `Scheme.Hom` |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | `IsProper`, `IsSeparated` |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | `IsClosedImmersion` |
| def-kun-projective | WeilConjectures.AlgebraicGeometry.Morphisms.Projective | `IsHProjective` |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | `pullback`, `pullback.snd` |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | `LocallyOfFiniteType`, `QuasiCompact` |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | `IsLocallyNoetherian` |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | the canonical open-subscheme inclusion `V.ι` |
| def-weil-surjective-morphism | Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap | `Surjective` |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | `Spec` |
| def-weil-pbc-quasi-compact-scheme | Mathlib.Topology.Defs.Filter | `CompactSpace` |

The finite extension of binary fibre products is Mathlib's
`CategoryTheory.Limits.widePullback`, `WidePullback.base`, `WidePullback.π`,
`WidePullback.lift`, and `WidePullback.π_arrow`, in
`Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks`. No alternative fibre-product notion
is defined. Relative projective spaces are the canonical `AlgebraicGeometry.ProjectiveSpace`
from `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, as used by the recorded
`IsHProjective`. Their dimension is number of homogeneous coordinates minus one.

Proof dependencies: the modules of `lem-chow-segre` and
`lemma-nagata-projective-space-base-change-pullback` are imported through
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product` (which exposes the canonical
base-change module). `lem-kun-projective-implies-proper` is imported as
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` and its declaration
`AlgebraicGeometry.hProjective_properness` was read. The remaining proof nodes are
Mathlib matches: separated comparison in Morphisms.Separated, closed-immersion base change
and composition in Morphisms.ClosedImmersion, Noetherian ring definitions in
RingTheory.Noetherian.Defs, and finite type over a Noetherian scheme in
AlgebraicGeometry.Noetherian / Morphisms.QuasiCompact. These are available through the
imports. The docstring includes all seven proof steps, their source tags and node names.

Source check: read the local Stacks sources at Tag 01WD (binary Segre embedding),
Tag 01KR (comparison after a separated map), Tag 0C4Q (closed-graph proof of projective
permanence), and Tag 01T6 (finite type over a Noetherian base). Read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md` for the ancestor context.

Edge cases checked before writing:

- A singleton I gives N=n and the comparison is an isomorphism; the statement specializes
  to the given closed immersion and its closed subschemes.
- n=0 gives N=0 for every allowed I; none of the formulae divides or requires n>0.
- Empty T is permitted and satisfies the absolute/relative embedding, projectivity,
  properness, finite type, and Noetherian conclusions. If X is nonempty it cannot satisfy
  the final dense-open isomorphism premise; if X is empty surjectivity is vacuous.
- P or a factor Y_i may be empty. No nonempty hypotheses exclude them.
- The empty index set is deliberately excluded by the node. Allowing it would make
  P=X and would incorrectly force arbitrary separated X to embed in P^0 over k.
- Non-Noetherian, non-finite-type, disconnected or nonreduced X is allowed.
  Separatedness suffices for the graph argument; Noetherianity is concluded only for P,T.
- k may have any characteristic. ULift keeps finite homogeneous coordinates in the
  same universe as the schemes. There are no auto-bound variables or universes.

Searches for existing statements (all against the prescribed read-only sources):

1. `msearch.py ... leanfinder` with
   "Finite fibre products over a separated scheme of closed subschemes of projective
   space embed in projective space and are proper Noetherian": 8 hits, chiefly
   `Proj.isSeparated`, `Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat`, and
   properness of finite morphisms/pullbacks. None states this finite-product result,
   exact dimension bound, the closed-model clauses, or dense-open surjectivity.
2. `msearch.py ... loogle` with `"AlgebraicGeometry", "IsHProjective"`: 0 hits.
3. `msearch.py ... grep` with `widePullback|projective.*[Ff]ibre|closed.model` restricted
   to AlgebraicGeometry: 0 hits.
4. `rg -n 'lem-sfb-projective-fibre-product-closed-model|widePullback|projectiveFibreProduct'`
   on `lean/WeilConjectures` and `lean/Sheaf`: no exact item or theorem match; generic
   wide-pullback utilities exist upstream but do not change the base.
5. `rg` for `projective.*(fibre|fiber)|[Ff]ibre.*projective|projectiveFibreProductClosedModel`
   on the same two trees found other fibre results, not this theorem.
6. `rg` of the item in `dag/lean_names_upstream.json` found no declaration.
   The source modules ProjectiveSpace.Product and ProjectiveSpace.Segre give only the
   existing Segre/product embedding infrastructure, not this node's combined statement.

Validation: `scompile.py Q124 lem-sfb-projective-fibre-product-closed-model` compiled both
sandbox and library module successfully (15.6s and 1.7s), without errors or other warnings.
One elaboration repair was needed: `Fintype` instead of `Finite` for the large-universe
finite wide-pullback shape, plus an explicit Scheme type annotation for P under
`CompactSpace`, preventing the elaborator from interpreting the limit as a limit of types.
No node correction, new node, unusable dependency, or disputed statement was found.

## Second reading by Q124

This is a second pass by the sole dispatched worker; the maintainer provides the independent
review. I re-opened the node and the final file and checked the complete binder list and
conjunction against the prose. The field/base/separatedness, finite nonempty index set,
n>=0, component closed embeddings and their over-S equalities all match. The only
auxiliary definition is the canonical comparison with the required components. All three
ambient embeddings use exactly N+1 coordinates. The conclusion quantifies over every
closed c, states both structural equalities for T, gives projectivity/properness/finite type
for the three specified maps, and spells Noetherianity as local Noetherianity plus
compactness of P and T. The restricted morphism in the final dense-open implication is
the second pullback projection to V, not the first projection to T. Empty T and n=0
remain covered. No mathematical mismatch or node change was needed. The elaboration
repair described above changes only how the finite set and underlying space are presented.
