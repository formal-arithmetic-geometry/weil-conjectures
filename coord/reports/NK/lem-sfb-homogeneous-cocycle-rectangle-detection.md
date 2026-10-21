## Worker report

The module `Sheaf.RepresentationTheory.HomogeneousCocycleRectangleDetection` states
`Representation.homogeneous_cocycle_rectangle_detection`, with its only proof
`sorry`. It constructs no auxiliary notions. Its declaration docstring reproduces
all nine proof steps of the current, reviewed stage-1 node, including the
augmentation, the degree bound on the ordered-join contraction, equivariance,
uniform finite formulas, and continuity of the primitive.

I read the current node, both statement-dependency nodes and their recorded
Mathlib declarations, all proof steps, the free-module proof dependency, and
paragraph (3) of the main-20261015 direct-images proof. That paragraph does not
prove this agent-written arithmetic expansion; the source's WANTED reference is
retained in the module docstrings. The existing stage-1 split/review is preserved.
Only the item's `lean` field changes. No new nodes, dependency modules, statement
correction, or disputed statement is needed.

Each hypothesis and conclusion is rendered as follows:

| Node text | Lean |
| --- | --- |
| K a field | `(K : Type u) [Field K]` |
| Topology with continuous addition, negation, multiplication | `[TopologicalSpace K] [IsTopologicalRing K]`; the class extends `ContinuousAdd`, `ContinuousMul`, `ContinuousNeg`, without continuity of field inversion |
| G a topological group | `(G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]` |
| M a K-vector space | `(M : Type w) [AddCommGroup M] [Module K M]` |
| Continuous addition and negation on M | `[TopologicalSpace M] [IsTopologicalAddGroup M]` |
| Continuous scalar multiplication | `[ContinuousSMul K M]`, joint continuity on `K × M` |
| K-linear left G-action | `(ρ : G →* (M ≃ₗ[K] M))`; the homomorphism law is precisely the left-action composition law, with every group element acting linearly and invertibly |
| Continuous G-action | `hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2)`; joint continuity, with no topology on an automorphism group assumed |
| n at least one | `(n : ℕ) (hn : 1 ≤ n)` |
| Open subgroup H with its induced topology | `(H : OpenSubgroup G)`; its carrier is a subtype with the recorded `instTopologicalSpaceSubtype` |
| Chosen a_0,...,a_n | `(a : Fin (n + 1) → G)` |
| Continuous f on G^(n+1) | `(f : C(Fin (n + 1) → G, M))`, using the finite product topology |
| Diagonal equivariance | `hequiv : ∀ g x, f (fun i ↦ g * x i) = ρ g (f x)` |
| Homogeneous cocycle | `hcocycle` quantifies over `Fin (n + 2) → G` and sums `(-1 : ℤ) ^ i.val • f (fun j ↦ x (i.succAbove j))`, equal to zero |
| Zero on the ordered rectangle H a_0 × ... × H a_n | `hrectangle : ∀ x : Fin (n + 1) → H, f (fun i ↦ (x i : G) * a i) = 0` |
| Continuous t on H^n | `∃ t : C(Fin n → H, M)` |
| Diagonal H-equivariance of t | First conjunct: `∀ g x, t (fun i ↦ g * x i) = ρ (g : G) (t x)` |
| Restriction of f equals delta t | Second conjunct: for every `x : Fin (n + 1) → H`, `f (fun i ↦ (x i : G))` equals the sum of `(-1 : ℤ) ^ i.val • t (fun j ↦ x (i.succAbove j))` |
| Actual cochains; no closure or completeness | The existential supplies an actual continuous function with pointwise equalities; no quotient, closure, completion, Hausdorffness, or completeness hypothesis appears |

`Fin.succAbove i` is the order-preserving inclusion skipping `i`, so both sums
have exactly the omitted coordinates, in the original order. Integer scalar
multiplication gives the alternating signs in every characteristic.

Dependency declarations used:

- `def-weil-field`: its `mathlib_match` is `Field`, read at
  `Mathlib.Algebra.Field.Defs`, line 180 and the preceding docstring. A field
  includes a nontrivial commutative ring with inverses of nonzero elements.
- `def-kun-subspace-topology`: `instTopologicalSpaceSubtype`, read at
  `Mathlib.Topology.Defs.Induced`, lines 60–78; it is the topology induced by
  inclusion. This is the topology on the open subgroup carrier, not a separately
  supplied topology. Its recorded module is publicly imported.
- Proof dependency `def-weil-pbc-free-module`: `Module.Free`, read at
  `Mathlib.LinearAlgebra.FreeModule.Basic`, lines 18–44; its module is imported
  privately as the stage-3 proof plan requires.
- Proof dependency `lem-sfb-ordered-join-partial-contraction` has no recorded Lean
  declaration on the read base. Its proof use is described in full in the
  docstring; no duplicate declaration is introduced. Its eventual proof import
  remains for the maintainer once that node is stated.

Edge cases checked before drafting: `n = 1` gives a primitive on H and the
boundary `t(h_1) - t(h_0)`. Degree zero is excluded exactly by `hn`, as in the
node. H can be the whole group or the trivial group when it is open; it is
nonempty because it is a subgroup. Coincident translates, repeated coordinates,
and equal a_i are not excluded. The zero vector space, characteristic two and
positive characteristic are allowed. No separation, local compactness,
finite-dimensionality, or completeness is imposed on any topology. Independent
universes `u v w` cover the field, group and module without an extra size equality.

Searches performed with `msearch.py` (the exact responses are retained in
`searches.jsonl` in the sandbox):

- LeanFinder: `A continuous homogeneous group cocycle vanishing on a product of
  subgroup cosets restricts to a continuous equivariant coboundary` returned
  eight low-degree algebraic coboundary facts, no rectangle theorem.
- Loogle: `"homogeneousCochains"` returned twelve results, including
  `TopRep.homogeneousCochains` and its differential. I read
  `Mathlib.RepresentationTheory.Homological.ContCohomology.Basic`: these cochains
  use iterated continuous-map spaces and invariants, not a theorem detecting
  vanishing on a rectangle. They supply no statement matching this node.
- LeanSearch: `Continuous homogeneous group cocycle vanishes on subgroup coset
  rectangle implies continuous equivariant coboundary on subgroup` returned
  eight low-degree cocycle/coboundary predicates and their quotient facts.
  I read `groupCohomology.IsCoboundary₁` and `IsCoboundary₂` in the low-degree
  source: they concern algebraic inhomogeneous cochains, not this assertion.
- Mathlib grep, subdirectory `RepresentationTheory`, query
  `(rectang|coset).*(cocycle|coboundary)|(cocycle|coboundary).*(rectang|coset)`:
  zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for rectangle/cocycle
  combinations, the intended name and the blueprint id found only the
  consumer's proof docstring in `LocalNormAlgclCocycleDescent`. The required
  `grep -rn` for the item id in `lean/WeilConjectures` found none. The source's
  homogeneous/inhomogeneous comparison modules give coordinate descriptions,
  not rectangle detection. The new declaration name is absent from
  `dag/lean_names_upstream.json` and both source roots.

The previous retry had no Lean module or changed node in this sandbox. The
present delivery supplies the missing theorem and its complete `lean` record,
so the stage-1 node is no longer submitted unchanged.

Validation: compilation and the required dry run are performed with the
prescribed wrappers; results are recorded below after they finish.

The direct `scompile.py` check passed with no errors or warnings: sandbox mode
7.4 seconds, library mode 17.6 seconds. The recorded signature was extracted
verbatim from the module. Comparing the node JSON with the read base reports
exactly one changed field, `lean`; the module has no line over 100 characters
and uses `set_option autoImplicit false` with all three universes explicit.

`deliver2.py NK lem-sfb-homogeneous-cocycle-rectangle-detection --no-push`
returned `OK (dry run)`: commit `18b51ed1419` passed the server preflight and
compiled. The packet contains exactly the module, item node, and worker report.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
