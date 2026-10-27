## Worker report

The module `Sheaf.AlgebraicTopology.CubicalBoundaryCoordinateProjections` states
`IntegralLatticeCubical.boundary_coordinate_projections`. Its only postponed proof is
that named theorem, whose docstring reproduces all eight steps of the node's proof.
The three new definitions have complete data: `resetCoordinate`,
`coordinateProjection`, and `coordinateProduct`. No statement correction, new node,
or dependency record repair is needed.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Integer rank r ≥ 0; ordered standard coordinates | `r : ℕ`; coordinate index `Fin r`, in its usual order. Index i represents the paper's i+1; this preserves the number of preceding directions and therefore every sign. |
| D = Z^r with its standard basis | `Fin r → ℤ`, with existing `unitVector r i = Pi.single i 1`. |
| Subsets I of cardinality a, integer degrees | Existing `Directions r a = {I : Finset (Fin r) // (I.card : ℤ) = a}`. |
| C_a free on pairs [v,I] | Existing `Chains r a = ((Fin r → ℤ) × Directions r a) →₀ ℤ`; existing `cell` is the indicated single basis vector. First conjunct states `Module.Free ℤ (Chains r a)`. |
| Zero terms outside 0 ≤ a ≤ r | The direction type is empty there; second conjunct states `Subsingleton (Chains r a)`, the literal zero module up to its unique isomorphism. All linear maps from or to these terms are consequently zero. |
| Alternating boundary with q_i(I) preceding indices | Existing `boundary` uses `(I.filter (fun j ↦ j < i)).card`, the sign `(-1 : ℤ)^q`, and the difference of the translated and original erased-direction cells. It extends by `Finsupp.linearCombination ℤ`. Third conjunct states its zero value for a ≤ 0; the same defining formula gives this because degree zero has only the empty subset and negative degrees have none. |
| rho_i(v) = v - v_i u_i | `resetCoordinate r i v = v - v i • unitVector r i`. |
| p_i kills cells containing i and otherwise resets the coordinate | `coordinateProjection` extends exactly these two basis cases by `Finsupp.linearCombination ℤ`; no arbitrary map is assumed. |
| epsilon sends every vertex to 1 | Existing `augmentation r`, the linear combination of the constant value 1. |
| s sends 1 to the origin vertex | Existing `sectionMap r`, `LinearMap.toSpanSingleton` on `cell r 0 0 ∅`. |
| Boundary squared zero in every integer degree | Fourth conjunct, `(boundary r (a - 1)).comp (boundary r a) = 0`. |
| epsilon boundary_1 = 0, hence augmented chain complex | Fifth conjunct, `(augmentation r).comp (boundary r 1) = 0`. Together with the previous equation these are precisely the module-chain-complex and augmentation conditions. No exactness or contraction hypothesis is introduced. |
| Each p_i commutes with boundary | Sixth conjunct, quantified over `i : Fin r` and `a : ℤ`, with the degree a-1 projection on the codomain. |
| The projections commute pairwise, including i=j | Seventh conjunct, quantified over both indices and every integer degree. |
| P_0 = 1 and P_k = p_1 ... p_k | `coordinateProduct` takes the first k indices from the ordered list `List.finRange r` and folds composition from the right with `LinearMap.id`; for k=0 its data is exactly the empty product. Values beyond r are harmless totalization and are not asserted to be additional projections. |
| Full product in degree zero equals s epsilon | Eighth conjunct `coordinateProduct r 0 r = (sectionMap r).comp (augmentation r)`. |
| Full product in every other integer degree is zero | Ninth conjunct, `∀ a : ℤ, a ≠ 0 → coordinateProduct r a r = 0`. |
| Translation [v,I] ↦ [v+w,I] | Existing `translate r a w`, with exactly this basis formula and free linear extension. |
| Translation commutes with boundary and preserves augmentation | Tenth and eleventh conjuncts give the displayed composition equalities. |
| Finite set of subsets of size a | Twelfth conjunct `Finite (Directions r a)`, also covering the empty set in out-of-range degrees. |
| Basis-preserving direct-sum isomorphism | Thirteenth conjunct gives `e : Chains r a ≃ₗ[ℤ] (Directions r a →₀ ((Fin r → ℤ) →₀ ℤ))`, and `e (single (v,I) 1) = single I (single v 1)`. The outer Finsupp is the direct sum of the free abelian groups on D. |
| Isomorphism intertwines translation with the regular action on every summand | The second property of e says `e (translate ... w x) I = Finsupp.mapDomain (fun v ↦ v + w) (e x I)`. This is the stated action on the canonical basis, which has one free orbit: the basis at v is uniquely the translate by v of the basis at zero. No action by arbitrary endomorphisms replaces this action. |
| Rank zero C_0 = Z with epsilon=s=1 under the identification | Last conjunct supplies a linear equivalence to Z with forward map `augmentation r` and inverse `sectionMap r`. Consequently those maps become identities in these coordinates. The preceding all-degree statements include the empty product and the vanishing of every other term. |

Dependency declarations read and used:

- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, read with its complete
  class signature and docstring, and `Module.free_iff_set`. These are the exact record
  of `def-weil-pbc-free-module`. `Finsupp.linearCombination` from
  `Mathlib.LinearAlgebra.Finsupp.LinearCombination` provides free linear extension.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology`, read with its surrounding variables, docstring and
  `HasHomology` condition; its underlying `ChainComplex` and
  `HomologicalComplex` use precisely square-zero adjacent linear maps. This is the
  recorded module of `def-weil-pbc-module-chain-complex-homology`. The statement
  requires no homology conclusion, so there is no need to evaluate `homology`.
- `Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction`: the existing
  `Directions`, `Chains`, `cell`, `unitVector`, `boundary`, `augmentation`,
  `sectionMap`, `translate` definitions, all read with their full signatures and
  docstrings. These actual constructions are reused instead of duplicated. Its
  `contraction` theorem is not invoked or assumed. It already owns those definitions
  under the parent node. Adding that parent as a DAG prerequisite would create a
  dependency cycle (the parent proof cites this item), so no parent prerequisite
  is added; this is reuse of its independently defined data only. In particular
  the maintainer must omit the reverse parent proof import under the import-cycle
  exception in stages/2-statements.md §3.7 unless those data are later factored out.

Edge cases were checked before writing: r=0 has one vertex, no projection indices,
and the identity empty product; a<0 and a>r have no cells; a=0 has no boundary
summands; at a=1 the augmentation of every edge difference is 1-1; at a=r the
next-degree group is zero; i=j causes no commutation exception; negative lattice
coordinates do not change the finite supports or resetting formula. There are
no auto-bound variables (`set_option autoImplicit false`) or universe constraints
excluding a lattice or degree. Since all lattice cell indices are fixed finite-rank
integer sets, their natural universe zero encoding loses no allowed object.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder "Integer cubical lattice chain boundary coordinate reset projections commute translation regular module decomposition"`: eight irrelevant cube-topology and composition-boundary hits; no exact statement.
- `msearch.py ... loogle "Finsupp.curryLinearEquiv, Finsupp.lsum"`: zero hits for that joint query. Reading the actual Finsupp sources separately confirmed the generic coefficient regrouping equivalence, which does not state the coordinate identities.
- `msearch.py ... grep "cubical|lattice.*boundary|coordinate.*projection" Algebra/Homology`: zero hits.
- `msearch.py ... leansearch "The cubical integer lattice chain boundary squares to zero and coordinate reset projections commute"`: eight hits, including alternating-face simplicial complexes and group bar homology; their cells and differentials differ, and none states the coordinate-reset result.
- `rg` over `lean/WeilConjectures` for `cubical`, `Cubical`, and the node id: no matching cubical lattice result. A private Galois-units `boundary_coordinates` lemma concerns different objects.
- `rg` over `lean/Sheaf` for those terms located the existing parent construction and its consumers. Reading the parent theorem confirmed it includes boundary/translation assertions but does not include coordinate-projection maps, their pairwise identities or ordered products. Therefore there is no exact existing declaration for the whole item. Searches for the newly introduced names found no clash in this namespace.
- Read the current blueprint `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), and the local Stacks source `more-algebra.tex` around `definition-koszul-complex`, including the preceding alternating differential. The detailed coordinate calculation is the node's agent-written extraction, as its source record already says.

Validation: scompile.py compiled this one module both under its sandbox and its
final library module name, in 1.9 s and 2.1 s respectively, with no errors or
unexpected warnings. Every definition has real data; nothing has been proved.
The node copy changes only `lean`, preserving its reviewed mathematical statement
and split verbatim. No STATEMENT-DISPUTED fault was found.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
