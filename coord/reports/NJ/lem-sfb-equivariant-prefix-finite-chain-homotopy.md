## Worker report

The module `Sheaf.RepresentationTheory.EquivariantPrefixFiniteChainHomotopy`
states `Algebra.equivariant_prefix_finite_chain_homotopy`, with its sole proof
`sorry`. Its owning helpers have real definitions: integral tuple chains,
augmented boundary, prefix insertion, diagonal translation, the recursive Q,
the uncollected finite formula list, and the coordinate-form predicate. All
are listed in `lean.declarations`; none is an independent auxiliary theorem.
The node's statement, dependencies, proof, and other fields are unchanged.

Indexing and objects:

- The natural index r is tuple length, namely paper degree q+1. Thus
  `prefixChains G (q+1)` is B_q and `prefixChains G 0` is B_{-1}.
  `Fin r → G` is the ordered tuple set, with repetitions allowed;
  `Finsupp.single x (1 : ℤ)` is its basis element.
- `Fin 0 → G` has exactly the empty tuple; its finitely supported integral
  functions identify canonically with Z. This does not require choosing an
  element of G. This is the augmented presentation of the complex; its extension
  below degree -1 has zero objects and zero outgoing boundary/prefix maps.
  Those lower zero terms impose no further identity. At length zero the
  boundary out to the zero group is zero, so the empty-tuple contracting
  identity is exactly the separate second conjunct of the theorem.
- `prefixBoundary` uses `powerSetComplexDifferential ℤ G` in positive
  degrees and `powerSetComplexAugmentation ℤ G` followed by the singleton
  embedding at the empty tuple for the augmentation. `prefixCone` uses the
  existing positive-degree `powerSetComplexHomotopy` and its augmentation
  homotopy, extended linearly from the empty tuple.
- `prefixTranslate` is linear pushforward of coordinatewise left multiplication,
  including the unique empty tuple, hence the trivial action at augmentation.

Hypothesis correspondence:

- `G`, `[Group G]`, `[TopologicalSpace G]`, `[IsTopologicalGroup G]` are the
  topological group, `H : Subgroup G` its subgroup, and `n : ℕ` includes n=0.
- `A : ∀ p : Fin (n+2), ... →ₗ[ℤ] ...` supplies precisely lengths 0 through
  n+1, i.e. degrees -1 through n. Additive homomorphisms between these abelian
  groups are equivalently Z-linear maps; no extra linearity assumption results.
- `haug : A 0 = LinearMap.id` is A_{-1}=1.
- `hchain` is d A_q=A_{q-1} d for all q=0,...,n; the successor index has
  explicitly displayed value p.val+1 and the castSucc index has value p.val.
- `hequiv` is A_p(hz)=h A_p(z), for all h in H and all chains, including the
  augmentation component.
- `b p` is the finite integer/map list `(k_{qj}, b_{qj})`; `hb` asserts the
  continuity of every map occurring in the list, and `hA` is its evaluation
  formula on every basis tuple. Finite index sets and finite lists are
  interchangeable by enumeration, including the empty index set. Lists retain
  repetitions and zero coefficients; no equality test on G is introduced.

Construction and conclusion correspondence:

- `prefixRecursiveQ G 0` is definitionally zero, giving Q_{-1}=0. Its successor
  branch forms `[x]-A[x]-Q_previous(d[x])`, prefixes `x 0` on this chain,
  and only then extends the basis assignment using `Finsupp.lift`.
  The argument contains exactly the finite initial segment of A it uses.
- The first conclusion conjunct asserts d squared zero, including augmentation
  after d from one-chains. The second is d C_b=1 on B_{-1}; the third is
  d C_b+C_b d=1 in every nonnegative degree. Together these are the claimed
  contracting identities on the augmented complex.
- The fourth conjunct is `h C_b z=C_(hb) (hz)` for every group element and all
  tuple lengths including zero; this is even the same universal h in G used
  by the prefix naturality clause, not an assumption on the A family.
- For each `p : Fin (n+1)`, the first inner conjunct writes the full formula
  for d Z_q(x)=0. The next asserts `LinearMap.id-A=boundary.comp Q +
  Q_previous.comp boundary`, so the identity holds on arbitrary chains.
- The next conjunct asserts Q(hz)=h Q(z) for every h in H and every chain.
- The next gives Q[x] as the evaluation of `prefixFormulaList` with fixed
  integer coefficients. The following conjunct asserts continuity of each
  map occurring in precisely that list.
- The actual `prefixFormulaList` constructor fixes the formulas, rather than
  merely postulating a finite expansion. Its successor branch concatenates
  `(1, x ↦ (x_0,x))`, the prefixed b terms with negative coefficients, and
  for each deletion position i the previous terms evaluated on the deleted
  subtuple and prefixed by x_0 with coefficient `-(-1)^i t`.
  Its length-zero list is empty. This uses only subtuple selection, the given
  b maps and prefixing an input coordinate. There is no equality comparison,
  coefficient collection, input-dependent choice, or coefficient topology.
- The final conjunct quantifies an arbitrary fixed family `a : ι → G` and
  fixed continuous `ρ : G → H`. `HasPrefixCoordinates H ρ a f` says each
  output coordinate is uniformly an input coordinate or `ρ(input)*a_i`.
  Assuming this for every b through the degree under consideration, it states
  the same condition for each map in that Q list. The finite family of a_i
  is not assumed nonempty, nor is rho required to be a homomorphism or retraction.
- Integrality and independence of eventual coefficients are visible in the
  definitions: all scalars are Z and no coefficient module, group, ring, or
  topology is a parameter of Q or its formula list.

Dependencies read and used:

- `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`, the recorded
  declaration of def-weil-pbc-free-module: a module has a basis indexed by
  a set, including the empty set. The concrete free models here use Finsupp
  and its free-module universal property, `Finsupp.lift`.
- `WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible`,
  `Algebra.powerSetComplexObject`, `powerSetComplexDifferential`,
  `powerSetComplexAugmentation`, `powerSetComplexHomotopy`,
  `powerSetComplexAugmentationHomotopy`, and `powerSetComplex_contractible`,
  the recorded proof dependency lem-weil-pbc-power-set-complex-contractible.
  The full definitions and contraction signature were read. Boundary and cone
  are adaptations of those existing maps to the common augmented index,
  not independent replacements of their positive-degree constructions.

Source check: opened the current `literature/blueprint/latest/blueprint/`
six-functors-basics ctf-stability direct-images proof, paragraph (3).
It states the stability argument only; as the node expressly records, this
prefix comparison is an agent-formulated auxiliary expansion rather than a
separately asserted blueprint theorem. Its full eleven-step node proof is
included in the theorem's docstring, including the n=0 and augmentation cases.

Edge cases checked before and during writing:

- n=0: A has only augmentation and degree zero components; Q_0 is the prefix
  of [x]-A_0[x], with no reference to A_1 or an undefined Q_{-2}.
- Empty tuple: translation fixes it, augmentation sends [x] to its basis
  element, C_b sends that element to [b], and Q_{-1} is zero.
- Repeated/equal tuple entries, negative or zero coefficients, and duplicate
  formulas remain valid: the list construction does not collect evaluated
  terms. The identity A gives Q=0 even if its uncollected list has cancellations.
- The trivial group and trivial subgroup are allowed; no Hausdorff, profinite,
  openness, compactness, or finite-index assumptions appear.
- An empty A formula list in a positive degree is accepted as input whenever
  the other hypotheses hold; the augmentation condition rules out impossible
  degree-zero zero maps. An empty family of a_i permits projection-only maps.
- All truncations have explicit finite bounds; no A above n occurs. G and
  the optional index family have independent explicitly declared universes.

Searches (no exact existing statement found):

- msearch leanfinder: "Equivariant prefix cone homotopy on augmented free tuple
  chains with finite continuous integral evaluation formulas": eight hits,
  mainly GenLoop homotopies and DoldKan.homotopyPInftyToId; none is this recursion
  for arbitrary A or supplies its finite continuous formulas.
- msearch loogle: `"Homotopy", "Finsupp"`: zero hits.
- msearch grep in RepresentationTheory:
  `(prefix|cone).*(homotopy|chain)|(homotopy|chain).*(prefix|cone)`: zero hits.
- msearch leansearch: "Prefix cone recursion for augmented free integer tuple
  chain endomorphisms with finite continuous formulas": eight irrelevant
  Cone/ContinuousHom recursor hits.
- rg in project WeilConjectures and Sheaf for prefix homotopy / finite
  evaluations, and the exact node id: found the upstream power-set contraction
  and prose uses of this calculation in rectangle/cocycle statements, not a
  declaration of this theorem or its recursive finite formula list. Read the
  HomogeneousCocycleRectangleDetection module. Name searches for prefixBoundary,
  prefixCone, prefixRecursiveQ, prefixFormulaList and HasPrefixCoordinates in
  Mathlib, both source roots and dag/lean_names_upstream.json found no clash.

Validation: scompile.py compiled both its sandbox probe and the actual library
module cleanly, with the expected sorry-only theorem. The final delivery dry
run is recorded by the delivery wrapper. No statement dispute or correction.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
