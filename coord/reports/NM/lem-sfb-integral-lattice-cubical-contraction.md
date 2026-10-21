## Worker report

This stage-2 delivery states `IntegralLatticeCubical.contraction` in
`Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction`. Its sole theorem has proof
`sorry`; every definition contains real data. All eleven public declarations are listed
in `lean.declarations`. The auxiliary definitions belong to the specified cubical-chain
notion of this item, rather than introducing independent mathematical prerequisites.
No new DAG nodes or dependency repairs are needed. The item JSON changes only `lean`.

The prior retry was a stage-1 no-op: NJ had already delivered the split. I read the current
NJ-reviewed eight-step proof and supplied the missing stage-2 Lean statement. The current
node has no `lean` record, and no existing project declaration states this contraction.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 0623,
`definition-koszul-complex`, including the alternating differential immediately before it,
and Tag 062F, `lemma-regular-koszul-regular`, including its proof. These are algebraic
comparison ingredients only, as the node expressly says. The nonequivariant contraction
is the node's agent-written signed-coordinate construction. I also read paragraph (3) of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`; the lattice lemma
is an algebraic input below its open-direct-image argument and does not change the unit.
The theorem docstring reproduces the eight proof steps, including the two sign cases,
negative-coordinate path sums, reset-map telescoping, exactness and free translation orbits.

Clause-by-clause correspondence:

- An integer rank at least zero is `r : ℕ`. The lattice is exactly `Fin r → ℤ`, and
  `unitVector r i := Pi.single i 1` is its standard basis. `Fin r` relabels coordinates
  1 through r by 0 through r-1 without changing their order or the smaller-direction count.
- `Directions r a` is the subtype of finite subsets `I : Finset (Fin r)` with
  `(I.card : ℤ) = a`. `Chains r a` is the free integral module on lattice-point/direction
  pairs, represented by finitely supported functions. `cell r a v I` is the corresponding
  basis vector when the cardinality matches, and zero otherwise. The theorem explicitly
  asserts `Module.Free ℤ (Chains r a)` and `Subsingleton (Chains r a)` outside `[0,r]`.
  Thus both negative and above-top degrees are zero modules, without excluding them.
- `boundary r a` extends the displayed boundary by `Finsupp.linearCombination ℤ`.
  Its basis image sums over precisely `i ∈ I`, with coefficient
  `(-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card`, translated vertex minus original vertex,
  and direction set `I.erase i`. Degree zero and outside-range boundaries vanish because
  the corresponding face sums or source groups are empty. No boundary is chosen abstractly.
- `augmentation r` extends the constant basis image 1. `sectionMap r` is scalar
  multiplication of the actual vertex `cell r 0 0 ∅`, so takes 1 to the origin.
- `originProjection r a` sends every basis vector to `cell r a 0 ∅`. The theorem asserts
  its equality to section composed with augmentation at zero and its vanishing elsewhere.
  The empty set has cardinality zero, so this is exactly the stated `e`, with real data.
- The first two conjuncts are boundary squared zero in every integer degree and
  augmentation composed with the degree-one boundary zero. Composition uses `LinearMap.comp`.
  Integers act on abelian groups canonically, so integral linear maps are exactly the
  abelian-group homomorphisms required here.
- `∃ h : (a : ℤ) → Chains r a →ₗ[ℤ] Chains r (a + 1)` states existence of the homotopy.
  Its first property, for every `0 ≤ a`, is precisely `∂ h + h ∂ = id - e` on every `x`.
  `incomingBoundary r a` is the same degree-`a+1` boundary with the canonical arithmetic
  cast `(a + 1) - 1 = a`. The other summand uses `LinearEquiv.cast` with
  `(a - 1) + 1 = a`. These are identity transports of degree indices, not extra assumptions.
  The next property explicitly sets `h (-1) (boundary r 0 x)` to zero as prescribed.
  Augmentation composed with section equals `LinearMap.id` is a separate conjunct.
- Exactness is stated without hiding the underlying maps: for all positive integer
  degrees, `LinearMap.range (incomingBoundary r a) = LinearMap.ker (boundary r a)`;
  at zero, range of `boundary r 1` equals kernel of `augmentation r`; at the terminal
  integers, `Function.Surjective (augmentation r)`. This is exactly augmented exactness.
  The imported dependency's module-chain-complex homology uses the kernel/image quotient;
  `ShortComplex.moduleCatLeftHomologyData` is its explicit module implementation.
  The node's exactness assertion does not require a separately chosen bundled complex;
  the actual degree maps and their square-zero law are all given here.
- `translate r a w` extends `[v,I] ↦ [v+w,I]`. The theorem asserts its commutation with
  each boundary and preservation of augmentation, the latter expressing trivial action
  on the terminal integers.
- The direct-sum clause is an integral linear equivalence from `Chains r a` to
  `Directions r a →₀ ((Fin r → ℤ) →₀ ℤ)`. The inner module is the free integral module
  on the lattice; the outer finitely supported functions are its direct sum over `I`.
  The displayed basis-image law sends `[v,I]` to the I-th summand's `[v]`, and the next
  law intertwines translation with `Finsupp.mapDomain (fun v ↦ v+w)` in every summand.
  `Finite (Directions r a)` explicitly ensures this sum is finite. This gives the
  specified regular translation modules, rather than an arbitrary abstract decomposition.
- Neither the homotopy nor the section has an equivariance condition. No negative
  assertion that they must fail equivariance is added: "need not" permits failure.
- When `r = 0`, the homotopy witness is required to vanish in every degree, and a
  linear equivalence from `Chains r 0` to `ℤ` identifies augmentation with its forward
  map and section with its inverse. This is exactly `s = ε = 1` under the unique-vertex
  identification, without incorrectly equating maps with different source types.

Dependencies used and signatures/docstrings read:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`
  (lines 40-48): existence of a basis, together with the set-indexed equivalence.
  The theorem uses this exact predicate. Finitely supported integer coefficients supply
  the actual free abelian groups and `Finsupp.linearCombination` supplies linear extension.
- `def-weil-pbc-module-chain-complex-homology`:
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  `HomologicalComplex.homology` (lines 65-91), a short complex's homology;
  `Mathlib.Algebra.Homology.HomologicalComplex`, `ChainComplex` (lines 146-152);
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
  `ShortComplex.moduleCatLeftHomologyData` (lines 101-113), the kernel modulo image.
  This is the exact meaning used for augmented exactness, rendered explicitly as
  kernel equals image and augmentation surjectivity. Both recorded dependency modules
  are public imports. There are no additional theorem proof dependencies to import.

Edge cases checked before drafting: `r = 0` has one vertex and no positive-dimensional
cells; every `a < 0` and `a > r` has no basis index; the degree-zero boundary has no
faces; top-degree homotopy has zero target. In rank one, an edge has boundary
`[v+1]-[v]`; paths to negative vertices require the negative sum from v to zero, including
v = -1. In rank two, removing the lower and upper directions has opposite signs, and
removal in either order gives the same translated corners. At all ranks the augmentation
of any edge boundary is `1-1`. At rank zero the projection is identity, making a zero
homotopy consistent with the contraction. The translation-equivariance clause involves
only differential and augmentation, so does not falsely require the origin to be fixed.
The specific finite-rank integer objects need no independent universe parameter;
`set_option autoImplicit false` forbids implicit unbound variables.

Searches actually run (recorded in sandbox `searches.jsonl`):

- LeanFinder: "The integral cubical chain complex of the lattice Z^r contracts onto its
  augmentation by a group homomorphism". Eight results: simplicial extra degeneracy,
  standard bar resolution and augmentation, Dold-Kan, alternating constant complex.
  None has these finite cubical terms or the given differential.
- Loogle: `ChainComplex, Homotopy`. Ten results, including `Homotopy.mkInductive`,
  projective-resolution lift homotopies and singular/simplicial homotopy operations.
  They construct or manipulate homotopies for other supplied complexes; no exact match.
- Mathlib grep through msearch: `cubical|[Ll]attice.*[Cc]ontract|[Cc]ontract.*[Ll]attice`.
  No hits.
- LeanSearch: "The augmented cubical chain complex on an integer lattice is split exact
  and has an integral chain contraction". Eight hits: augmentation construction, abstract
  short-complex splitting and acyclicity, and singular homology of totally disconnected
  spaces. None defines this cubical chain complex or states the contraction.
- Direct project rg for `cubical|[Ll]attice.*[Cc]ontract|integralLattice|IntegralLattice`:
  only unrelated integral coefficient/lisse representation lattices. rg for
  `lem-sfb-integral-lattice-cubical-contraction|[Ll]attice.*[Kk]oszul|[Cc]ubical` in
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found only
  a downstream prose mention of the discrete-lattice Koszul node. A literal node-id
  grep in `lean/WeilConjectures` found nothing. Exact namespace/module-name rg across
  Mathlib and both project source trees found no existing declaration.
- Read the plausible candidate sources: `RepresentationTheory/Homological/Resolution.lean`
  lines 230-258 (`forget₂ToModuleCatHomotopyEquiv`) and
  `Algebra/Homology/AlternatingConst.lean` lines 228-237
  (`alternatingConstHomotopyEquiv`). The former has the simplicial bar-resolution terms;
  the latter has alternating identity/zero maps on a constant object. Neither is this
  finite cubical lattice complex, and neither is a one-line specialization of the item.

No statement correction and no STATEMENT-DISPUTED issue. Server `scompile.py` successfully
compiled both its sandbox probe and the named library module (about 2.1 and 2.4 seconds),
with no errors or unexpected warnings. Initial elaboration errors were corrected by
marking the Finsupp cell noncomputable and inserting the canonical integer-degree casts.
No theorem was proved.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
