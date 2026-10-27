## Worker report

Delivered module: `Sheaf.Algebra.Homology.RationalBasedRetract`.
The general statement is `RationalBasedRetract.universal_homotopy`; the final
constant-complex clause is `RationalBasedRetract.constant_universal_homotopy`.
Both proofs are `sorry`, as required for stage 2. All other declarations contain
real formulas; no choice from a postponed existence theorem occurs.
The item's statement, dependencies and proof are unchanged. No statement dispute,
new nodes, or dependency repairs are needed.

Hypotheses, individually:

- The arbitrary set of components is `M : Type u`; no finiteness or nonemptiness
  instance is present.
- The based rational cochain complexes are `P K : M → CochainComplex
  (ModuleCat.{v} ℚ) ℤ`. `P` already includes d² = 0. The integer indexing is the
  cochain reindexing of the dependency's chain-complex convention.
- `IP IK : M → ℤ → Type w` and `bP bK : ∀ m n, Module.Basis ...` give the specified
  bases in every degree. Arbitrary index sets, including empty and infinite ones,
  are allowed; a common universe is obtained by taking the maximum of sizes.
- `hPneg` and `hKneg` make negative terms zero modules, expressed invariantly by
  `Subsingleton`, rather than by selecting a particular presentation of zero.
- `hKzero` sets all differentials of K equal to zero.
- `i : ∀ m, K m ⟶ P m` and `p : ∀ m, P m ⟶ K m` are rational chain maps.
  Their chain-map equations and `hKzero` are exactly di = 0 and pd = 0, without
  additional assumptions. The main conclusion repeats di = 0 explicitly.
- `hpi : ∀ m, i m ≫ p m = 𝟙 (K m)` is pi = 1 (categorical composition order).
- `hH : ∀ m n, IsIso (HomologicalComplex.homologyMap (p m) n)` is precisely the
  induced isomorphism on kernel-modulo-image cohomology. Since K has zero
  differential, Hⁿ(K) is canonically Kⁿ; hence this is the node's stated map.

Conclusions, individually:

- `kernel P K p m n` is ker p inside Pⁿ, using `LinearMap.ker`.
- `cycles P K p m n` is Cⁿ ∩ ker dⁿ, the ambient image of ker(d|C).
- The first conjunct is `IsCompl (LinearMap.range iⁿ) Cⁿ`. The next conjunct
  says d maps C into C, and the third says d kills i(K). Along with the supplied
  chain maps and pi = 1, these state the splitting as complexes with the original
  inclusion and projection.
- Acyclicity is the equality `cycles ... n = (kernel ... (n-1)).map d`, i.e.
  cycles equal boundaries inside C. `cycles ... 0 = ⊥` states the bottom case.
- Existential `L,e` with `Complements ... L e` gives C = Z ⊔ L and disjointness,
  hence C = Z ⊕ L, together with the exact differential equivalence.
  `e m n : L^(n-1) ≃ₗ[ℚ] Zⁿ` is the same d: Lⁿ ≃ Z^(n+1), reindexed; its value
  is required to equal the actual differential. Thus this does not introduce an
  arbitrary isomorphism unrelated to d.
- The following universal quantifier ranges over EVERY such L and e. It first
  asserts `(e m 0).symm.toLinearMap = 0`, namely s⁰ = 0.
- The existential h consists of rational linear maps Pⁿ → P^(n-1). The next
  equation is literally h(ik+z+l) = e.symm(z), including its inclusion into P.
- `Identities ℚ ...` states h⁰ = 0, d² = 0, di = 0, pd = 0, pi = 1,
  dh + hd = 1 - ip, hi = 0, ph = 0, and h² = 0. The two `cast`s in dh+hd only
  identify (n-1)+1 and (n+1)-1 with n; they impose no mathematical hypotheses.
- `SumIdentities` uses Mathlib `DFinsupp.mapRange.linearMap` on all four maps.
  Its underlying `Π₀ m, P m n` is the direct sum; these componentwise maps preserve
  m and finite m-support by construction, and satisfy exactly the same identities.
- Each basis vector's image has finite rational support because `bW.repr (f (bV a))`
  is a `Finsupp`. This is built into the type, with no finite-dimensionality premise.
- `extend` is a real B-linear map between free B-modules on the SAME basis sets:
  its column at a is `mapRange (algebraMap ℚ B)` of that finite rational column,
  and `Finsupp.linearCombination B` extends it B-linearly. This explicitly supplies
  well-defined maps without any assumed extension or chosen arbitrary map.
- `ExtendedIdentities` uses that formula for each of d,i,p,h and asserts all the
  displayed identities on every component and the direct sum. The quantifier
  `∀ (B : Type t) [CommRing B] [Algebra ℚ B]` includes the zero algebra.
- In the final clause, singleton-basis coordinates present Pⁿ = ℚ. `constantKIndex n`
  has one element exactly for n = 0 and is empty otherwise, giving K = ℚ[0].
  `constantD` is zero at even n and identity at odd n; `constantI` and `constantP`
  are the identity at zero, zero elsewhere. `constantH R n` is h^(n+1), equal to
  identity exactly when n+1 is even (automatically at least 2), zero otherwise.
  The omitted h⁰ has zero target. `constant_universal_homotopy` gives all bottom
  and positive-degree identities and, separately for d,i,p,h, states equality of
  their B formulas with `extend` of their rational matrices. This fixes the same
  rational choice over every B, rather than choosing new homotopies over B.

Dependencies read and used:

- `def-weil-pbc-module-chain-complex-homology`: public import
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`;
  `HomologicalComplex.homology` and `HomologicalComplex.homologyMap`.
  Read their full signatures/docstrings and the associated short-complex setup.
  Public import `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` supplies the
  module-category homology instances; `ShortComplex.moduleCatLeftHomologyData`
  and `ShortComplex.moduleCatHomologyIso` were read to check the quotient meaning.
- Proof dependency `lem-trf-vector-subspace-complement`: plain import
  `Mathlib.LinearAlgebra.Basis.VectorSpace`; read `Submodule.exists_isCompl`
  and its complement construction. This is the existing arbitrary-dimensional
  complement result, not restated in this delivery.
- Other Mathlib APIs: `Module.Basis`, `Finsupp.linearCombination`,
  `Finsupp.basisSingleOne`, `DFinsupp.mapRange.linearMap`, and `Submodule.map`.
  No polynomial bar module is imported: its specialized extension is not the
  general arbitrary-basis construction needed here.

Edge cases checked before and during drafting: M empty makes the direct sums
zero; empty basis sets and zero P/K are permitted; arbitrary infinite bases still
produce finite columns; complexes may be unbounded above; degree zero uses
Z⁰ = 0 and zero incoming module; negative degrees are zero by hPneg/hKneg; the
coefficient algebra is allowed to be zero (no Nontrivial instance). In the constant
example, at n = 0 the positive homotopy h¹ vanishes and ip = 1; at n = 1, h²d¹ = 1;
at n = 2, d¹h² = 1; every pair of successive homotopies contains a zero map.

Searches actually performed:

- `msearch.py ... leanfinder`: "A fixed rational cochain retract with acyclic
  kernel admits a square zero contracting homotopy from complements to cycles,
  extending its column finite matrices to every rational algebra". Eight results,
  including QFactorsThroughHomotopy, DoldKan.homotopyQToZero and K-projective /
  K-injective homotopyZero; none supplies the specified retract, every-complement
  formula, side identities and simultaneous arbitrary-basis extension.
- `msearch.py ... loogle`: `"Homotopy", "retract"`: OK, zero hits.
- `msearch.py ... grep`: `(contracting.?homotopy|column.?finite|based.*[Ee]xten|deformation.?retract)`:
  two hits, a column-finite matrix comment in Basis/Cardinality and BasedFunctor;
  neither matches this statement.
- `rg` in project `WeilConjectures/` and `Sheaf/`: based/rational retract/homotopy,
  matrix extension, node id, and proposed namespace/declaration names. No exact
  statement or namespace collision. Read the complete existing
  `Sheaf.Paper.RationalPolynomialBarContraction`, including `extendHomotopy` and
  `contraction`: it is specific to polynomials and lacks the general conclusions.
- Targeted Mathlib source searches found finite-support mapRange/linearCombination,
  DFinsupp maps and basisSingleOne; their definitions were read and reused.

Validation: the complete final module compiled in both sandbox and library mode
through the prescribed `scompile.py`, with no errors or warnings. The only proof
bodies in the module are the two required postponed statement proofs.

## Second reading by Q83

Self-audit, not an independent review: the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent delivery review. I read
the node and final file again against every clause as mapped above. The audit
checked in particular the universal quantifier on complements, the equality of e
with the differential, the same rational h before the B quantifier, finite support,
zero coefficients, and the constant-complex clause. The main and constant theorem
statements together cover the node. No statement correction was made. Compiler
feedback required importing the standard Finsupp basis module and explicitly
annotating the source/target ModuleCat objects of its constant matrices; these
were elaboration repairs, with no change to the mathematical statement.
