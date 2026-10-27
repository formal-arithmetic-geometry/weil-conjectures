## Worker report

Repair of returned immutable head 07bac48b6421. The previous delivery was a
stage-1 re-split and supplied no Lean statement. This delivery supplies
`lean/Sheaf/AlgebraicGeometry/UnitBinomialFiniteEtale.lean`, whose sole declaration is
`AlgebraicGeometry.unitBinomial_finite_surjective_etale`. Its proof is `sorry`, as
required for stage 2. There are no new definitions, helper theorems, new DAG nodes,
dependency repairs, or statement corrections.

The sandbox initially contained only launcher marker files, not the previous node or
report. I therefore took the entire current live-read-clone node as the baseline,
including Q51's seven-step proof and its reviewed record, and changed only `lean`.
In particular `proof`, `proof_deps`, `proof_origin`, `split_report`, `statement`, and
all seven `stmt_deps` are identical to that live node. No supersession of Q51's split
is proposed. The delivery wrapper rebases the delivery on the current server branch.

Source read: `literature/stacks-project/etale-cohomology.tex`, Tag 03PL,
`lemma-kummer-sequence`, lines 2842–2885, especially 2872–2884. This is exactly the
unit-root algebra `A[T]/(T^n-a)` whose structure map is finite free of rank n,
faithfully flat, surjective on spectra, and standard etale because its derivative
is invertible. The declaration docstring reproduces the seven reviewed proof steps,
with their dependency IDs, including the separate zero-ring argument, basis,
finiteness, faithful-flat coordinate argument, prime-surjectivity, explicit inverse
of the derivative, and standard-etale quotient isomorphism.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring of any universe: `(R : Type u) [CommRing R]`, with `universe u`
  explicitly declared and `set_option autoImplicit false`.
- The integer `n >= 1`: `(n : ℕ) (hn : 1 ≤ n)`. Every integer at least one has this
  natural-number representation; negative integers and zero are outside the node.
- Its image in R is a unit: `(hnR : IsUnit (n : R))`, using the canonical natural cast.
- The specified unit: `(u : Rˣ)`, with `(u : R)` its image in the ring.
- The polynomial and actual quotient algebra: every occurrence of B is
  `AdjoinRoot (Polynomial.X ^ n - Polynomial.C (u : R))`. `AdjoinRoot` is definitionally
  `Polynomial R ⧸ Ideal.span {f}`, not an arbitrary algebra isomorphic to the quotient.
  Its Mathlib `Algebra R` instance is the canonical quotient algebra structure.
- The class t of T: `AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (u : R))`,
  defined as `AdjoinRoot.mk f Polynomial.X`.
- Free with the particular basis `1,t,...,t^(n-1)`: the first conjunct is
  `∃ b : Module.Basis (Fin n) R (AdjoinRoot (...)), ∀ i : Fin n, b i = ... ^ (i : ℕ)`.
  This records both existence of the basis and every specified basis vector, rather
  than merely freeness or an unspecified module rank. In particular i = 0 is 1.
  `Module.Basis` means an R-linear equivalence to finitely supported coordinates,
  exactly the recorded free-module notion.
- The canonical morphism: all three geometric conjuncts use the identical expression
  `Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot (...))))`. The ring map is
  the canonical structure map, and `Spec.map` reverses its direction as required.
- Finite: `IsFinite` of that morphism, the second conjunct.
- Surjective: `Surjective` of that morphism, the third conjunct, meaning surjectivity
  of its underlying point map.
- Etale: `Etale` of that morphism, the fourth conjunct, the recorded affine-local
  Mathlib definition, equivalent to the node's flat/unramified/presentation wording.
- The zero ring and n = 1 are allowed: no `Nontrivial`, field, domain, characteristic,
  or extra rank/degree hypothesis is present. The index is `Fin n`, not the polynomial's
  `natDegree`, which would become zero over the zero ring.

The seven statement dependencies and declarations read and used:

- `def-weil-polynomial-ring`: `Polynomial` in `Mathlib.Algebra.Polynomial.Basic`,
  lines 72–82; the binomial uses its `X`, `C`, and ring operations.
- `def-weil-pbc-algebra-hom-quotient`: its Mathlib match, `AlgHom` in
  `Mathlib.Algebra.Algebra.Hom` (lines 35–39), `Ideal.Quotient.algebra` and
  `Ideal.Quotient.mkₐ` in `Mathlib.RingTheory.Ideal.Quotient.Operations`
  (lines 353–370). Read also `AdjoinRoot` (lines 61–64), `of`, `algebraMap_eq`
  (147–148), and `root` (163–165) in `Mathlib.RingTheory.AdjoinRoot`.
  The statement uses their canonical quotient algebra, without redeclaring it.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`, lines 469–480.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, lines 35–41.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, lines 57–61.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, lines 43–50.
- `def-weil-pbc-free-module`: `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`, lines 42–44; its notion of a basis is
  `Module.Basis` in `Mathlib.LinearAlgebra.Basis.Defs`, lines 81–96.
  The first conjunct supplies precisely this data with the prescribed index/vectors.

The statement imports these modules publicly, and the stated Mathlib proof inputs
as ordinary imports. The latter include `AdjoinRoot.powerBasis'` and
`Polynomial.Monic.finite_adjoinRoot` (AdjoinRoot, lines 633–652),
`AlgebraicGeometry.IsFinite.SpecMap_iff` (Finite, lines 73–76),
`Module.FaithfullyFlat` (Flat.FaithfullyFlat.Basic, lines 58–65),
`RingHom.FaithfullyFlat` (RingHom.FaithfullyFlat, lines 23–31),
`PrimeSpectrum.comap_surjective_of_faithfullyFlat`
(Flat.FaithfullyFlat.Algebra, lines 144–148), and `StandardEtalePair`, its
`Algebra.Etale` instance and `homEquiv` (Etale.StandardEtale, lines 46–60,
141–148, 191–192). These match the proof dependencies; no unstated prerequisite
module is silently replaced by an extra hypothesis.

Edge cases checked mathematically before writing:

- Zero ring: every polynomial and quotient element is equal. For any positive n,
  `(Fin n →₀ R)` and B are singleton modules, so they admit the required linear
  equivalence; no linear-independence convention excludes this case. Both spectra
  are empty, hence their map is surjective, finite and etale.
- n = 1: the binomial is `T-u`, B is canonically R, the sole vector is `t^0 = 1`,
  and the spectrum map is an isomorphism. No n > 1 restriction appears.
- n = 0: excluded exactly by hn; its exclusion matters since a nonzero ring with
  u = 1 would give B = R[T] and the finite-rank assertion would fail.
- Positive characteristic: permitted whenever `(n : R)` is invertible. No
  separability or root-of-unity hypothesis is added. Over a field whose
  characteristic divides n, hnR correctly fails.
- Nonreduced rings: allowed; the inverse derivative calculation uses only units.

Searches actually run in this repair:

1. `msearch.py ... leanfinder` with query
   "For a commutative ring and a positive integer invertible in the ring, adjoining
   an nth root of a unit has the power basis of length n and finite surjective etale
   spectrum map" returned eight hits: `AdjoinRoot.powerBasis'`, `AdjoinRoot.powerBasis`,
   `IsPrimitiveRoot.powerBasis`, `IsAdjoinRootMonic.powerBasis`, and four related
   basis results. None states all of the node's module and scheme clauses.
2. `msearch.py ... loogle '"AdjoinRoot", "Etale"'` returned one hit,
   `StandardEtalePair.equivAwayAdjoinRoot`; this is a localization equivalence,
   not this statement.
3. `msearch.py ... grep 'etale_X_pow_sub_C|powerBasis.*|faithfullyFlat_of_monic'
   RingTheory` returned 25 hits, including `AdjoinRoot.powerBasis'`, module-finiteness
   uses, and general power-basis declarations; none gives the whole conjunction.
4. `rg` in the project source for AdjoinRoot/basis/etale found upstream
   `AdjoinRoot.etale_X_pow_sub_C` in
   `WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale`, lines 326–336, and its
   use in `WeilConjectures.AlgebraicGeometry.Sites.Kummer`, lines 105–129.
   I opened its full signature/docstring: it proves the ring etale clause only,
   so it cannot serve as an `existing: true` match for all four clauses.
   The site theorem constructs an etale cover for a unit on an open, not the
   specified basis and finite morphism over an arbitrary ring.
5. `rg` for `lem-sfb-unit-binomial-finite-etale` in `lean/WeilConjectures`
   gave no declaration. The project search in `lean/Sheaf` found only its mention
   in the proof docstring of `Curve/TameRadicalNormalization.lean`, not a statement.
6. Name search `unitBinomial_finite_surjective_etale|unitBinomial` across Mathlib,
   `lean/WeilConjectures`, and `lean/Sheaf` found no existing name or full statement.

No STATEMENT-DISPUTED issue was found. The node's mathematical statement is unchanged.
The old reviewed proof is preserved, including its zero-ring case; the theorem
statement itself does not rely on `natDegree = n` in that case.

Validation: the required `scompile.py N9 lem-sfb-unit-binomial-finite-etale` compiled
both the sandbox-transformed and final library module against the live published
server build, in 2.3 and 2.4 seconds, with no errors or unexpected warnings.

## Second reading by N9

I reread the actual finished signature against the live node and Tag 03PL after the
first successful compile. This is a separate second pass in the dispatcher worker;
no other agent was started, in accordance with the explicit brief. The maintainer's
independent review remains responsible for reviewing the delivery.

The ring binder is `CommRing R` with universe u, and does not impose nontriviality.
The positivity binder is exactly `1 ≤ n`; the other numerical binder is exactly
`IsUnit (n : R)`. The unit is the specified bundled `u : Rˣ`, not a newly chosen
ring element. All occurrences of the quotient use the same binomial and the
canonical `Algebra R` instance. The `Fin n`-indexed existential basis has every
vector equated to the matching power of the actual adjoined root. Thus it states
both freeness and the specified basis, including in the zero ring; it does not
replace n by `natDegree`. Each geometric conjunct uses the same `Spec.map` of
`algebraMap`, not an arbitrary map or an isomorphic unspecified algebra. The
three properties are exactly `IsFinite`, `Surjective` and `Etale`. The n = 1 and
zero-ring cases survive all binders, and n = 0 is excluded by the node itself.
No mathematical mismatch was found in this pass.

The return's H1 shape fault is repaired by a real compiled `.lean` module, a
non-null lean record whose signature is extracted verbatim from the file, source,
blueprint and complete seven-step proof docstrings, and this second-reading section.
The H2/A7 fault is repaired by restoring the whole current live node before
setting only its `lean`: the reviewed Q51 proof, all proof dependencies, proof
origin and split report are preserved verbatim as JSON values. There is no
attempt to re-split or supersede it, and no change of statement or dependencies.
