## Worker report

The module `Sheaf.Algebra.Lie.PinnedSerrePresentationIsomorphism` states
`LieAlgebra.exists_pinnedSerrePresentation_isomorphism`, with its entire proof `sorry`.
It introduces no definitions. The node copy changes only `lean`; no statement correction,
new node, or dependency repair is needed. All universes and variables are explicit, with
`autoImplicit false`. Classical decidable equality is used to form the internal direct sum
and the existing Serre quotient without adding a decidable-equality hypothesis.

The source was read in the local Milne PDF: printed pp.503–504 (PDF pages 515–516),
and printed p.508 (PDF page 520). The former defines the split Cartan and root
decomposition and gives the Serre presentation; the latter supplies the characteristic-zero
extension and normalized simple-root triples. The comparison with a prescribed rational
pinning is the supporting assertion identified as such in the node, not a claim that the
printed complex existence theorem alone states this comparison. No unit statement changes.
The current blueprint is `literature/blueprint/latest`, unit `sk-thm-sf-ctf-stability`.

Hypothesis and clause correspondence:

- Rational finite-dimensional semisimple Lie algebra: `(L : Type u) [LieRing L]
  [LieAlgebra ℚ L] [FiniteDimensional ℚ L] [HasTrivialRadical ℚ L]`.
  `HasTrivialRadical` is exactly the predicate recorded by
  `def-wf-semisimple-lie-algebra`, rather than the different direct-sum predicate
  `LieAlgebra.IsSemisimple`.
- The maximal abelian subalgebra is `(H : LieSubalgebra ℚ L) [IsLieAbelian H]`
  with `hmax`. The displayed `hsplit` says every adjoint of an element of H is
  diagonalizable over ℚ by the span of its eigenspaces, as in Milne p.503.
- The reduced crystallographic root system in the Cartan dual is
  `(ι : Type v) [Finite ι] (P : RootPairing ι ℚ (Module.Dual ℚ H) H)` with
  `[P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]` and `heval` identifying
  its bilinear pairing with evaluation. `P.root` is an embedding, so its range
  is exactly a finite set of roots. Root nonvanishing follows from the
  root-coroot pairing being 2 over ℚ. The root pairing's intrinsic coroots
  encode the given root system; they are not silently identified with the
  independently supplied normalized bracket elements `hα`.
- The direct decomposition `L = H ⊕ ⨁ g_α` is `hdecomp`, using
  `DirectSum.IsInternal` for the family indexed by `Unit ⊕ ι`. Its first
  summand is `H.toSubmodule`; each remaining summand is
  `(LieModule.weightSpace L (P.root a)).toSubmodule`. The definition
  `LieModule.mem_weightSpace` says exactly `[h,z] = α(h) • z` for every h.
  The one-dimensionality of every root space is `hdim`.
- The element h_α is `hα a : H`. `hbracket` places its image in L in the linear
  span of all brackets between the ordinary α and -α weight spaces. This is
  the node's bracket of subspaces, not an arbitrary element of H. `htwo` is
  exactly `α(h_α) = 2`. These hypotheses are for every root, not just simple roots.
- The finite simple-root index is `(I : Type w) [Finite I]`; `s : I → ι`
  selects the roots and `b : Module.Basis I ℚ (Module.Dual ℚ H)` with `hb`
  identifies them with the basis vectors. Injectivity of s follows from the
  basis and root embedding, so no independent injectivity assumption is added.
  `hsign` states separately that every root coordinate is an integer and that
  either all coordinates are nonnegative or all are nonpositive.
- The prescribed nonzero e_i and f_i are `e f : I → L`, with `he` and `hf`
  giving ordinary positive/negative weight membership and nonvanishing.
  `hef` is `[e_i,f_i] = h_(α_i)`.
- The integer matrix is `A : Matrix I I ℤ`, and `hA` is precisely
  `(A i j : ℚ) = α_j(h_(α_i))`. Quantifying over an integer matrix with this
  equality is the usual explicit rendering of "put a_ij = ... ∈ ℤ".
  The node's consequences `a_ii = 2` and `a_ij ≤ 0` for distinct indices
  are the first two conjuncts of the conclusion, not extra assumptions.
- The presented algebra is the existing `Matrix.ToLieAlgebra ℚ A`.
  Reading `CartanMatrix.Relations.HH`, `EF`, `HE`, `HF`, `adE`, `adF`,
  `toSet`, and `toIdeal` confirms all six families of relations and the
  Lie ideal they generate. Mathlib writes the E relation as
  `(ad E_i)^((-A i j).toNat) [E_i,E_j]`, which equals the stated
  `(ad E_i)^(1-A i j) E_j` off the diagonal once `A i j ≤ 0`.
  On the diagonal its extra generator is already zero by alternation.
  The same applies to F. The free universal property is provided by
  `FreeLieAlgebra.lift`, an equivalence between generator assignments and Lie homomorphisms.
- The conclusion `∃ φ : Matrix.ToLieAlgebra ℚ A ≃ₗ⁅ℚ⁆ L` supplies an actual
  rational Lie algebra isomorphism. Each of the next three quantified clauses
  evaluates φ on `LieSubmodule.Quotient.mk' ... (FreeLieAlgebra.of ℚ ...)`
  for respectively `CartanMatrix.Generators.H`, `E`, and `F`, and gives
  respectively the prescribed h_α, e_i, and f_i. Thus the conclusion specifies
  the induced pinned map, rather than merely asserting an unpinned isomorphism.

Recorded dependencies and declarations used:

- `def-wf-lie-algebra` is a Mathlib leaf, with its recorded `LieRing`,
  `LieAlgebra`, `LieSubalgebra`, and quotient notions. The signatures and
  docstrings were read in `Mathlib.Algebra.Lie.Basic`, `Subalgebra`, and `Quotient`.
- `def-wf-semisimple-lie-algebra` is a Mathlib leaf recorded on
  `Mathlib.Algebra.Lie.Semisimple.Defs`, `LieAlgebra.HasTrivialRadical`,
  with the equivalence `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
  in `Mathlib.Algebra.Lie.Semisimple.Basic`; both were read.
- The ordinary weight-space declaration and membership characterization are
  `LieModule.weightSpace` and `LieModule.mem_weightSpace` in
  `Mathlib.Algebra.Lie.Weights.Basic`.
- The internal-sum interpretation was checked against
  `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` in
  `Mathlib.Algebra.DirectSum.Module`.
- The presentation and generator constructors are in
  `Mathlib.Algebra.Lie.SerreConstruction`; its free universal property is
  `FreeLieAlgebra.lift` in `Mathlib.Algebra.Lie.Free`.
- RootPairing, its root-system mixin, reducedness, and crystallographicity were
  read in `Mathlib.LinearAlgebra.RootSystem.Defs`, `Reduced`, and `IsValuedIn`.
  `Mathlib.LinearAlgebra.RootSystem.Chain` exposes these root-system interfaces.
- The stated proof dependency `lem-sfb-serre-rational-presentation` is imported
  privately from `Sheaf.Algebra.Lie.RationalSerrePresentation`. Its full theorem
  signature and proof docstring were read. Its `rationalSerreGenerator` helper
  uses `Fin r`; the present arbitrary finite-index statement instead writes the
  identical quotient-generator expression directly, without defining a copy.
- The proof dependency `lem-sfb-sl2-primitive-string-vanishing` is the recorded
  Mathlib leaf `IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_eq_zero_of_eq_nat`
  in `Mathlib.Algebra.Lie.Sl2`, which is imported privately; its signature was read.
- `lem-sfb-integrable-sl2-reflection-automorphism` has neither a Lean record nor
  Mathlib match in the current DAG, so there is no stated proof module to import.
  It is a proof dependency only and supplies no missing notion in this statement.
  Its use is retained explicitly in the theorem's seven-step proof docstring.

Edge cases checked: no `Nonempty` hypothesis appears for I or ι. If I is empty,
the basis gives `Dual ℚ H = 0`; the nonzero-root and decomposition hypotheses
force no roots and L = 0. The quotient on no generators is zero and has the
unique isomorphism to L. The direct sum still retains its Unit-indexed Cartan
summand, so it does not accidentally omit H in rank zero. Rank one gives the
usual sl2 relations with no off-diagonal conditions. Reducible systems, including
A1 × A1, are allowed: there is no irreducibility or simplicity assumption.
In type A2 the off-diagonal -1 produces the expected second adjoint power.
Independent universes u, v, w permit arbitrary ambient algebra and index sizes;
there is no forced universe equality or `Fin`-only restriction.

Searches for an existing statement, all run through the prescribed msearch wrapper:

- LeanFinder: "Chevalley Serre presentation isomorphism to a split semisimple
  rational Lie algebra with prescribed simple root generators" returned eight
  Geck construction hits. Those construct a particular matrix Lie algebra,
  not an isomorphism with the prescribed L and pinning.
- Loogle: "Matrix.ToLieAlgebra, FreeLieAlgebra.lift, LieEquiv" returned no hits.
- Grep: "ToLieAlgebra|serre.*[Ii]so|[Ii]so.*[Ss]erre" in Algebra/Lie returned
  six hits: the quotient, exceptional-type abbreviations, and a direct-sum
  homomorphism; none states this pinned isomorphism.
- LeanSearch: "A split semisimple Lie algebra is isomorphic to the Serre
  presentation with prescribed simple root vectors" returned quotient, relation,
  and semisimplicity definitions, not this theorem.
- Project `rg` searches for Serre/pinning/presentation and the exact node id
  in `lean/WeilConjectures` and `lean/Sheaf`, plus the upstream names table,
  found no existing pinned Serre isomorphism. The related Sheaf theorem
  `rationalSerrePresentation` constructs and describes the quotient; the
  Chevalley normalization theorem constructs a basis, not this quotient map.

Validation: the prescribed `scompile.py NN lem-sfb-pinned-serre-presentation-isomorphism`
compiled the file both as a sandbox module and under its library module name,
cleanly in 5.5 and 1.5 seconds. The initial missing decidable-equality instance
for the direct-sum index was repaired with declaration-scoped `open Classical in`.
No diagnostic commands remain; every line has at most 100 characters.

No `STATEMENT-DISPUTED` issue was found.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
