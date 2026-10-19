## Worker report

The module `Sheaf.TraceFormula.QuasiFinitePolynomialKernelDimensionDrop` states
`AlgebraicGeometry.topologicalKrullDim_spec_lt_of_quasiFinite_over_mvPolynomial_of_nonzero_kernel`.
It renders the source statement with a field `k`, a natural number `n`, a commutative
finite type `k`-algebra `T`, a `k`-algebra map from `MvPolynomial (Fin n) k`, finite type
of that map (`hφ`), quasi-finiteness at every prime of `T` (`hq`), and a nonzero element
of its kernel (`hker`). The conclusion is the strict inequality
`topologicalKrullDim (Spec (CommRingCat.of T)) < (n : WithBot ℕ∞)`, including the
zero-ring empty-spectrum convention.

Each hypothesis is rendered by the corresponding explicit binder: `[Field k]`,
`[CommRing T]`, `[Algebra k T]`, `[Algebra.FiniteType k T]`, `φ`, `hφ`, `hq`, and
`hker`. The finite-type clause is the explicit `@Algebra.FiniteType` instance induced
by `φ.toRingHom.toAlgebra`; the quasi-finite clause quantifies `q : PrimeSpectrum T`
and uses `@Algebra.IsQuasiFiniteAtPrime` for that same map and instance; the kernel
clause is `∃ p, p ≠ 0 ∧ φ p = 0`.

The proof docstring records the intended quotient-by-kernel argument: the four-rings
lemma gives finite type and quasi-finiteness after factoring through the quotient, a
nonzero kernel element lets one prepend `(0)` to every lifted prime chain, the local
quasi-finite dimension inequality and localization chain formula bound every target
local dimension by `n - 1`, and the spectrum/ring dimension identity gives the result.
The theorem proof is `sorry` as required for stage 2.

Dependencies used by the module are the recorded declarations `MvPolynomial` and
`Algebra.FiniteType` from Mathlib, `Algebra.IsQuasiFiniteAtPrime` from
`WeilConjectures.RingTheory.QuasiFiniteAtPrime`, `AlgebraicGeometry.Spec` from
Mathlib, `topologicalKrullDim` from Mathlib, and the proof-plan modules
`Sheaf.RingTheory.QuasiFiniteFourRings` and
`Sheaf.RingTheory.QuasiFiniteLocalDimension`.
The latter two are imported privately because they are proof dependencies.

Edge cases checked: `T = 0` has empty spectrum and bottom dimension; for `n = 0` every
nonzero polynomial is a unit, so a kernel relation forces `T = 0`; `n = 1` gives a
zero-dimensional bound; reducible examples such as `k[x,y]/(xy)` satisfy the expected
strict bound; and the identity polynomial map is excluded because its kernel is zero.
No extra hypothesis such as injectivity, integrality, or nontriviality of `T` was added.

Searches: the inherited stage-1 `msearch.py` LeanFinder, LeanSearch, Loogle, and
Mathlib grep searches (recorded in the node's `mathlib_searches`) found no exact
statement. `rg` over `lean/Sheaf` and `WeilConjectures/` found no declaration for
this blueprint id or theorem. Existing nearby dimension and quasi-finite declarations
were read and are only ingredients, not duplicates. No statement correction or new
node was needed.

## Second reading by Q95

Independent maintainer review of immutable delivery
`662b2ebe572af95af43af1d985cb5c7fe3f2b277`, performed on 2026-10-18.
The worker did not perform this reading. The theorem's mathematics and signature are accepted.

Clause-by-clause comparison:

- Field `k`: `(k : Type u) [Field k]`; no characteristic restriction.
- Nonnegative integer `n`: `(n : ℕ)` and variable set `Fin n`.
- Commutative finite type k-algebra `T`: `(T : Type v) [CommRing T] [Algebra k T]`
  and `[Algebra.FiniteType k T]`. No nontriviality, domain, reducedness or extra
  Noetherian assumption on `T`.
- The k-algebra map is `φ : MvPolynomial (Fin n) k →ₐ[k] T`. `MvPolynomial` is the
  dependency's actual finite-support polynomial algebra, not a private substitute.
- Finite type of this map is `hφ`, explicitly using `φ.toRingHom.toAlgebra`.
- Everywhere quasi-finite is `hq : ∀ q : PrimeSpectrum T, ...`, using precisely that
  algebra instance and `hφ`. The actual definition `Algebra.IsQuasiFiniteAtPrime`
  takes the canonical fibre prime under `PrimeSpectrum.preimageHomeomorphFiber`
  and requires its singleton to be open. Its data is real; no arbitrary map or
  hollow choice occurs. Tensor-factor order is immaterial via the canonical symmetry.
- Nonzero polynomial in the kernel is exactly `∃ p, p ≠ 0 ∧ φ p = 0`.
- Conclusion is the strict bound on the actual scheme's topological dimension:
  `topologicalKrullDim (Spec (CommRingCat.of T)) < (n : WithBot ℕ∞)`.
  `Spec` has underlying Zariski prime spectrum; `topologicalKrullDim` is the supremum
  of lengths of strict chains of nonempty irreducible closed subsets.
- Universes `u` and `v` are explicitly declared and independent. All variables are
  bound. The signature, after the merge tool's whitespace normalization, equals
  the JSON `lean.statement`; the replacement does not change it.

Sources and dependency inspection:

Read the immutable item and all five statement-dependency JSON records. Read Stacks
`algebra.tex` in the Q95 source clone: 00QK, lines 31380–31420 (especially the final
nonzero residue-polynomial inference); 00QF, lines 31267–31287; 00QG, lines
31291–31305; 00PN, lines 30293–30343; 00PK/00PL, lines 30195–30243. Read
`topology.tex`, definition-Krull, lines 1392–1418. The item isolates a valid
field-algebra input in 00QK; the valuation/domain hypotheses belong to the parent
application, not to this input.

Opened the exact Mathlib definitions in `Algebra/MvPolynomial/Basic.lean:82`,
`RingTheory/FiniteType.lean:39`, `AlgebraicGeometry/Scheme.lean:470`,
`Topology/KrullDimension.lean:39`, `Order/KrullDimension.lean:78` and the irreducible
closed-set structure. Read the current upstream quasi-finiteness definition via
`scompile.py --source WeilConjectures.RingTheory.QuasiFiniteAtPrime`, since both
local context trees lack that upstream file. It has the recorded independent
universes and canonical fibre construction.

Read every proof-dependency statement and the four-rings and local-dimension module
docstrings/signatures in the Q95 clone. Also opened the exact polynomial dimension,
localization-height and spectrum-dimension declarations in Mathlib.

Proof audit, in node order:

1. The empty spectrum has bottom dimension. With zero variables a nonzero kernel
   element is an invertible scalar, forcing the zero ring. These are elementary.
2. A field is Noetherian of dimension zero; the recorded Noetherian polynomial
   dimension theorem gives `dim P = n`. The finite-support leading-exponent argument
   proves the domain assertion, hence `(0)` is prime.
3. The four-rings theorem applies to `(P,T,P/I,T)` with identity on `T`.
   The kernel factorization makes the square commute, `t=t*1` supplies its
   finite-sum condition, and the relevant prime contracts to itself. Its conclusion
   includes finite type of the quotient-induced map, not just quasi-finiteness.
4. Surjectivity lifts prime ideal differences, preserving strictness; each lifted
   prime contains nonzero `h`, so `(0)` can be prepended. This gives the uniform
   `n-1` bound, including reducible/nonreduced quotients. This is elementary.
5. The localization-chain statement gives the bound for `R_r`. The local
   quasi-finite inequality requires only the finite type and pointwise
   quasi-finiteness already verified, and gives the bound for `T_q`.
6. Any finite prime chain ends at a prime `q`; localization bounds its length.
   The supremum remains at most `n-1`; the ring/spectrum dimension theorem identifies
   the conclusion. `proof_deps` equals the union of step `uses`.

Edge cases: zero ring (including `n=0`) is admitted; nonzero `T` with `n=0` cannot
satisfy `hker`; `n=1` gives dimension at most zero. Quotients such as
`k[x,y]/(xy)` and `k[x]/(x²)` show that no domain or reducedness is intended.
The identity polynomial map is excluded by `hker`. No finiteness of a prime set,
choice of characteristic, or equality of universes is hidden.

One-definition-per-notion: inspected the recorded LeanFinder, LeanSearch, Loogle
and grep searches, and independently searched Mathlib RingTheory, upstream
WeilConjectures and the Q95 side RingTheory/TraceFormula modules for quasi-finite
Krull-dimension and kernel statements. The nearby
`topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial` only gives `≤ n`.
The polynomial-dimension, quotient-bound and one-dimensional quasi-finite results
are ingredients, not this assertion. No duplicate exact statement was found.

Route pivot: none of the item's statement/proof dependencies occurs in
`origin/newtargets-dag:coord/route-pivot-dropped.txt`. No item repair note exists
at the specified remote-ref path. No infinity/dg/model machinery or pro-etale
substitute is used.

Findings and complete fixes:

- H11: the delivered second-reading section explicitly disclaimed having read
  anything. Replaced that placeholder with this substantive independent reading;
  preserved the Worker report.
- H8: the original proof summary omitted the polynomial-domain/dimension step and
  compressed the edge cases. Expanded it into the six node steps with named inputs.
- H9: removed imports used only by the intended future proof and changed the direct
  quasi-finiteness import from the retired Sheaf path to its recorded upstream
  module. The old import did compile; this is dependency hygiene, not a failed
  declaration or a new definition. The replacement uses only the statement imports.
- The delivery report did not record a per-file compiler invocation/result. This
  review supplies reproduced evidence below. No statement, hypothesis, node record,
  proof dependency or mathematical construction was changed.

Compiler evidence:

Ran `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q95
lem-trf-quasi-finite-polynomial-kernel-dimension-drop <file>` separately on the
immutable module and its complete corrected replacement. Both exited 0, with no
reported errors or warnings. Original output: sandbox 4.7 s, library 1.8 s,
private overlay `/dev/shm/nt-tmp/nt-local-compile-80gw3yil/.lbuild`.
Corrected output: sandbox 1.5 s, library 2.1 s, private overlay
`/dev/shm/nt-tmp/nt-local-compile-04ujbeyh/.lbuild`.
The installed wrapper currently delegates to server `nt_srv_compile.py
--wire-confirm`; it reports private overlay compilation and a library-path check.
This is the prescribed wrapper's behavior, not a direct SSH invocation by the reviewer.

Both modules have one theorem proved only by `sorry`, no definitions or local
proofs, source/blueprint module and declaration docstrings, and no lines exceeding
100 characters. No global build, live Lean edit, repository mutation, delivery or
merge was performed. Only review/fixes files were written.
