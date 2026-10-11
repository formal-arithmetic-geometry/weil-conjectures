## Worker report

The module `lean/Sheaf/Paper/KoszulDifferential.lean` states
`ExteriorAlgebra.koszul_differential`. It binds a commutative ring `R`, an
`R`-module `E`, and an `R`-linear form `φ : E →ₗ[R] R`, and existentially
provides an `R`-linear endomorphism `D` of `ExteriorAlgebra R E`.

The first conjunction renders clause (i): `D 1 = 0` and the recursion
`D (ι v * x) = algebraMap (φ v) * x - ι v * D x`; the following quantified
conjunction states uniqueness among all linear maps satisfying those two
conditions. The next clause renders (ii)'s value on degree one. Degree zero
is represented explicitly by `Submodule.map D (⋀[R]^0 E) ≤ ⊥`, while positive
degrees are represented by
`Submodule.map D (⋀[R]^(n+1) E) ≤ ⋀[R]^n E`; this preserves the node's
convention `⋀^(-1) = 0` without identifying negative indices with natural
number subtraction. Clause (iii) is the alternating formula for every
`n+1` inputs, using `ExteriorAlgebra.ιMulti` and `Fin.succAbove` to omit the
summand's input. Clause (iv)'s graded Leibniz identity is stated for every
homogeneous subtype `x : ⋀[R]^m E` and arbitrary `y`; its final quantified
conjunction states uniqueness among linear maps satisfying that identity and
the specified values on generators.

The dependency `def-weil-pbc-exterior-algebra` is supplied by Mathlib:
`ExteriorAlgebra`, `ExteriorAlgebra.ι`, `ExteriorAlgebra.exteriorPower`
(notation `⋀[R]^n`), `ExteriorAlgebra.ιMulti`, and the grading declarations.
The existence dependency `lem-weil-pbc-koszul-differential-existence` is also
a Mathlib leaf, via `CliffordAlgebra.contractLeft`,
`contractLeft_one`, and `contractLeft_ι_mul`; no project dependency module is
needed.

Edge cases checked: degree zero is mapped to the zero submodule; the explicit
formula is indexed by `n+1`, hence covers exactly `n ≥ 1` and has the empty
sum behavior at no input only through the separate degree-zero clause; the
submodule inclusions allow the zero module and arbitrary commutative rings,
including characteristic two; `Fin.succAbove` handles omission for every
positive degree.

Searches made: `msearch.py ... leanfinder` for “Koszul differential on an
exterior algebra” returned no exact project declaration; `msearch.py ...
loogle` for `CliffordAlgebra.contractLeft, ExteriorAlgebra.exteriorPower`
returned only the contraction candidates; `msearch.py ... grep` and `rg` over
Mathlib and `WeilConjectures` found no Koszul differential statement. The
Mathlib source files `LinearAlgebra/CliffordAlgebra/Contraction.lean`,
`LinearAlgebra/ExteriorAlgebra/Basic.lean`, and `ExteriorAlgebra/Grading.lean`
were read to verify the recorded declarations and signatures.

No `STATEMENT-DISPUTED` issue or node fault was found.


## Earlier second reading (a previous round; superseded)

I reread the node and the module independently. The binders match the node's
commutative ring, module, and linear form. Clause (i) is rendered by the
existential linear endomorphism, its unit equation, recursion, and quantified
uniqueness. Clause (ii) has the generator value and separates degree zero
(mapping into bottom) from positive degrees, exactly implementing the node's
negative-degree-zero convention. Clause (iii) uses `ιMulti` and
`Fin.succAbove`, which is the same omitted-factor wedge and has the required
sign. Clause (iv) quantifies homogeneous `x` and arbitrary `y`, with the
algebra-map form of the scalar sign, and includes uniqueness from the
Leibniz rule and generator values. All objects are the Mathlib exterior
algebra and its graded submodules; no extra hypotheses or cases were added.


## Second reading by M1

I opened the node, its source on the server, both dependency nodes, and the
Mathlib declarations they record. Stacks `more-algebra.tex`, lines 6558–6595,
Definition 0622 and its following formula, works over a ring with an arbitrary
module and a linear form; the subsequent finite-free assumption is optional
and is not part of this definition. I also read `algebra.tex`, lines 2165–2200
(Tag 00DM), for the exterior-algebra notion. The tag table confirms both labels.

Object/hypothesis/conclusion inventory, matched clause by clause:

- R is a commutative ring: `(R : Type u) [CommRing R]`. Exact; no domain,
  nontriviality, field, characteristic, or Noetherian hypothesis.
- E is an arbitrary R-module: `(E : Type v) [AddCommGroup E] [Module R E]`.
  Exact; neither freeness nor finite generation is assumed.
- φ is an R-linear form E → R: `(φ : E →ₗ[R] R)`. Exact.
- The algebra, generators, product, graded pieces, and wedge products are
  `ExteriorAlgebra R E`, `ExteriorAlgebra.ι R`, multiplication, `⋀[R]^n E`,
  and `ExteriorAlgebra.ιMulti R n`. Exact recorded dependency notions:
  Basic.lean:60 defines the algebra as CliffordAlgebra at Q = 0; its quotient
  relation in CliffordAlgebra/Basic.lean:63 kills v*v; Basic.lean:69 gives ι;
  Basic.lean:79 gives the powers of its range; Basic.lean:271 and :300 give
  the alternating product in the original input order. Grading.lean:72 gives
  the direct-sum grading. These realize `def-weil-pbc-exterior-algebra`,
  not a private exterior algebra or only a finite/free specialization.
- (i), existence of an R-linear endomorphism: the outer `∃ D : ... →ₗ[R] ...`.
  Exact, with one D shared by all clauses.
- (i), unit and recursion for every v and x: `D 1 = 0` and the immediately
  following `∀ (v : E) (x : ExteriorAlgebra R E)` equality. Exact:
  `algebraMap ... (φ v) * x` is scalar multiplication by φ(v).
- (i), uniqueness under precisely these equations: the first `∀ D'`, with
  the unit and recursion as antecedents and `D' = D` as conclusion. Exact;
  uniqueness does not require D' to satisfy the later clauses.
- (ii), generator value: `∀ v, D (ι R v) = algebraMap ... (φ v)`. Exact.
- (ii), all degrees including the negative-degree-zero convention:
  `Submodule.map D (⋀[R]^0 E) ≤ ⊥` and
  `∀ n : ℕ, Submodule.map D (⋀[R]^(n + 1) E) ≤ ⋀[R]^n E`.
  Exact, avoiding the incorrect natural-number subtraction at zero.
- (iii), every positive length and every vector list: `∀ n : ℕ,
  ∀ v : Fin (n + 1) → E`, the displayed equality on `ιMulti`. The source
  length is n+1. The summation over `Fin (n+1)` enumerates every factor;
  `v ∘ i.succAbove` omits exactly that factor while preserving order
  (Data/Fin/SuccPred.lean:509). The original exponent `i.1 + 1` was WRONG:
  source position j is i.val+1, so source exponent j+1 is i.val+2.
  Repaired to `i.1 + 2`. The repaired clause is exact.
- (iv), graded Leibniz identity: `∀ m : ℕ, ∀ x : ⋀[R]^m E,
  ∀ y : ExteriorAlgebra R E`, the displayed identity with sign `(-1)^m`.
  Exact: only x is required homogeneous and y is arbitrary.
- (iv), uniqueness with the identity and generator values: the final `∀ D'`
  takes precisely those two antecedents and concludes `D' = D`. Exact;
  the unit equation is not an extra hypothesis here. The degree conclusion
  for D is already clause (ii).

Edge cases: the formula's Lean n=0 is source length one. After the sign repair,
its only term is +φ(v)*1, since `ιMulti R 0` is 1; before repair it was -φ(v).
For example R=ℤ, E=ℤ, φ=id, v=1 contradicted the generator-value clause.
For length two the repaired signs are +,-. The empty wedge is 1 and is covered
by the unit and degree-zero clauses; (iii) requests only positive lengths.
The zero module, zero linear form, zero ring, arbitrary characteristic
(including two), and homogeneous zero elements are all permitted. The
uniqueness argument subtracts D'(1) and never divides by two. Independent
universes u and v are explicitly bound; no smallness or same-universe
restriction is imposed. Schemes/empty schemes do not enter this statement.

Independent searches (using different wording from the worker):

- `msearch.py ... leansearch "interior multiplication by a linear functional
  on exterior algebra graded antiderivation"`: service returned Internal
  Server Error; recorded as unavailable, with no mathematical verdict.
- `msearch.py ... leanfinder "An exterior algebra contraction lowers
  homogeneous degree and satisfies the graded Leibniz rule for a linear
  functional"`: returned Clifford contraction, its recursion, auxiliary
  declarations, and `ExteriorAlgebra.liftAlternating_ι_mul`; none states
  all clauses or the homogeneous degree and general Leibniz conclusion.
- `msearch.py ... loogle '"contractLeft"'`: Clifford left contraction and
  associated identities, plus unrelated tensor pairing declarations.
- `msearch.py ... grep 'koszul|interiorProduct|antiderivation|contractLeft'
  LinearAlgebra`: contraction candidates only. Independent `rg` with
  `koszul|antiderivation|interior.?product|koszul_differential|contractLeft`
  over WeilConjectures, repository lean/Sheaf, and dag/lean_names_upstream.json
  found Koszul braidings, a projective-line short exact sequence, tensor
  evaluation maps, and syzygy statements, not this theorem.

I opened Contraction.lean:84, :125–126, and :178:
`CliffordAlgebra.contractLeft` is a dual-to-endomorphism linear map with the
unit equation and required recursion. Specializing Q=0 gives exactly the
existence dependency `lem-weil-pbc-koszul-differential-existence`. It does
not already provide the entire statement, so the item's module stays.
There are no new definition nodes, dependency modules, or statement_change
in this delivery, and no missing notion requires one. The mathematical
node is correct; only its Lean rendering needed the sign correction.

Other repairs: expanded the theorem docstring into all six proof steps,
naming both dependency nodes and describing the induction base cases,
spanning arguments, sign shift, Leibniz regrouping, and uniqueness reduction.
Added the standard copyright/license/authorship header. The theorem still
has exactly one `sorry`; nothing is proved and no definition is introduced.
The contraction import supports the documented existence construction; the
grading import supplies the homogeneous pieces and direct-sum interpretation.
The node's `lean.statement` was synchronized verbatim with the repaired
signature; all other node fields are unchanged. All variables and universes
are explicitly bound and lines are at most 100 characters.

Validation: `scompile.py M1 lem-weil-pbc-koszul-differential
.../lean/Sheaf/Paper/KoszulDifferential.lean` compiled the 99-line module on
the server in 1.6 seconds, exit code 0, with no errors or warnings.
