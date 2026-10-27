## Worker report

The module `Sheaf.Algebra.Lie.WeylOnlyNormalForm` states
`LieAlgebra.weylOnlyNormalForm`, with `sorry` as its entire proof. Its six helper
declarations construct exactly the quotient and canonical maps introduced in the
item's own statement. They are recorded in `lean.declarations`; no independent
notion is introduced and no new node or dependency module is needed. Every
helper is real data, using Mathlib constructions, with no postponed proof.
The existing node is changed only in `lean`.

Hypothesis and clause correspondence:

- A finite set I: `{I : Type u} [Finite I]`, for an explicitly declared arbitrary
  universe `u`. No inhabitance or decidable-equality assumption is imposed.
- An arbitrary rational matrix B: `(B : Matrix I I ℚ)`, with no diagonal,
  integrality, sign, rank, finite-type, symmetry or nondegeneracy assumption.
- Rational Lie algebras and ideals in `def-wf-lie-algebra`: Mathlib's `LieRing`,
  `LieAlgebra ℚ`, `LieIdeal ℚ`, `LieSubmodule.lieSpan`, and Lie quotient instances.
- The free Lie algebra on the three generator families: `FreeLieAlgebra ℚ
  (CartanMatrix.Generators I)`, using the existing `H`, `E`, `F` constructors.
  Its universal property is Mathlib's equivalence `FreeLieAlgebra.lift` and its
  inverse restriction along `FreeLieAlgebra.of`, not an extra hypothesis.
- The quotient by the generated ideal: `weylOnlyIdeal B` uses
  `LieSubmodule.lieSpan ℚ _` on the union of exactly four ranges, and `WeylOnly B`
  is the actual quotient by that ideal. `CartanMatrix.Relations.HH ℚ` is precisely
  `[h_i,h_j]`. `CartanMatrix.Relations.EF ℚ` is `[e_i,f_i]-h_i` on the diagonal
  and `[e_i,f_j]` off the diagonal, exactly the delta relation. The last two
  ranges are explicitly `[h_i,e_j] - B i j • e_j` and
  `[h_i,f_j] + B i j • f_j`. The plus sign in the latter gives the required
  negative Cartan action. There are no `adE`, `adF` or other relation families.
- The images `h_i,e_i,f_i` are `weylOnlyGenerator B` of the corresponding
  generator, using `LieSubmodule.Quotient.mk'` on `FreeLieAlgebra.of`.
- The free negative and positive Lie algebras are each `FreeLieAlgebra ℚ I`;
  these are separate summands with respective maps `weylOnlyNegative B` and
  `weylOnlyPositive B`. Their generator assignments are `F i` and `E i`, extended
  by `FreeLieAlgebra.lift ℚ`. Reusing the same free-algebra type for the two
  separately labelled copies does not identify elements of their summands.
- The Cartan vector space with its indicated basis is `I →₀ ℚ`, whose canonical
  basis vectors are the finitely supported unit vectors (`Finsupp.single i 1`).
  `Finsupp.linearCombination ℚ (fun i ↦ weylOnlyGenerator B (H i))` is exactly
  the map sending the coefficient vector c to the finite sum of `c_i • h_i`.
- The displayed three-summand linear map is `weylOnlyNormalFormMap B`.
  Two `LinearMap.coprod` applications map `(y,(c,x))` to
  `ι₋ y + (∑ i, c_i • h_i + ι₊ x)`, the node's formula by associativity.
  A finite direct sum of three vector spaces is represented by their product.
- Isomorphism of rational vector spaces: `Function.Bijective
  (weylOnlyNormalFormMap B)`. The map is already a bundled rational linear map,
  so bijectivity is precisely that this specified map is a linear isomorphism,
  rather than a bare existence of some unrelated isomorphism.
- Both maps injective: the next two conjuncts are `Function.Injective
  (weylOnlyNegative B)` and `Function.Injective (weylOnlyPositive B)`.
- Empty I: the final implication `IsEmpty I → ...` states `Subsingleton` for
  `FreeLieAlgebra ℚ I`, `I →₀ ℚ`, and `WeylOnly B`. The one free-algebra
  `Subsingleton` assertion applies to both separately labelled copies. These
  are nonempty additive groups, so `Subsingleton` means zero vector space.

Dependency declarations and imports:

The sole statement dependency `def-wf-lie-algebra` has status `mathlib` and no
`lean` record. I read its complete `mathlib_match` and the relevant original
signatures/docstrings: `LieRing` and `LieAlgebra` in `Mathlib.Algebra.Lie.Basic`,
`LieIdeal` in `Mathlib.Algebra.Lie.Ideal`, and
`LieSubmodule.Quotient.lieQuotientLieAlgebra` in `Mathlib.Algebra.Lie.Quotient`.
Their standard instances are used, not copied. `Mathlib.Algebra.Lie.SerreConstruction`
publicly imports Free and Quotient and supplies `CartanMatrix.Generators`, HH and
EF. Its `Matrix.ToLieAlgebra` is not used: it imposes additional Serre relations
and is parameterized by an integer matrix. The two other public imports supply
`Finsupp.linearCombination` and `LinearMap.coprod`. Neither proof prerequisite
`lem-sfb-weyl-word-operators` nor `lem-sfb-free-lie-word-embedding` has a recorded
Lean declaration in the read repository, so there is no available proof module
to import. They are named in the theorem's six-step proof docstring and the
node's existing proof dependency list is preserved.

Source and edge-case checks:

I opened Milne's PDF, physical pp.515--516 / printed pp.503--504, with pdftotext.
Its first proof displays the Weyl presentation, free negative and positive
subalgebras, and the direct sum. The PDF has the already documented misprints
`[X_i,X_i]=H_i` and a repeated X instead of Y in the Cartan relation; the accepted
node has their intended corrections. I did not change the node statement.
Bourbaki VIII §4 no.2 remains the detailed source Milne cites; the node's explicit
agent argument supplies the arbitrary-rational-matrix generality. I checked
its mechanism: varying all highest weights separates Cartan coefficients even
for singular or zero B, and exchanging e/f and negating h respects all four
relations for every B. The same-sign Jacobi and opposite-sign word inductions
use no Cartan-matrix hypothesis.

Checked I empty: no generators or relation instances; the free, Cartan and
quotient spaces vanish, and the explicit map is the zero-space isomorphism.
Checked a singleton: the two free Lie algebras are one-dimensional; for any
rational b the three brackets `[e,f]=h`, `[h,e]=b e`, `[h,f]=-b f` are consistent,
including b=0 (the three-dimensional Heisenberg algebra). Checked zero and
singular matrices with several indices: weights λ, not rows of B, separate h,
so there is no hidden rank assumption. The two displayed rational-weight
families use the correct row/column order B i j. No characteristic or
nonempty-index case is silently excluded. No STATEMENT-DISPUTED fault found.

Searches (all performed before writing the module):

- `msearch.py leanfinder`, query `Weyl only Lie algebra presentation arbitrary
  rational matrix free negative Cartan positive normal form`: eight hits,
  including `RootPairing.GeckConstruction.lieAlgebra`, `Matrix.ToLieAlgebra`,
  `CartanMatrix.Generators`, EF, adE, toSet. None states the required Weyl-only
  decomposition. The generator type and the reusable HH/EF relations were used.
- `msearch.py loogle`, query `FreeLieAlgebra, LieIdeal`: one hit,
  `CartanMatrix.Relations.toIdeal`, which also includes Serre relations.
- `msearch.py leansearch`, query `Triangular decomposition of the free Lie
  algebra quotient by Weyl relations without Serre relations`: eight hits,
  including `FreeLieAlgebra`, its instances, `Matrix.ToLieAlgebra` and
  `LieModule.IsTriangularizable`. The free construction is used; none of the
  other statements is the required normal form.
- `msearch.py grep`, query `Weyl|normal.form|Serre`, subdirectory `Algebra/Lie`:
  twelve hits in SerreConstruction, Basis/Basic, Loop, Weights/IsSimple and
  UniversalEnveloping. Reading SerreConstruction and GeckConstruction/Basic
  confirmed that their algebras differ from this Weyl-only universal quotient.
- Direct project `rg` for `Weyl|weyl|normalForm|FreeLieAlgebra` and later
  `weylOnly|WeylOnly|Weyl.only|Weyl-only|FreeLieAlgebra` in `lean/WeilConjectures`
  and `lean/Sheaf/Algebra/Lie`: only the rational Serre quotient helper was
  relevant; it quotients by the full Serre ideal and cannot serve here.
  Literal item-id search in `lean/WeilConjectures` returned no match. Direct
  `rg` for `WeylOnly|weylOnly` across Mathlib and both project roots found none.
- DAG search for `Weyl.only|Weyl-only|weylOnly|weyl_only` found this item,
  its word-operator and free-embedding prerequisites, arbitrary-basis PBW and
  its Serre-quotient parent. None supplies a recorded Weyl-only quotient or
  normal-form declaration. `tools/blueprint_refs.py search 'Weyl'` found zero
  blueprint nodes; `ancestor` reports null, as already recorded in the item.
  The latest blueprint tree was used. No repair note exists for this item.

Verification: `scompile.py Q65 lem-sfb-weyl-relations-free-normal-form` on the
one delivered module passed in both its sandbox and library-mode compilation,
with no errors or warnings. Every universe and variable is explicit and
`autoImplicit` is disabled. The only postponed proof is the named main theorem.

## Second reading by Q65

Independent clause-by-clause reading (maintainer cc reviewer; the delivered
section was a self-reread by the worker and is replaced by this one; the
worker report above is kept verbatim).

Node statement as a list, with the Lean rendering and verdict:

1. I a finite set: `{I : Type u} [Finite I]`, universe u bound by `universe u`;
   no DecidableEq/Inhabited/Fintype instance in the signature (EF's
   DecidableEq is supplied by `classical` inside `weylOnlyIdeal`). OK.
2. B an arbitrary rational matrix: `B : Matrix I I ℚ`, no further hypothesis. OK.
3. Lie algebras/ideals of def-wf-lie-algebra: Mathlib LieRing/LieAlgebra ℚ,
   LieIdeal, LieSubmodule.lieSpan, Lie quotient (the node's mathlib_match). OK.
4. Free Lie algebra on {h_i,e_i,f_i}: `FreeLieAlgebra ℚ (CartanMatrix.Generators I)`
   (Generators = H | E | F over I), which has the stated universal property
   (`FreeLieAlgebra.lift`). OK.
5. W(B) = quotient by the ideal generated by exactly the four families: I read
   Mathlib SerreConstruction.lean:90-110. `Relations.HH` = ⁅H i,H j⁆;
   `Relations.EF` = if i=j then ⁅E i,F i⁆-H i else ⁅E i,F j⁆ (= [e_i,f_j]-δ_ij h_i);
   the two explicit ranges are ⁅H i,E j⁆ - B i j • E j and ⁅H i,F j⁆ + B i j • F j,
   index order b_ij as in the node. No adE/adF (Serre) family. `WeylOnly B` is
   the genuine quotient. OK.
6. F^-, F^+ free on y_i, x_i: two copies of `FreeLieAlgebra ℚ I` as separate
   product factors. OK.
7. h^0 = ⊕ Q u_i with its basis: `I →₀ ℚ` (single i 1 basis). OK.
8. ι_- (y_i ↦ f_i), ι_+ (x_i ↦ e_i): `weylOnlyNegative/Positive` =
   `FreeLieAlgebra.lift ℚ` of the F/E generator images. OK.
9. The linear map (y,Σc_i u_i,x) ↦ ι_-(y)+Σ c_i h_i+ι_+(x): `weylOnlyNormalFormMap`
   = coprod of ι_-, `Finsupp.linearCombination` of the h_i, and ι_+. OK.
10. Isomorphism of Q-vector spaces: `Function.Bijective` of that specific
    ℚ-linear map (equivalent to it being a linear isomorphism). OK.
11. Both ι_± injective: the second and third conjuncts. OK.
12. I = ∅ ⇒ all four spaces zero: `IsEmpty I →` Subsingleton of the free algebra
    (both copies are the same type), of `I →₀ ℚ`, and of `WeylOnly B`. OK.
13. No assumption on B: none in the Lean. OK.

Edge cases: I empty (covered by clause 12, no Nonempty assumption); |I| = 1 with
b = 0 (Heisenberg case, statement true, no exclusion); singular B (weights λ
separate the h_i, no rank hypothesis); universe of I arbitrary.

Searches: Mathlib Algebra/Lie grep for FreeLieAlgebra/CartanMatrix.Generators/
Serre: only SerreConstruction (`Matrix.ToLieAlgebra`, integer matrix plus Serre
relations) and GeckConstruction (finite root pairing): not this notion. Project
live/side-live lean: only `RationalSerrePresentation.lean`, which quotients by
the full Serre ideal for an integer Cartan matrix: not this notion. The item is
not landed with a `lean` record by any other group. No duplicate definition.

Records: only the `lean` field differs from the live node; `lean.statement` is a
verbatim substring of the module; module docstring and every declaration carry
the source place and `(blueprint: lem-sfb-weyl-relations-free-normal-form)`;
the theorem docstring carries the six proof steps; helpers are real data; the
only `sorry` is the main theorem. No mismatch in the Lean; no change made to it.
