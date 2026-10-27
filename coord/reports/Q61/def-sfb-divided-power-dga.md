## Worker report

Item: `def-sfb-divided-power-dga`. Module:
`Sheaf.RingTheory.DividedPowerDGA`. Main declaration:
`GradedAlgebra.DividedPowerDGA`. The module defines the complete DGA structure,
its component differentials, its integer-indexed chain complex and homology, and
`GradedAlgebra.DividedPowerDGA.IsPolynomial` for the underlying divided-power algebra.
Only the item's `lean` field changes. No new nodes, dependency repairs or statement
corrections are needed.

Read the item and all five statement-dependency nodes, their recorded declarations
and docstrings, and Stacks `literature/stacks-project/dpa.tex`, section Tate
resolutions, especially 09PF, 09PG, 09PH, 09PI, 0F4I and 09PJ (lines 933--1100).
Also read the explanation of polynomiality after `lemma-tate-resolution` and at
the start of the proof of the lifting lemma (lines 1222--1225, 1345--1353).
The latest blueprint has no separate definition replacing these source notions.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| R is an arbitrary commutative ring | Explicit `{R : Type u} [CommRing R]`; no domain, characteristic or nontriviality hypothesis |
| Associative unital R-algebra A | Explicit `{A : Type v} [Ring A] [Algebra R A]`; A itself is not assumed commutative |
| Nonnegative direct-sum grading, unit and scalars in degree zero, products add degrees | `𝒜 : ℕ → Submodule R A` and the recorded Mathlib `[GradedAlgebra 𝒜]` |
| Zero components in negative degrees | The dependency's `integerComponent 𝒜` uses `⊥` at every `Int.negSucc` |
| Signed homogeneous commutativity | `[IsStrictlyGradedCommutative 𝒜]`, field `signed_comm` |
| Odd homogeneous squares are zero | The same class, independent field `odd_sq_zero`, including characteristic two |
| The positive even part and the full even part | The dependency's `positiveEvenIdeal 𝒜` in `evenSubalgebra 𝒜` |
| Graded divided powers on that ideal | `DividedPowerDGA` extends the recorded `GradedDividedPowers 𝒜` |
| gamma_0(x) = 1 | Inherited `DividedPowers.dpow_zero` for `x ∈ positiveEvenIdeal 𝒜` |
| gamma_1(x) = x | Inherited `dpow_one` |
| gamma_n(x) has degree 2in for x of degree 2i | Inherited `GradedDividedPowers.dpow_homogeneous`; positive operations land in the ideal by `dpow_mem` |
| Product of divided powers with binomial coefficient | Inherited `mul_dpow`, with a natural-number cast in the even ring |
| gamma_n(ax) = a^n gamma_n(x), a any even element | Inherited `dpow_mul`; its scalar is any `evenSubalgebra 𝒜` element, not just an R-scalar |
| The sum formula | Inherited `dpow_add`, summing over `Finset.antidiagonal n`, exactly the pairs (b,n-b) |
| The iterated-power factorial quotient | Inherited `dpow_comp`, with `Nat.uniformBell n m`; `Nat.uniformBell_mul_eq` identifies this integer with the stated quotient |
| Higher powers of products of homogeneous odd elements vanish | Inherited `dpow_odd_mul`; its even lift z is constrained to equal x*y |
| R-linear differential | `d : A →ₗ[R] A` |
| d maps A_i to A_(i-1), including d(A_0)=0 | `degree` for every integer i maps component i+1 to i; take i=-1 for degree zero |
| d squared is zero | `square_zero : ∀ x : A, d (d x) = 0` |
| Signed Leibniz identity | `leibniz`, for all homogeneous x in degree i and y in degree j, with sign `(-1 : A)^i` |
| d(gamma_n(x)) = d(x) gamma_(n-1)(x), n>=1 | `compatible`, for every positive n and every element of the whole positive even ideal; no homogeneous restriction |
| Underlying chain complex | `componentDifferential` is the actual restriction of d; `chainComplex` uses `ChainComplex.of` on integer components |
| H_i = kernel of outgoing d modulo image of incoming d | `homology D i := D.chainComplex.homology i`, the recorded `HomologicalComplex.homology`; the imported ModuleCat homology API identifies it with exactly that quotient |
| Polynomial degree-zero starting algebra on any set of variables | In `IsPolynomial`, an existential `J₀ : Type v` and actual `MvPolynomial J₀ R ≃ₐ[R] (B 0).Carrier` |
| Degree-zero concentration, hence zero positive even ideal and trivial powers initially | `(B 0).grade n = if n = 0 then ⊤ else ⊥`; the existential `γ 0` is forced on the zero ideal by the ordinary divided-power axioms |
| Successive adjunctions, each in one positive degree | The sequence `e : ℕ → ℕ`, positivity `∀ k, 0 < e k`, and `p k : SetPresentation (B k) (γ k) (e k) (J k) (B (k+1))` |
| Sets of exterior variables in odd degree | `SetPresentation.finite` uses `FiniteTower.step.oddModel : OddPresentation`; coordinates are pairs, multiplication has the graded sign and T squared is zero |
| Sets of divided-power variables in even degree | The same presentation uses `Step.evenModel : EvenPresentation`, free-module coordinates on divided symbols, degree ae and binomial multiplication |
| T^[0]=1, T^[1]=T, T^[a]=gamma_a(T) | `EvenPresentation.unit_coordinates`, `Step.even_variable`, `Step.even_normalized`, and the set-level `SetNormalized`; `SetPresentation.divided_symbols` identifies the finite and set symbols |
| Unique extended divided powers | The predicate requires the extension and normalization `SetNormalized` supplied by the dependency; uniqueness is the dependency's `set_variables`, not an extra arbitrary choice of operations |
| Finite or infinite sequence | A countable tower with arbitrary positive degrees; finite towers are padded with empty J k and constant later stages |
| The infinite model is the increasing union | `UnionPresentation` provides injective maps into the given algebra, compatible with the step inclusions, covering every element and giving exactly its union grading |
| Isomorphism as graded R-algebras with divided powers | The algebra itself is allowed as the presented union, and `Preserves (q.into k) (γ k) D.toGradedDividedPowers` identifies its divided powers with every stage; transporting a presentation along any graded divided-power isomorphism gives exactly this data |
| Polynomiality is a condition only on the underlying graded divided-power algebra | `IsPolynomial` uses `D.toGradedDividedPowers`, never `D.d` or the differential laws |

The single global linear differential is equivalent to a family on components:
restriction gives that family; conversely, the internal direct-sum decomposition
extends a linear family uniquely to A. The square-zero and Leibniz identities on
components extend by linearity and bilinearity. This is an encoding of the stated
objects, not a hypothesis about a different algebra.

The presentation stages and variable labels live in A's carrier universe v. This
is not a mathematical cardinal bound: the stages are isomorphic to their images
inside A by the injective union maps. When R is nonzero, distinct polynomial or
adjoined variables are distinct elements of A, so their sets can be indexed in
that universe too. In the zero-ring case the whole algebra and all stages are
zero and all sets may be taken empty. The coefficient ring universe u remains
independent; an algebra equivalence from `MvPolynomial J₀ R` is allowed between
different universes.

Dependencies used, with their recorded interfaces opened:

- `Sheaf.RingTheory.NonnegativeStrictGradedAlgebra`:
  `GradedAlgebra.IsStrictlyGradedCommutative`, `integerComponent`,
  `evenSubalgebra`, `positiveEvenIdeal`. This reuses the given internal grading,
  including the parity construction and its inherited commutative even ring.
- `Sheaf.RingTheory.GradedDividedPowers`:
  `GradedAlgebra.GradedDividedPowers`, its inherited ordinary `DividedPowers`
  fields, `dpow_homogeneous`, and `dpow_odd_mul`.
- `Sheaf.RingTheory.DividedPowerVariableAdjunction`:
  `GradedAlgebra.VariableAdjunction.AlgebraData`, `SetPresentation`,
  `SetNormalized`, `UnionPresentation`, and `Preserves`. Read also `Hom`,
  `OddPresentation`, `EvenPresentation`, `EvenNormalized`, `Step`, `FiniteTower`,
  and all four adjunction/union statements to verify the presentation semantics.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology`; `ChainComplex.of` gives the actual complex.
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` supplies module homology
  and `CategoryTheory.ShortComplex.moduleCatHomologyIso`, whose target is
  explicitly the kernel modulo the image into that kernel.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; also read the recorded
  universal-property declarations `MvPolynomial.aeval` (Eval) and
  `MvPolynomial.algHom_ext` (Basic). The polynomiality clause needs the actual
  polynomial algebra, not a second universal-property predicate.

Edge cases checked against the definitions:

- Degree zero: `degree (-1)` forces d(A_0)=0 because the target is `⊥`.
  The integer-indexed complex also has zero objects at every negative degree.
- n=1: compatibility reads d(x)=d(x)*1 by the inherited first and zeroth
  divided-power laws. n=0 is not erroneously included in compatibility.
- Positive even elements need not be homogeneous; compatibility uses the entire
  ideal. The odd-product vanishing axiom remains restricted to homogeneous
  factors, allowing a nonzero gamma_2 of a sum of two odd products.
- Characteristic two: odd-square zero is still separately required; no division
  by 2 or by a factorial occurs. In every characteristic the iterated-power
  coefficient is the natural integer `uniformBell`, already in the dependency.
- Empty polynomial-variable set gives R in degree zero; empty adjunction sets
  are permitted by the recorded finite-subset presentation. No generators or
  positive-degree elements are required to exist.
- Pure degree-zero polynomial algebras use only empty adjunctions; finite
  nonempty sequences are included by empty tails; infinite sequences retain
  exactly the compatible increasing-union condition.
- The zero coefficient ring and zero algebra are permitted. No nontriviality,
  Noetherian, finite-generation, or differential filtration hypothesis is added.
- A non-polynomial DGA is allowed: polynomiality is a separate predicate, not a
  field required of every divided-power DGA.

Searches actually run through the prescribed `msearch.py` wrapper:

- LeanFinder: `A nonnegative strictly graded commutative differential graded
  algebra with compatible divided powers`. Eight hits, including
  `ExteriorAlgebra.gradedAlgebra`, ordinary `DividedPowers`, rational/square-zero
  ideal divided powers and `GradedAlgebra`; no compatible divided-power DGA.
- Loogle: `"DividedPowers", "differential"`. Zero hits.
- Mathlib grep: `DividedPowerDGA|DividedPowerDga|DifferentialGraded|divided.*differential`.
  Zero hits.
- LeanSearch: `A strictly graded commutative differential graded algebra with
  compatible divided powers`. Eight hits on graded tensor commutation, ordinary
  ideal divided powers and exterior grading; no definition of the combined DGA.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `DividedPowerDGA|DividedPowerDga|DividedPower.*Differential|Differential.*DividedPower`
  returned no match. Searched the same names in all Mathlib source too: no match.
- Direct `rg` for `def-sfb-divided-power-dga` in `lean/WeilConjectures` returned
  no match. The dependency modules were read and reused rather than duplicated.

No STATEMENT-DISPUTED issue remains. The known 09PI misprint about iterated powers
was already corrected in the accepted DAG and its dependency; this module uses
that dependency unchanged. It does not alter any target or node statement.

The sole postponed theorem is
`GradedAlgebra.DividedPowerDGA.componentDifferential_comp`. It is the square-zero
well-definedness assertion for the chain complex already named in this node;
its docstring gives the complete proof by evaluation and subtype injectivity.
All definition data, including the differential restrictions and the chain
complex, are written explicitly. No object is selected from a sorry existence
proof. Every variable and universe is bound, with `autoImplicit false` enabled.

Validation: compiled the module with `scompile.py Q61 def-sfb-divided-power-dga`
against the live published library, in both sandbox and library module modes.
Both compiles were clean (only the permitted postponed theorem). The final
import header and delivery are additionally checked by the prescribed dry run.

## Second reading by Q61

Reopened the complete node, each recorded dependency interface and the finished
Lean module for a second clause-by-clause pass. This is the worker's second
reading; the maintainer supplies the independent delivery review.

Checked in particular that A has `Ring`, not `CommRing`; the coefficient ring
alone is commutative; the grading is the dependency's actual internal grading;
the inherited strictness retains odd squares in characteristic two; the divided
powers include the integer iterate coefficient and vanishing on homogeneous odd
products; `compatible` includes inhomogeneous positive even inputs; and the
integer differential sends degree zero to zero. Confirmed that the homology is
taken from this differential, not from an arbitrary complex.

For polynomiality, followed `SetPresentation.finite` to both parity-dependent
free-module coordinate presentations, the normalized even powers, the label and
symbol comparison maps, and the union's injectivity, compatibility, coverage and
grading fields. Checked that the polynomial starting algebra has its actual
MvPolynomial algebra equivalence and all positive components zero. Confirmed
that empty sets admit the finite case and that the union maps preserve the given
powers. There is no requirement that the differential preserve the chosen tower.
No statement mismatch was found. Added explicit public imports of both recorded
underlying-structure modules before final validation so every statement
dependency is directly visible in the delivered header.
