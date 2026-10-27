## Worker report

The module `Sheaf.RingTheory.GradedDividedPowers` defines
`GradedAlgebra.GradedDividedPowers` for a commutative coefficient ring `R`, a ring
`A` with an `R`-algebra structure, and a nonnegative grading `𝒜` carrying
`GradedAlgebra` and the dependency's `IsStrictlyGradedCommutative` instance. It
extends Mathlib's `DividedPowers (positiveEvenIdeal 𝒜)`, whose underlying operation
is the map on the positive even ideal and whose `dpow_null` extension is zero
outside that ideal.

The node's map clause is rendered by the inherited `DividedPowers.dpow`; its
positive ideal-valuedness is `DividedPowers.dpow_mem`, and the convention
`γ₀(x)=1` is `DividedPowers.dpow_zero`. The clauses `γ₁(x)=x`,
`γ_n(x)γ_m(x)=binom(n+m,n)γ_{n+m}(x)`,
`γ_n(ax)=a^nγ_n(x)`, the divided-power addition formula, and the composition
formula are respectively the inherited fields `dpow_one`, `mul_dpow`, `dpow_mul`,
`dpow_add`, and `dpow_comp`; Mathlib's `antidiagonal` sum is the coefficient-free
form of the addition axiom, and `Nat.uniformBell n m` is the integer factorial
quotient in the composition clause. Natural-number coefficients act in the even
subalgebra by its existing cast, hence by repeated addition rather than division.
The even-scalar in `dpow_mul` is an element of `evenSubalgebra 𝒜`, and its second
argument is an element of `positiveEvenIdeal 𝒜`, exactly the two objects in the
source clause.

The grading clause is the field
`dpow_homogeneous`: for positive `n` and positive `i`, an element `x` of the even
subalgebra lying in `𝒜 (2*i)` has `dpow n x` in `𝒜 (2*i*n)`. The two odd homogeneous
inputs and the condition `n > 1` are the hypotheses of `dpow_odd_mul`; its subtype
`z : evenSubalgebra 𝒜` is required to have underlying value exactly `x*y`, so the
conclusion is precisely `γ_n(x*y)=0`. The extra subtype only records the even
ambient object in which Mathlib's operation is defined; subtype proof irrelevance
makes it the same element as the product. No differential is present.

The statement dependency used is `Sheaf.RingTheory.NonnegativeStrictGradedAlgebra`,
with declarations `GradedAlgebra.IsStrictlyGradedCommutative`,
`GradedAlgebra.evenPart`, `GradedAlgebra.positiveEvenPart`,
`GradedAlgebra.evenSubalgebra`, and `GradedAlgebra.positiveEvenIdeal`. The ordinary
operation is imported from `Mathlib.RingTheory.DividedPowers.Basic`.

Edge cases checked: `n=0` is handled by `dpow_zero` and is excluded from the
homogeneity clause; `n=1` is allowed in the homogeneity clause and is the identity
case; `i=0` is excluded exactly where the source says positive even degree; zero
inputs and the zero positive ideal use Mathlib's zero-ideal conventions; odd
products are required to be homogeneous and only higher powers (`n>1`) vanish;
characteristic two is covered by the dependency's independent odd-square-zero
condition. The factorial coefficients are natural numbers, so no division in `R`
is introduced.

Searches for an existing declaration were made with `msearch.py`:

- LeanFinder query “Divided power structure on a strictly graded commutative algebra
  preserving homogeneous degrees and vanishing on products of odd homogeneous
  elements”: only `GradedAlgebra` and unrelated Clifford/exterior grading results;
  no match.
- LeanSearch query “Divided powers on a graded commutative algebra preserving degrees
  and vanishing on odd homogeneous products”: ordinary `DividedPowers` results only;
  no graded structure.
- Loogle query `"DividedPowers", "graded"`: zero hits.
- grep query `divided.*power.*grad|grad.*divided.*power|dpow.*degree` in Mathlib:
  no graded divided-power declaration (the hits were unrelated class-number files).
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for graded/divided-power names and the node id: no existing project or upstream
  declaration.

## Second reading by Q14

I reread the node and the module against Stacks Tag 09PG. The source's seven
conditions are all present: the five ordinary divided-power identities and the
`γ₀` convention come from the inherited Mathlib structure, while degree
multiplication and vanishing on products of homogeneous odd elements are the two
new fields. The source's positive-even domain is exactly `positiveEvenIdeal 𝒜`;
its even ambient ring is `evenSubalgebra 𝒜`. The module restricts the odd-product
condition to homogeneous components `𝒜 (2*i+1)` and `𝒜 (2*j+1)` and to `n>1`, and
adds no differential or extra hypothesis. The `z` subtype is uniquely determined
by its equality to the product, so it does not change the clause. The zero and
characteristic-two cases remain included by the inherited structure and the
strict-commutativity dependency.
