## Worker report

The module `Sheaf.RingTheory.DividedPowerVariableAdjunction` states all four clauses of
`lem-sfb-divided-power-variable-adjunction`. The primary declaration is `odd_variable`;
`lean.declarations` additionally records `even_variable`, `finite_order_comparison`,
`set_variables`, `increasing_union`, and all presentation helpers. Each theorem has exactly
`sorry` as its proof and a source/proof docstring. There are no postponed definition bodies.

Dependencies read and used:

- `Sheaf.RingTheory.NonnegativeStrictGradedAlgebra`: `GradedAlgebra.IsStrictlyGradedCommutative`,
  `integerComponent`, `oddPart`, `evenSubalgebra`, `positiveEvenIdeal`, and the parity
  constructions inherited by `GradedDividedPowers`.
- `Sheaf.RingTheory.GradedDividedPowers`: `GradedAlgebra.GradedDividedPowers`, its ordinary
  `DividedPowers` projection and `dpow`. This is the exact recorded structure, including
  homogeneous degrees and the odd-product axiom, not a commutative-algebra substitute.
- Mathlib: `GradedAlgebra`, `Submodule`, `AlgHom`, `LinearEquiv`, `Finsupp`, and
  `Nat.uniformBell`. `Nat.uniformBell_mul_eq` says
  `uniformBell n a * a!^n * n! = (n*a)!` for positive a. Thus the displayed coefficients
  are the node's integers acting by repeated addition, without division in R.

The statement dependencies both have usable published records. The two theorem-only proof
inputs `lem-sfb-split-square-zero-divided-powers` and
`lem-sfb-ordinary-pd-polynomial-extension` have no Lean modules in their current node records;
their natural-language uses are carried verbatim in the proof docstrings. They are not
needed to type the statement and no substitute theorem or axiom is introduced.

Clause and hypothesis correspondence:

- `R : Type u`, `[CommRing R]`; `AlgebraData R` contains exactly a carrier with `Ring`,
  `Algebra R`, `grade : ℕ → Submodule R`, `GradedAlgebra grade` and
  `IsStrictlyGradedCommutative grade`. This is just a dependent package of the recorded
  dependency interfaces, so it covers every possibly noncommutative strictly graded algebra.
  `γ : GradedDividedPowers A.grade` is the given structure. `he : 0 < e` represents the
  positive integer degree; `Odd e` and `Even e` select the two cases.
- (1) `OddPresentation.coordinates` is the free-module presentation A ⊕ AT;
  `inclusion_coordinates` is a ↦ (a,0), and hence implies injectivity. Its homogeneous
  multiplication field is exactly (a,b)(c,d) = (ac,ad+(-1)^j bc). Bilinearity comes from
  the R-algebra structure and the linear coordinates, so homogeneous c determines every
  product by its finite graded decomposition. `grading` gives A_m ⊕ A_(m-e)T using
  `integerComponent` for negative degrees. Unit coordinates give 1=(1,0). Thus T=(0,1)
  has T²=0 and the specified commutation law. `odd_variable` asserts existence of this
  presentation, its strict grading, and δ. `Preserves` is restriction to γ on the positive
  even ideal, for every n. The quantified δ' clause is uniqueness among ALL extensions.
  The final clause is precisely δ_n(x+yT)=γ_n(x)+γ_(n-1)(x)yT for n>0, positive-even x
  and arbitrary odd y. The variable z names the unique even-subalgebra element with those
  coordinates; it does not impose a new condition on x or y.
- (2) `EvenPresentation.coordinates` is the direct sum of copies of A indexed by ℕ,
  represented by `ℕ →₀ A`. Its multiplication field states the binomial rule on every
  pair of coefficient monomials. The linear coordinates and distributivity determine the
  product on all finite sums. `unit_coordinates` and `inclusion_coordinates` identify
  T^[0] with 1 and the coefficient inclusion. `grading` is exactly the sum of the
  A_(m-ae)T^[a], including the zero negative components. `EvenNormalized` is
  δ_a(T)=T^[a] for every a>0. `even_variable` gives an extension and uniqueness among
  extensions satisfying this normalization. Its final two clauses give the iterate formula
  and the arbitrary-even-coefficient formula with `Nat.uniformBell n a`, for n,a>0.
- (3) `Step` packages precisely one odd or even presentation, its generator, coefficient
  inclusion, and the extended divided powers. `FiniteTower` is a finite sequence of such
  adjunctions with the composite inclusions. The degree e is fixed across the tower.
  `finite_order_comparison` quantifies over two towers and a permutation of their labels;
  it asserts a unique bijective graded algebra map preserving divided powers and fixing
  coefficients and labelled generators. Preservation automatically fixes every even divided
  symbol, as required in the node. `SetPresentation` presents the directed union over ALL
  `Finset J`: each finite tower is labelled bijectively by its finite subset, embeds
  injectively in B, has increasing ranges, and the ranges cover B. Its grading is explicitly
  the union grading. Generator and even divided-symbol equations implement the canonical
  identifications. `set_variables` allows an arbitrary `J : Type w`, including empty J;
  the result carrier lies in `Type (max v w)` to accommodate the entire set. It gives the
  unique extension with the even-generator normalization and its compatibility with each
  finite stage. Every finite presentation uses actual data; none is selected by choice
  from a postponed mere-existence proof.
- (4) `A : ℕ → AlgebraData R`, `γ k` are the given stages and divided powers.
  `e k`, `he k`, `J k`, and `p k` say each successor is obtained by (3);
  `hp k` says its given divided powers are exactly the prescribed extension. Each step
  may have its own positive degree, as allowed by successive uses of (3).
  `UnionPresentation` has injective compatible inclusion maps, covers every element, and
  specifies membership in its grading by membership in one stage's component.
  `increasing_union` asserts existence of this nonnegative strictly graded union and
  exactly one graded divided-power structure restricting to every γ k.

Sources read: Stacks `dpa.tex`, section-tate, lines 951–1089 (09PF, 09PG, 09PH, 09PI, 0F4I),
and the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. The item is a supporting
node, not the blueprint unit statement. The node's correction of the source iterate
coefficient and the divided-power qualification on order comparisons are retained exactly.
No statement correction, new node or dependency repair was necessary. The presentation
records are helpers belonging to this node's specified constructions, not new independent
mathematical notions. `AlgebraData` repackages existing definitions rather than redefining
any of their axioms.

Edge cases checked before/following writing:

- Empty finite tower (n=0) and empty J give just the coefficient algebra; finite-order
  comparison fixes coefficients, and normalization is vacuous for J empty.
- The zero ring and zero positive-even ideal are admitted: coordinate equivalences become
  equivalences of zero modules and no nonzero-generator hypothesis appears.
- Characteristic two remains valid: strict commutativity retains the independent odd-square
  axiom. No inference from 2x²=0 is used and no characteristic restriction is imposed.
- e=1 is the least odd degree, e=2 the least positive even degree. Degree zero coefficients
  and m<e are included through `integerComponent`. Degree e=0 is excluded exactly by the node.
- For n=1 the odd formula gives x+yT, including x=0 because γ₀(0)=1 in the positive ideal.
  For n>1, x=0 yields vanishing of the square-zero part as intended.
- The iterate coefficient at n=a=2 is 3, not 1. At n=1 or a=1 it is 1; no field or
  invertibility assumption enters any formula.
- Products of homogeneous odd elements vanish under higher powers; sums of distinct odd
  products are not required to vanish. The recorded dependency retains this distinction.
- Arbitrary index universes are accommodated by max v w for set adjunctions; countable
  unions of stages of universe v remain in universe v. Ring universe u is independent.

Searches performed using the prescribed wrapper:

1. LeanFinder: "Adjoining exterior odd variables and even divided power variables to graded
   divided power algebras". Eight hits: exterior/Clifford gradings and generator lifts;
   none is this extension theorem.
2. Loogle: `"DividedPowers"`. Twelve hits: ordinary ideal divided powers and its API;
   no graded-variable adjunction theorem.
3. Mathlib grep: `DividedPowerAlgebra|graded.*divided|divided.*graded`, subdirectory
   `RingTheory`. Five hits in `DividedPowerAlgebra/Init.lean`: its ungraded universal algebra
   does not supply these graded operations or this extension theorem.
4. LeanSearch: "Graded divided power algebra extension by exterior and divided power
   indeterminates". Eight hits: exterior grading, GradedAlgebra, ordinary divided powers,
   and graded tensor products; none states this result.
5. Direct project searches: `rg -n 'divided.power|DividedPower|StrictGraded'` over
   `lean/WeilConjectures` and `lean/Sheaf`, plus the item id over `lean/WeilConjectures`.
   Only the two dependency modules and unrelated Kostant/Lie divided-power material appeared;
   there is no existing declaration for the four clauses or their presentations.

Validation: the entire delivered module compiled through `scompile.py` in both sandbox
and library module modes with no errors and no warnings. The initial compiler feedback
(reserved field identifiers, one noncomputable Finsupp helper, one unused proof binder)
was repaired and the clean full-file compile repeated.

## Second reading by Q42

This is a separate in-thread reading with the node and final module open; no independent
agent was started, as required by the dispatcher brief. I checked all four clauses, not
only the primary recorded declaration. The odd sign acts on the right constant coefficient,
and `OddPresentation.multiplication` matches the node's (-1)^j bc. Both grading fields use
integer subtraction rather than truncated natural subtraction. Both uniqueness predicates
quantify over all graded structures with exactly the prescribed restriction/normalization,
not just over a selected family. The even coefficient is uniformBell n a, with n the outer
index, matching (na)!/(n!(a!)^n). In the finite comparisons I checked the permutation maps
old variable i to target variable σ i, fixes A, and includes preservation of divided powers;
plain-algebra uniqueness is not asserted. The set construction includes injectivity,
coverage, all finite subsets, actual labelled generators, and the union grading. Finally,
the sequential union has compatible injective maps and an unrestricted unique extension
agreeing with all stages. Helpers have actual record data or explicit projection formulas.
No mathematical mismatch was found and no node field outside lean was changed.
