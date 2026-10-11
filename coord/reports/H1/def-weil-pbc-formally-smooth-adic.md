## Worker report

The module defines `Algebra.FormallySmoothAdic R S n : Prop`, the lifting
condition for the `n`-adic topology on `S` with discrete base `R`. Source:
Stacks Project, More on Algebra, Tags 07EB, 07E9, 07EC, and 07NI. The local
`literature/stacks-project/more-algebra.tex` was absent, so I read the cited
tags at `https://stacks.math.columbia.edu/tag/07EB` (and 07E9, 07EC, 07NI).

Statement correspondence:

- `R : Type u`, `[CommRing R]`, `S : Type v`, `[CommRing S]`, and
  `[Algebra R S]` give the commutative rings and structure map `R → S`.
- `(n : Ideal S)` is the specified adic ideal of the target.
- `∀ ⦃D : Type w⦄ [CommRing D] [Algebra R D]` quantifies over commutative
  `R`-algebras `D` in an arbitrary universe `w`.
- `(J : Ideal D), J ^ 2 = ⊥ →` is the square-zero ideal condition.
- `g : S →ₐ[R] D ⧸ J` is an `R`-algebra map into the quotient, whose
  `R`-algebra structure is induced by `D`.
- `∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g x = 0` states that `g` kills a positive
  power of `n`, exactly the continuity condition for an adic source and a
  discrete target (Tag 07E9).
- `∃ f : S →ₐ[R] D, (Ideal.Quotient.mkₐ R J).comp f = g` is the required
  `R`-algebra lift through the quotient map.
- The remarks about continuity of a lift and equivalence with Stacks 07EB
  appear in the docstring. The comparison with an `m`-adic base topology in
  07EC(2)/07NI is explanatory in the node and is not part of the condition.

The dependency `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf:
`AlgHom` (`Mathlib.Algebra.Algebra.Hom`), ideal multiplication and powers
(`Mathlib.RingTheory.Ideal.Operations`), and `Ideal.Quotient.mkₐ` plus the
quotient algebra instance (`Mathlib.RingTheory.Ideal.Quotient.Operations`).
The single import of the last module supplies them all.

Edge cases checked: `n = ⊥` makes the power condition true for every `g`;
`n = ⊤` restricts it to maps killing all of `S`; `J = ⊥` remains among the
quantified ideals; the zero rings and zero algebras are admitted because no
nontriviality assumption is imposed. The exponent must be at least one.
The separate universe `w` leaves the test algebra size unrestricted.

Existing-definition searches:

- `msearch.py ... leanfinder "formally smooth for the n-adic topology: algebra
  maps killing a power of n lift across square-zero ideals"`: eight hits,
  including `Algebra.FormallySmooth.exists_lift` and adic-completion lifts;
  none includes the source ideal-power condition.
- `msearch.py ... loogle "FormallySmooth, FormallySmoothAdic,
  Ideal.Quotient.mkₐ"`: zero hits; the query's unqualified first name was
  reported unknown.
- `msearch.py ... grep "FormallySmooth|formally smooth" RingTheory/Smooth`:
  hits concern discrete formal smoothness or consequences for completions.
- `rg` over the upstream `WeilConjectures` and repository `lean/Sheaf`:
  no adic formal-smoothness definition; upstream hits use Mathlib's discrete
  `Algebra.FormallySmooth`.
- `grep -rn "def-weil-pbc-formally-smooth-adic"` over upstream
  `WeilConjectures`: no hit.

The server compiled the module cleanly with `scompile.py`.

## Second reading by H1

I checked the node against Stacks Tags 07EB, 07E9, 07EC, and 07NI, and read the
Mathlib declarations named in its sole statement dependency,
`def-weil-pbc-algebra-hom-quotient`. The source assumes commutative unital rings,
a continuous map from discrete `R` to `n`-adic `S`, and discrete test rings;
continuity of the first map is automatic.

- `R : Type u`, `S : Type v`, `[CommRing R]`, `[CommRing S]`, and
  `[Algebra R S]` render the commutative rings and their structure map: exact.
- `(n : Ideal S)` renders the specified ideal of `S`: exact.
- `∀ ⦃D : Type (max u v)⦄ [CommRing D] [Algebra R D]` renders each
  commutative test `R`-algebra. The universe is fixed by `R` and `S`, as in
  Mathlib's `Algebra.FormallySmooth.iff_comp_surjective`: exact within Lean's
  standard universe convention.
- `(J : Ideal D), J ^ 2 = ⊥ →` renders every square-zero ideal: exact.
- `g : S →ₐ[R] D ⧸ J` uses Mathlib's quotient `R`-algebra instance and
  `AlgHom`, the dependency's recorded notions: exact.
- `∃ k : ℕ, 1 ≤ k ∧ ∀ x ∈ n ^ k, g x = 0` renders a positive power killed
  by `g`: exact; Tag 07E9 identifies this with adic-to-discrete continuity.
- `∃ f : S →ₐ[R] D, (Ideal.Quotient.mkₐ R J).comp f = g` renders the lift
  and quotient equation: exact; `mkₐ` is the dependency's recorded map.
- The node's remarks about the lift killing `n ^ (2 * k)` and continuity are
  explanatory, outside the predicate. The declaration docstring carries both
  proof steps, using `f(n ^ k) ⊆ J`, `J ^ 2 = 0`, and Tag 07E9. The comparison
  with an adic base topology is likewise explanatory, not an extra binder.

Edge cases: `n = ⊥` makes the power condition automatic; `n = ⊤` requires
`g` to kill all of `S`; `J = ⊥`, zero rings, and characteristic zero or positive
remain admitted. `k = 0` is excluded, as the node requires. There is no index
set or scheme in this statement. An arbitrary independent universe `w` was a
mistake: the truth of the predicate could vary with the inferred universe.
I changed `Type w` to `Type (max u v)` and removed `w`; this follows Mathlib's
formal-smoothness lifting criterion and admits test algebras large enough for
the usual universe-lift arguments. I also corrected the node's `lean.statement`
to match the exact signature extracted by delivery preflight.

Independent searches: `msearch.py` with LeanFinder query "topologically
formally smooth adic algebra square zero lifting" returned only Mathlib's
discrete `Algebra.FormallySmooth` and adic-completion consequences. Loogle
query `Algebra.FormallySmoothAdic` returned no declaration; grep query "adic
formal smoothness lifting nilpotent quotient" returned no hit. `rg` over
Mathlib's `RingTheory/Smooth`, the upstream `WeilConjectures`, and this
repository's `lean/Sheaf` found no existing adic lifting predicate. Thus this
module remains necessary; no other mismatch was found.
