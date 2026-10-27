## Worker report

The module `Sheaf.RingTheory.AdjoinDGACycle` states the two parity cases of
`lem-sfb-adjoin-dga-cycle`, as `GradedAlgebra.VariableAdjunction.odd_differential_extension`
and `GradedAlgebra.VariableAdjunction.even_differential_extension`. Both proofs are `sorry`.
There are no definitions, extra nodes, dependency repairs or statement corrections.

Read the complete item, including its eight proof steps; both statement dependencies and
all their recorded interfaces; Stacks `literature/stacks-project/dpa.tex`, Tag 09PM
(`lemma-extend-differential`, lines 1181ff.); and the source declarations described below.
The node agrees with the source. The source omits the computation; both theorem docstrings
carry the corresponding detailed computation from the accepted DAG split.

Hypotheses and objects, clause by clause:

- A commutative ring R is `(R : Type u) [CommRing R]` in both statements. The coefficient
  algebra and adjoined algebra use independent universes v and w; neither is restricted to
  R's universe or to the other's universe.
- The given divided-power DGA `(B,d,gamma)` is `(B : AlgebraData.{u, v} R)` and
  `(d : DividedPowerDGA B.grade)`. `AlgebraData` packages exactly the existing unital
  algebra, nonnegative grading, signed commutativity and strict odd-square-zero instances.
  `d.toGradedDividedPowers` is the original gamma; `d.d` is its actual R-linear differential.
- The positive integer e is `(e : ℕ) (he : 0 < e)`. The node's two exhaustive parity cases
  become `(heodd : Odd e)` and `(heeven : Even e)` in the corresponding theorems.
- The cycle is `(z : B.Carrier) (hz : z ∈ B.grade (e - 1)) (hcycle : d.d z = 0)`.
  Positivity of e ensures this natural subtraction is exactly the node's nonnegative degree.
- The specified adjoined algebra C, rather than an arbitrary algebra or map, is
  `(C : AlgebraData.{u, w} R)` with `(p : OddPresentation B C e)` or
  `(p : EvenPresentation B C e)`. These recorded presentations supply the linear
  coordinates, injective graded inclusion, multiplication and full grading of B ⊕ BT or
  the direct sum of the B T^[a]. Injectivity follows immediately from
  `p.inclusion_coordinates` and injectivity of the coordinate equivalence.
- The fixed extended divided powers are `(δ : GradedDividedPowers C.grade)` and
  `(hδ : Preserves p.inclusion d.toGradedDividedPowers δ)`. The even case additionally uses
  `(hnormalized : EvenNormalized p δ)`, which is precisely gamma_a(T)=T^[a] from the
  adjunction node. These are the structures already supplied by that node, not additional
  mathematical hypotheses or an extra polynomiality assumption on B.

Conclusions, clause by clause:

- Existence of the differential making C a divided-power DGA is
  `∃ D : DividedPowerDGA C.grade`. Its fields give R-linearity, degree minus one,
  square zero, signed Leibniz and compatibility on the entire positive even ideal.
  `D.toGradedDividedPowers = δ` fixes exactly the already specified divided powers on C.
  The global linear-map encoding is equivalent to the compatible degree maps because
  the underlying algebra has the recorded internal direct-sum grading. In particular,
  `D.degree` uses integer components and forces degree zero to map to zero.
- Extension of the old differential is
  `∀ b : B.Carrier, D.d (p.inclusion.toAlgHom b) = p.inclusion.toAlgHom (d.d b)`.
- In the odd case T is `p.coordinates.symm (0, 1)`; in the even case it is
  `p.coordinates.symm (Finsupp.single 1 1)`. The generator equation is respectively
  `D.d T = p.inclusion.toAlgHom z`, so z is explicitly transported along the given inclusion.
- Uniqueness quantifies over every `D' : DividedPowerDGA C.grade` with the same δ,
  the extension equation and the generator equation and concludes `D' = D`. In particular,
  the competing differential is NOT required to satisfy the monomial formula; that formula
  is a separate conclusion. Once the divided powers and differential coincide, the remaining
  structure fields are propositions, so uniqueness of the whole structure is equivalent
  to uniqueness of the differential in the node.
- The inclusion is a morphism of divided-power DGAs: its algebra and grading preservation
  are `p.inclusion : Hom B C`, its divided-power preservation is `hδ`, and its differential
  preservation is the conclusion's extension equation. The presentation already supplies
  injectivity. There is no second definition of a morphism or an untied existential map.
- For odd e the final conclusion quantifies over `(i : ℕ) (b : B.Carrier)` with
  `b ∈ B.grade i` and asserts
  `D.d (incl b * T) = incl (d.d b) * T + (-1 : C.Carrier)^i * (incl b * incl z)`.
  This is the node's formula for every homogeneous coefficient, including degree zero.
- For even e the final conclusion quantifies over `(i a : ℕ) (b : B.Carrier)` with
  `b ∈ B.grade i` and `0 < a` and asserts
  `D.d (incl b * t_a) = incl (d.d b) * t_a + (-1 : C.Carrier)^i *
  (incl b * incl z * t_(a-1))`, where `t_a` is
  `p.coordinates.symm (Finsupp.single a 1)`. These are the prescribed divided powers of T
  by `EvenNormalized`; at a=1 the final symbol is t_0=1. The extension equation separately
  handles a=0, which the node's positive-index formula does not assert.

Dependency declarations used:

- `Sheaf.RingTheory.DividedPowerDGA`: `GradedAlgebra.DividedPowerDGA` and its fields
  `d`, `degree`, `square_zero`, `leibniz`, `compatible`, `toGradedDividedPowers`.
  The inherited graded divided powers are those of `Sheaf.RingTheory.GradedDividedPowers`.
- `Sheaf.RingTheory.DividedPowerVariableAdjunction`:
  `GradedAlgebra.VariableAdjunction.AlgebraData`, `Hom`, `Preserves`,
  `OddPresentation`, `EvenPresentation`, `EvenNormalized`. Read their complete signatures
  and docstrings, and the `odd_variable` and `even_variable` existence/uniqueness theorems
  supplying these presentations and extended divided powers. Both recorded dependency
  modules are public imports. The proof dependency list is exactly the statement dependency
  list, so these imports also include the complete DAG proof plan.
- Mathlib's `Finsupp.single` identifies individual even basis symbols; all ring, module,
  grading and linear-equivalence operations are inherited from the dependency interfaces.

Edge cases checked before writing:

- e=1: z lies in B_0 and is a cycle, T is exterior, and the formula is the Koszul
  one-variable differential. No positivity of the degree of z is assumed.
- e=2: z lies in B_1; its square vanishes by strict odd-square-zero, including in
  characteristic two. No assumption that 2 or any factorial is invertible is introduced.
- e=0 is excluded exactly by the node; no other positive degree is excluded.
- z=0 gives the coefficientwise old differential on the adjoined free summands.
- b of degree zero is included; the old and new integer-degree conditions force its
  differential into the zero negative component. The proof docstrings handle this boundary
  without taking a negative natural degree or using a spurious sign identity at p=0.
- In the even case a=1 gives t_0=1 and a=0 is handled by the extension equation. Arbitrary
  positive a are allowed; no nonvanishing assumption on the symbols or coefficients occurs.
- The zero ring, zero homogeneous coefficients, and zero positive even parts are permitted.
  R has no characteristic restriction. The odd compatibility proof expands finite odd sums
  and cancels cross terms, rather than dividing by two. The even proof uses integer
  coefficient identities, rather than inverting factorials.
- Independent carrier universes permit any presentation of the same free extension.
  The theorem does not select a presentation or divided powers from an unproved existence
  assertion; it applies to the actual supplied presentation and operations.

Searches for an existing statement (all run for Q67 / lem-sfb-adjoin-dga-cycle):

- `msearch.py ... leanfinder "A unique differential extending a divided power differential
  graded algebra after adjoining a variable whose differential is a cycle"`: eight hits,
  concerning Kahler differentials, algebra presentations, square-zero ordinary derivations
  and Jacobi-Zariski maps; none has the strict graded divided-power extension statement.
- `msearch.py ... loogle 'DividedPowers, "differential"'`: zero hits.
- `msearch.py ... grep 'DividedPowerDGA|divided.?power.*differential|extend.*differential'`:
  one unrelated manifold extended-chart differential hit.
- `msearch.py ... leansearch "There is a unique differential on an algebra adjoining an
  exterior or divided power variable extending a differential graded algebra with prescribed
  cycle"`: eight hits on ordinary Differential rings, field derivations and polynomial
  derivation extensionality; none matches the item.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for `DividedPowerDGA`, divided-power
  differential, `lemma-extend-differential` and the item id: only the given DGA dependency
  module; no differential-adjunction theorem. The prescribed item-id search upstream also
  found no match. Searches for the two new theorem names in Mathlib, upstream, Sheaf and
  `dag/lean_names_upstream.json` found no collision.

Validation: the complete delivered module compiled on the server through the prescribed
`scompile.py Q67 lem-sfb-adjoin-dga-cycle .../AdjoinDGACycle.lean`, including library-mode
compilation, with no errors or warnings. `set_option autoImplicit false` binds all variables
and universes explicitly. The only postponed proofs are the two named theorems, both
corresponding to this DAG node and carrying full natural-language proofs in their docstrings.

Independent review is performed by the maintainer, as directed by the dispatcher brief.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
