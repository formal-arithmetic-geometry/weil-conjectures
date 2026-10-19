## Worker report

The node is already implemented by the upstream `slopmaster2` declarations, so no new Lean
module is needed.  The node copy records
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceSeries` as the probing module and
records the declarations `FrobeniusModule`, `FrobeniusModule.localPolynomial`,
`LinearMap.traceSeries`, `FrobeniusModule.traceSeries`, `LinearMap.alternatingTraceSeries`, and
`FrobeniusModule.alternatingTraceSeries`.

The first clause, that a Frobenius module is a finite-dimensional vector space with a linear
automorphism, is rendered by the structure `FrobeniusModule` in
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule`: its `carrier` has
`AddCommGroup`, `Module K`, and `FiniteDimensional K` instances and its `frobenius` field is a
`LinearEquiv`.  Specializing its field parameter `K` to the chosen algebraic closure
`\Qlb` gives the stated pair `(V,F)`.

For a field `K`, `LinearMap.traceSeries` has signature
`noncomputable def traceSeries (F : Module.End K V) : K⟦X⟧ :=` and is defined by the coefficient
sequence `if n = 0 then 0 else LinearMap.trace K V (F ^ n) / n`.  Thus on a finite-dimensional
`V` it is exactly
`∑_{n≥1} Tr(F^n | V) T^n/n`; the zero coefficient is the omitted `n=0` term.  No
invertibility or semisimplicity is required.  The source declaration does not retain an unused
`FiniteDimensional` binder, but its specialization to finite-dimensional spaces is the node's
notion.

The determinant clause is rendered by `FrobeniusModule.localPolynomial`, which is the reverse
characteristic polynomial `M.frobeniusEnd.charpolyRev`, i.e. the polynomial determinant
`det(1-TF)` for a Frobenius module.  For an arbitrary endomorphism the same reverse
characteristic polynomial is available as `LinearMap.charpolyRev`; the node's determinant formula
is therefore the same construction.  `FrobeniusModule.traceSeries` is the Frobenius-module
wrapper around `LinearMap.traceSeries`.

For a finite index set and a family, `LinearMap.alternatingTraceSeries` has signature
`noncomputable def alternatingTraceSeries (s : Finset ℤ) (F : ∀ i, Module.End K (W i)) : K⟦X⟧ :=`
and is the finite sum `∑ i ∈ s, (i.negOnePow : ℤ) • traceSeries (F i)`.  The sign is exactly
`(-1)^i` (including negative integer indices), and finite distributivity gives the displayed
coefficient form.  `FrobeniusModule.alternatingTraceSeries` is the corresponding wrapper for a
family of Frobenius modules.  The empty index set and negative indices are accepted by the
`Finset ℤ`/`Int.negOnePow` formulation; zero-dimensional spaces and singular or nilpotent
endomorphisms are also allowed by `LinearMap.traceSeries` and `charpolyRev`.  No semisimplicity
assumption occurs in any declaration.

No statement dependencies are listed by the node; all notions above are supplied by the
recorded upstream declarations.

Searches for an existing declaration:

* `msearch.py ... leanfinder "Frobenius module finite dimensional vector space automorphism trace series determinant alternating trace series"` returned unrelated finite-field trace results and `LinearMap.trace`; it did not find the project names through semantic search.
* `msearch.py ... loogle "LinearMap.traceSeries, LinearMap.alternatingTraceSeries, FrobeniusModule"` reported unknown identifiers/no hits in Mathlib.
* `msearch.py ... grep "traceSeries|alternatingTraceSeries|FrobeniusModule" Mathlib` returned no Mathlib matches.
* `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` located the exact declarations in
  `ZetaLinearAlgebra/FrobeniusModule.lean`, `ZetaLinearAlgebra/DetTrace.lean`, and
  `ZetaLinearAlgebra/FrobeniusModule/TraceSeries.lean`; `rg` over the shared `lean/Sheaf` tree
  found no duplicate declaration.

The existing declarations were checked with `scompile.py` by importing
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceSeries` and issuing `#check` for all six
recorded names; the check compiled cleanly.

## Second reading by NS

I read the sandbox node and its exact source,
`literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-def-frobmod/_section.md`,
and the enclosing `sec-trace-formula/_section.md`. This is a blueprint definition, not
an assertion sourced from a Stacks tag. The source text equals the node text. The enclosing
section imposes no additional linear-algebra hypotheses. I opened the actual upstream
structure and definitions in `ZetaLinearAlgebra/FrobeniusModule.lean`,
`ZetaLinearAlgebra/DetTrace.lean`, `ZetaLinearAlgebra/FrobeniusModule/TraceSeries.lean`,
and `Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean` under the slopmaster2 source tree.
There are no statement dependencies, new nodes, dependency modules, or statement corrections.
No repair note for this item is present in `coord/repair-notes`.

Clause-by-clause inventory and verdict:

1. The coefficient field for a Frobenius module is the chosen algebraic closure of Q_l.
   `FrobeniusModule.{u,v} K` accepts any field, so setting `K` to that chosen field gives
   precisely this specialization. It does not require a Frobenius action on the field,
   a finite base field, or a choice of eigenbasis. Verdict: matches.
2. Its vector space V is finite-dimensional, and F is a K-linear automorphism.
   `FrobeniusModule.carrier : Type u`, its `AddCommGroup`, `Module K`, and
   `FiniteDimensional K` structure fields, and
   `frobenius : carrier ≃ₗ[K] carrier` encode exactly these data.
   `frobeniusEnd` is `frobenius.toLinearMap`. Verdict: matches.
3. The generalized pair has any field K, a finite-dimensional K-space V, and any
   endomorphism F. `LinearMap.traceSeries (F : Module.End K V)` has just the field,
   additive-group, and module binders; its specialization to finite-dimensional V gives
   the stated construction. The missing finite-dimensional binder is harmless additional
   generality of an existing definition, not a new theorem about infinite-dimensional
   traces. In particular F need not be invertible. Verdict: matches on the node's domain.
4. The trace series has coefficient zero at n=0 and coefficient `Tr(F^n)/n` for n>0.
   The body is exactly
   `PowerSeries.mk fun n ↦ if n = 0 then 0 else LinearMap.trace K V (F ^ n) / n`.
   `LinearMap.coeff_traceSeries` confirms this coefficient formula. `K⟦X⟧` is the
   formal-power-series ring; no convergence condition is added.
   `FrobeniusModule.traceSeries` applies this definition to `frobeniusEnd`.
   Verdict: matches, including the starting exponent 1.
5. The determinant for an arbitrary F is `LinearMap.charpolyRev F`, defined as
   `F.charpoly.reverse`. I checked the bridge `LinearMap.charpolyRev_toMatrix` and
   Mathlib's `Matrix.charpolyRev`, whose body is
   `det (1 - (X : R[X]) • M.map C)` in
   `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`.
   Thus this is det(1-TF), including singular F. The required `Module.Free` and
   `Module.Finite` instances follow from the node's finite-dimensional vector-space
   hypothesis over a field. `FrobeniusModule.localPolynomial` specializes the same
   construction to its automorphism. Verdict: matches. The first worker discussed
   `LinearMap.charpolyRev` but omitted it from `lean.declarations`; I added it, so the
   recorded declaration list explicitly covers this general determinant clause.
6. The grading set is a finite subset of Z, and the family may have different spaces
   in each degree. `LinearMap.alternatingTraceSeries` takes `s : Finset ℤ`,
   `W : ℤ → Type v`, the additive-group/module structures on each `W i`, and
   `F : ∀ i, Module.End K (W i)`. Only terms in s are summed. A family given only on s
   can be extended outside s by the zero vector space and its zero endomorphism;
   these values are never read by the sum. Thus the total-family encoding imposes
   no mathematical hypothesis on the given finite family. Verdict: matches.
7. The first alternating-series formula is exactly its body
   `∑ i ∈ s, (i.negOnePow : ℤ) • traceSeries (F i)`.
   `Int.negOnePow` gives the parity sign for every integer, including negative ones.
   For the second displayed formula I read `LinearMap.coeff_alternatingTraceSeries`:
   coefficient n is zero at n=0 and otherwise
   `(∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace K (W i) (F i ^ n)) / n`.
   Its existing proof distributes the finite sum and scalar multiplication over
   division. `FrobeniusModule.alternatingTraceSeries` uses the same generic definition.
   Verdict: both formulas match; the wrapper is not substituted for arbitrary F.
8. No semisimplicity is assumed: no diagonalizability, splitting, eigenvalue, or
   semisimple instance appears in any of these signatures. Verdict: matches.

Edge cases: the empty s gives the empty sum 0; no Nonempty binder occurs. V=0 is
allowed, with trace series 0 and determinant 1, consistent with the existing
`LinearMap.charpolyRev_of_subsingleton`. Singular and nilpotent F remain available
in the generic definitions. The constant coefficient is explicitly zero; n=0
never contributes `Tr(1)/0`. Negative grading integers use parity, not natural
exponentiation. Field and space universes are independent in the printed signatures;
there is no forced equality. A finite family fits one common universe (and can be
lifted to a maximum when necessary). There is no scheme hypothesis or empty-scheme
case in this node. The generic definition has no characteristic-zero binder: it
uses Lean's field division, so if the cast of a positive n is zero its coefficient
is zero by totalized division. For the intended Q_l-algebraic-closure specialization
all positive n are nonzero. No exponential/logarithmic identity over positive
characteristic is asserted here; those separate upstream identities have CharZero.

Independent searches, performed with `msearch.py NS sk-def-frobmod` and direct rg:

- LeanSearch: "formal power series whose nth coefficient is trace of nth power of a
  linear map divided by n" returned `PowerSeries.mk`, exponential/Bernoulli series,
  and other unrelated constructions, no replacement definition.
- LeanFinder: "formal power series coefficients trace of iterated endomorphism
  divided by positive integer and determinant one minus variable times endomorphism"
  returned matrix characteristic-polynomial/trace coefficient lemmas and ordinary
  determinant declarations. These explain parts of the construction but do not
  replace the upstream series definitions.
- Loogle: `LinearMap.charpolyRev` was unknown in the Mathlib-only index. Direct rg
  instead located its exact upstream definition and the Mathlib matrix determinant.
- `msearch ... grep 'FrobeniusModule|alternatingTraceSeries|traceSeries' Mathlib`
  returned no matches. Independently rg with `trace.*[Ss]eries|[Ss]eries.*trace|FrobeniusModule`
  across all Mathlib and `lean/Sheaf` found only unrelated Lie derived-series/trace-form
  occurrences. Searches in the upstream `WeilConjectures` tree found the exact
  definitions opened above. The side module `Sheaf.LinearAlgebra.ReverseCharpolyCoefficients`
  uses the same upstream `charpolyRev` and does not redefine this notion.

H5/H6/H8/H9: the existing definitions have actual structure/sequence/polynomial/sum
bodies, and I added no definition, axiom, or proof. The original upstream series
and wrapper docstrings identify sk-def-frobmod; the node has no proof steps to copy.
No new module/docstring or unused binder is introduced. The recorded
`lean.statement` remains verbatim the upstream signature
`noncomputable def traceSeries (F : Module.End K V) : K⟦X⟧ :=`.
The public imports of the recorded module expose all seven declarations.

The sole delivery repair is adding `LinearMap.charpolyRev` to `lean.declarations`
and explaining the general determinant clause and its inferred instances in
`lean.note`. The node's mathematical statement is unchanged. I retained the
worker report in place. An independent scratch probe imports the recorded module,
checks all seven declarations and the coefficient/determinant bridges, and prints
both generic series bodies and the axioms of the structure, trace series, and
general determinant. Those three axiom lists contain only propext,
Classical.choice, and Quot.sound. The probe is scratch only and is not delivered.

Validation: `scompile.py NS sk-def-frobmod scratchpad/SecondReading.lean` passed
both sandbox and library checks without errors or warnings (2.6 seconds for the
library check). The first diagnostic run used `pp.universes`; I removed that
scratch development option and reran to obtain this clean result.
