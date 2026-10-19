## Worker report

The module `Sheaf.Paper.FieldTorAmplitude` states
`WeilConjectures.field_tor_amplitude`. It quantifies the fixed finite-field datum,
prime and algebraic closure, and scheme from the node. For every finite coefficient
field `E` and object `K` of the recorded common-stage finite coefficient category, the
first conjunct gives integers `a ≤ b` implicitly through
`Scheme.HasProEtaleTorAmplitude` for the specified ordinary realization functor
`System.finite E`. For every object `K` of the common-stage pair category, the second
conjunct gives the same Tor-amplitude assertion for the specified closure realization
`System.closure`. The ordinary realization is the canonical choice supplied by
`OrdinaryFieldRealization.exists_ordinaryFieldRealization`; no extra hypothesis or
constructibility condition is added.

The declarations used are `Sheaf.Paper.FieldStageOrdinaryRealization`,
`WeilConjectures.OrdinaryFieldRealization.System`,
`WeilConjectures.OrdinaryFieldRealization.exists_ordinaryFieldRealization`,
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients.Stage`,
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients.Pair`,
`AlgebraicallyClosedCoefficients.Coefficient`,
`AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`, and
`Sheaf.Paper.FiniteTorAmplitude` (whose field-stage category is the given category
itself). `HasProEtaleTorAmplitude` renders the clause that for every degree-zero
constant-field module sheaf the derived tensor cohomology vanishes outside one
integer interval; its interval is quantified after fixing `K`, before any test
module is chosen.

Edge cases checked: the interval allows `a = b`; the quantifier includes the zero
object, identity coefficient inclusion, empty scheme, and arbitrary degree-zero test
module. No finite-dimensionality or constructibility hypothesis on the test module
is introduced. Independent universes `d`, `u`, and `v` are retained, and the closure
is transported by the existing `Closure` interface rather than identifying its
universe with that of `Y`.

Searches made: `msearch.py leanfinder` for “finite Tor amplitude at field
coefficients” returned no exact declaration; `msearch.py loogle` for
`TorAmplitude, HasFiniteProEtaleTorAmplitude` found only the existing pro-etale
predicate; `rg` over `WeilConjectures/` and `lean/Sheaf/` found no declaration of
this lemma. The dependency declarations were opened and their signatures checked.
The existing ordinary-realization theorem and the existing finite-Tor predicate are
used; no new definition node or dependency repair is needed.

## Second reading by Q102

I reread the node and the module signature clause by clause. The finite-stage
quantifier is rendered by `E` and `K : Stage ... E`, and its ordinary realization is
exactly `System.finite E`. The algebraically closed clause is rendered by the pair
category and `System.closure`. The Tor conclusion is exactly the recorded
`HasProEtaleTorAmplitude` predicate, including a single interval independent of the
module test. The only source-level “membership” wording is represented by the typed
category binders themselves, as in the recorded field-stage category aliases. No
mismatch was found.

## Independent maintainer landing reading, 2026-10-18

The immutable delivery a0196e9df8efb619720cdea8c4db4fc0ea227f77 is correct in
substance. The landing replacement changes documentation and proof imports only.
The theorem signature and the node's lean.statement remain verbatim equal.

Clause checks: D, the prime l and l != D.p render the inherited coefficient datum;
Omega is any algebraic closure in independent universe v; Y is any Scheme in u,
with no structure morphism, Noetherian, quasi-compact or invertibility hypothesis.
The finite-stage E binder covers the directed finite subfields, and Stage unfolds
to the recorded raw scalar localization on its equivalent small coefficient model.
Pair is the recorded common-stage category without Karoubi completion. Their
objects already belong to the field-stage finite-Tor categories because those
categories are aliases of the given categories. System.finite and System.closure
are the specified ordinary realizations, constrained by the integral object and
pure-scalar morphism formulas; this is not a choice of an arbitrary functor.
HasProEtaleTorAmplitude includes a <= b, tests every degree-zero module sheaf,
and requires cohomology to vanish outside the interval for every K-flat model.
The bounds follow K and precede all test sheaves. Shrink.algEquiv transports both
finite coefficients and the closure without imposing u = v.

Edge cases: zero object, empty scheme, base coefficient field, identity inclusion,
a = b, arbitrary negative endpoints, and unrestricted test sheaves are retained.
There is no n parameter at field stages. The source's field-flatness argument is
valid for arbitrary module sheaves over a discrete constant field sheaf.

Landing corrections: H8, add the node's three-step natural-language proof to the
theorem docstring; H9/stages/2-statements.md rule 7, add the two recorded proof
imports KFlatResolutionIndependentCoefficients and ConstantFieldTensorCohomology.
No new helper, definition, node or statement correction is needed. The original
Worker report and Second reading by Q102 sections are preserved.

Independent searches: LeanSearch for "A bounded complex of sheaves over a constant
field has finite Tor dimension" returned constant-sheaf, projective-dimension and
sheaf-limit results, with no exact statement. Loogle for "TorAmplitude" returned
zero results. Targeted rg searches in Mathlib, upstream WeilConjectures and
lean/Sheaf found existing Tor predicates and the field-category alias, but no
existing theorem with these realization clauses. The upstream pro-etale finite-Tor
category is a different interface and is not substituted for this ordinary
constant-coefficient statement.

Compiler evidence: scompile.py Q102 lem-weil-field-tor-amplitude on the immutable
module exited 0, no Lean diagnostics: sandbox overlay phase 189.4 s including
dependencies, library confirmation 7.5 s. The same wrapper on the complete fixed
FieldTorAmplitude.lean exited 0, no Lean diagnostics: sandbox overlay phase 21.0 s,
library confirmation 5.6 s. These are wrapper phase times; each Lean invocation
retains its default 60 s limit. This installed scompile.py currently delegates the
side overlay and confirmation to the server, rather than running a local compiler.
Only the prescribed wrapper was invoked, with no direct ssh, lake build, global
build or live Lean edit.
