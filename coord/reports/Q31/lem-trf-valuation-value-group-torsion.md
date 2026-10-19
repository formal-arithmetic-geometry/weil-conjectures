## Worker report

The module `Sheaf.RingTheory.ValuationValueGroupTorsion` states
`WeilConjectures.algebraic_extension_value_group_torsion`.  It uses the Mathlib
field-extension convention `[Field K] [Field E] [Algebra K E]` (the dependency
`def-pc-field-extension`) and the algebraicity class `[Algebra.IsAlgebraic K E]`
(the dependency `def-weil-algebraic-element`, whose element predicate is
`IsAlgebraic`).  The subring in the node is `V : Subring E`.

The hypothesis that every nonzero element of `E` or its inverse lies in `V` is rendered
by `hV : ∀ z : E, z ≠ 0 → z ∈ V ∨ z⁻¹ ∈ V`.  The conclusion's quantifier over every
nonzero `x` is `∀ x : E, x ≠ 0 →`.  The positive integer is
`∃ n : ℕ, 0 < n`; the base-field nonzero factor is
`∃ a : K, a ≠ 0`; and the unit factor is
`∃ u : E, u ≠ 0 ∧ u ∈ V ∧ u⁻¹ ∈ V`.  The power-times-unit equation is
`x ^ n = algebraMap K E a * u`.  The prose quotient clause in the node is the
standard consequence of this elementwise formulation, with the unit subgroup
`V^× = {u : E^× | u, u⁻¹ ∈ V}`; the theorem deliberately states the node's
“in element form” assertion directly.

The proof is `sorry`, as required for stage 2.  Its docstring records the node proof:
choose a nonzero polynomial relation, normalize at a term dividing all other terms,
use closure of nonunits under sums to obtain a unit ratio, and handle either exponent
order by inversion.

Dependencies used: `Mathlib.Algebra.Algebra.Defs.Algebra` for the field extension
structure (recorded by `def-pc-field-extension`), and
`Mathlib.RingTheory.Algebraic.Defs.Algebra.IsAlgebraic` / `IsAlgebraic` for the
algebraic extension convention (recorded by `def-weil-algebraic-element`).

Edge cases checked: `E = K` (take `n = 1` and `u = 1`), `V = E` (every nonzero
factor is a unit), purely inseparable algebraic extensions, ramified finite extensions,
and higher-rank valuation rings.  The nonzero hypotheses ensure that `x`, `a`, and
`u` represent elements of the multiplicative groups; no discreteness, rank, finiteness,
or characteristic assumption is introduced.

Searches for an existing declaration: `msearch.py Q31 lem-trf-valuation-value-group-torsion
leanfinder` with queries about algebraic valued-field extensions and power-times-unit
expressions returned only general valuation-ring, finite-field, and discrete-uniformizer
results; `loogle` queries `Algebra.IsAlgebraic, Valuation` and `Valuation, IsAlgebraic,
value group, quotient torsion` returned no matching theorem; `leansearch` queries about
algebraic valued-field extensions and torsion value-group quotients returned only
`ValuationRing`, `ValuationSubring`, and abstract torsion declarations.  Grep of
Mathlib `RingTheory/Valuation` and the project `WeilConjectures` found no declaration
of this arbitrary algebraic-extension power-times-unit statement.  The existing DAG
was searched for the item and for value-group/power-times-unit wording; no duplicate
notion was found.

No node correction or statement dispute was needed.

## Second reading by Q31

I reread the node and the module independently.  `K` and `E` are fields with the
algebra map and algebraicity instance, exactly matching the field-extension and
algebraic-element dependencies.  `V` is a subring of `E`, and `hV` quantifies over
all and only nonzero elements, expressing the inverse alternative without adding a
valuation rank or discreteness assumption.  For each `x ≠ 0`, the Lean conclusion
contains exactly a positive natural exponent, a nonzero `a : K`, a nonzero `u : E`
with both `u` and `u⁻¹` in `V`, and the equation `x ^ n = algebraMap K E a * u`.
The added nonzero binder on `u` is forced by the node's use of the multiplicative
unit group `V^×`; it excludes the zero element, which cannot be a unit.  No clause
of the elementwise statement is omitted or strengthened, and the quotient sentence
is represented by the explicitly identified element form as the title specifies.
