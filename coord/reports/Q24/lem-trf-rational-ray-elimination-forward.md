## Worker report

The module `Sheaf.TraceFormula.RationalRayEliminationForward` supplies the explicit
signed elimination index and family, and states `Weil.rationalRayEliminationForward`.
The theorem's proof is `sorry`; both definitions have complete data. These two
helpers are precisely the family constructed in this node, not independent notions.
They are recorded alongside the theorem in `lean.declarations`. No new nodes,
dependency repairs, or statement corrections are needed. Only the item's `lean`
field changes.

The source is the node's agent-written assertion extracted from
`lem-trf-rational-cone-dual-finite`, old proof steps 3--4, whose current Lean module
and proof docstring were read. ILO, Travaux de Gabber, Exposé VIII Remark 3.1.29,
printed p. 103, supplies context only; it is not claimed as the source of this
elementary assertion. The theorem docstring reproduces the complete argument:
finite sign classes, linearity by the linear-map operations, the retained-form
inequalities, and the nonnegative residual combination with cancelling parameter.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Rational vector space V | `{V : Type u} [AddCommGroup V] [Module ℚ V]` |
| Finite set I | `{I : Type w} [Finite I]`, with no nonemptiness hypothesis |
| Rational linear forms f indexed by I | `(f : I → V →ₗ[ℚ] ℚ)` |
| Vector v | `(v : V)` |
| Coefficients a_i = f_i(v) | Directly `f i v`, without an extra arbitrary coefficient parameter |
| Zero sign class I_0 | `{i : I // f i v = 0}` |
| Positive sign class I_+ | `{i : I // 0 < f i v}` |
| Negative sign class I_- | `{j : I // f j v < 0}` |
| Disjoint union of all three blocks | `rationalRayEliminationIndex f v`, the sum `I₀ ⊕ (I₊ ⊕ (I₊ × I₋))` |
| First block f_h | `Sum.inl h` maps to `f h.val` |
| Second block f_i | `Sum.inr (Sum.inl i)` maps to `f i.val` |
| Pair block a_i f_j - a_j f_i | `Sum.inr (Sum.inr (i, j))` maps to `(f i.val v) • f j.val - (f j.val v) • f i.val` |
| Every member is a rational linear form | The family's codomain is `V →ₗ[ℚ] ℚ`; scalar multiplication and subtraction are Mathlib's linear-map operations |
| Family is finite | The theorem's first conjunct is `Finite (rationalRayEliminationIndex f v)` |
| Every x and rational t | `∀ (x : V) (t : ℚ)` |
| Nonnegative parameter | `0 ≤ t →` |
| All residuals are nonnegative | `(∀ i : I, 0 ≤ f i x - t * f i v) →` |
| All family members are nonnegative at x | `∀ j : rationalRayEliminationIndex f v, 0 ≤ rationalRayEliminationFamily f v j x` |
| Empty index sets, repetitions, zero forms allowed | There is no `Nonempty`, injectivity, distinctness, or nonzero hypothesis; the family retains indices |

The sole statement dependency is `def-weil-field`, status `mathlib`, whose
`mathlib_match` is `Field`. Its full definition and docstring in
`Mathlib.Algebra.Field.Defs` were read. The current blueprint field definition was
also read from `literature/blueprint/latest`. The rational field and order instances
are imported through `Mathlib.Algebra.Order.Field.Rat`. The other public imports
are `Mathlib.Algebra.Module.LinearMap.Defs`, giving `LinearMap`, its scalar action
and subtraction, and `Mathlib.Data.Finite.Defs`, giving `Finite`. In particular,
`LinearMap.smul_apply` and `LinearMap.sub_apply` were read in full: evaluating the
pair form gives exactly `a_i * f_j x - a_j * f_i x`. There are no proof-dependency
nodes and no unused project imports. The vector space and index universes `u`, `w`
are independent and explicit; `autoImplicit` is disabled in the file.

Edge cases were checked before writing:

- If I is empty, all three blocks are empty and the final universal quantifier is vacuous.
- If v = 0, every coefficient is zero and the first block is precisely all original indices.
- If only negative coefficients occur, the family is empty, as specified.
- If either strict-sign class is empty, the pair block is empty, while the other blocks remain.
- If t = 0, each original value is nonnegative, and the two coefficients in a pair combination are nonnegative.
- Zero forms stay in the zero block. Repeated forms remain separate indices, including equal pair forms.
- No finite dimensionality of V is imposed. The zero vector space is included.
- For a concrete sign check, take coordinate forms, v = (2,-3), x = (3,-2), t = 1. Both residuals equal 1 and the pair evaluates to 2*(-2)-(-3)*3 = 5, so the order and sign agree with the node.
- Dropping t ≥ 0 would fail already for f(v) = 1, t = -1, f(x) = -1. The required hypothesis is retained.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanSearch: `For finitely many rational linear forms, nonnegative residual inequalities with a nonnegative parameter imply all opposite sign elimination inequalities`. Eight hits, including `elimVar`, `pelimVar`, Linarith implementation types/instances, an unrelated NormNum inequality, and `Sum.nonneg_elim_iff`. None supplies this indexed linear-family assertion.
- LeanFinder: `A finite family of rational linear forms yields nonnegative signed elimination forms when t is nonnegative and f_i x minus t times f_i v is nonnegative`. Eight hits: chiefly the Linarith simplex certificate machinery and `elimVar`, plus unrelated root-system, convex-body and combinatorial nonnegativity results. No exact statement.
- Loogle: `LinearMap.sub_apply, LinearMap.smul_apply`. Zero hits for the combined query. Both actual declarations were then located and read directly in Mathlib; neither is the complete node.
- Mathlib grep: `fourier.?motzkin|rationalRay|elimin.*nonneg|nonneg.*elimin`. Thirteen hits, chiefly tactic implementation/documentation. Read `Tactic/Linarith/Oracle/FourierMotzkin.lean` at its `PComp.add`, `elimVar` and `pelimVar` definitions: these are computations on syntactic comparisons, not this theorem.
- Local `rg -n -i 'rational.?ray|ray.?elimination|signed.?elimination|fourier.?motzkin'` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: only an unrelated rational-character-ray definition in `TorusCharacterTangentWeights.lean`.
- Local `grep -rn 'lem-trf-rational-ray-elimination-forward' lean/WeilConjectures`: no matches.
- Local `rg` for all three proposed declaration names over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no matches. The already landed cone description is the parent theorem, not this finite-family forward assertion.

Validation: `scompile.py Q24 lem-trf-rational-ray-elimination-forward` compiled the
delivered module in both sandbox and library modes with exit code 0 and no errors
or warnings. No proof was supplied. No statement dispute or node fault was found.

## Second reading by Q24

I reopened the item JSON and delivered Lean file for a second pass. This is a
worker self-check; the maintainer's independent review remains the delivery review,
and no additional agent was started. The comparison above checks each hypothesis
and conclusion explicitly. I specifically rechecked the pair order `(positive,
negative)` and the subtraction order `a_i f_j - a_j f_i`, the inclusion of positive
forms even when there are no negative indices, and finiteness of the indexed
family rather than merely finiteness of its image. The definitions preserve the
node's disjoint union with no quotient identifying repeated values. The codomain
already enforces rational linearity, and the single theorem states precisely the
remaining finiteness and necessary inequalities. No mismatch or correction was
found. The source attribution consistently distinguishes the agent-written proof
from ILO's contextual remark.
