# Worker report: def-fd-additive-character

## Files written

- `dag/nodes/sec-fourier-transform/def-fd-additive-character.json`: existing definition, now a Mathlib leaf; no new nodes.
- `citations.json`: `[]`, because a Mathlib leaf has no proof steps citing DAG nodes.
- `searches.jsonl`: the unedited log written by msearch.py. Every new mathlib_searches entry copies its tool and query exactly; source hits were read.

## Attachments

None. The previous ATTACH result was rejected, and this delivery does not ask to attach a project declaration. The current read clone does now contain compTrace and the related theorems in `lean/WeilConjectures/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`, lines 58, 68, 78 and 86; I read them as corroborating source only. No closure or axiom claim about those project declarations is needed for the Mathlib result.

## WANTED

None.

## Corrections and source comparison

I read the item and its blueprint_update, the old and current detailed blueprint definitions, both unit texts, and the chapter record. The delivered statement follows `literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-char/def-fd-additive-character.md` (order 3016) as required: it includes arbitrary F' of characteristic different from p, values in F'(μ_p), arbitrary fixed nontrivial Ψ, and the primitive scaling clause. The imported scheme-conventions dependency defines scheme morphisms and is not used here. It is replaced by the existing definitions of ℓ-adic numbers and an algebraic closure, with their actual roles named in the text. No statement dispute was found. No hypothesis or conclusion was weakened.

The blueprint's suggested primitiveChar is only a chosen character, not a theorem saying that an arbitrary Ψ is the chosen one. The delivery therefore records the general composition, injective precomposition, trace surjectivity, and nontrivial-implies-primitive declarations too. It does not infer equality with Mathlib's canonical choice. The unit's additional ψ_n trace-transitivity clause belongs to sk-def-char; the assigned detailed definition does not state that clause. No unit realization file is changed.

## Mathlib match, clause by clause

1. `AddChar` (Mathlib/Algebra/Group/AddChar.lean:70) applied directly to a units codomain defines exactly the homomorphisms in the statement. Nontriviality is ψ ≠ 1, where the trivial character is identically 1 (same file:185, 194, 249–251). If field-valued AddChar is preferred, `val_isUnit` (:375) gives its units interpretation. Thus no continuity condition or stronger injectivity condition is introduced, including for the algebraic closure of a finite field.
2. `AddChar.compAddMonoidHom` (:232) with `(Algebra.trace (ZMod p) k₀).toAddMonoidHom` is exactly ψ(x)=Ψ(Tr(x)); its evaluation lemma is at :238. The trace definition in Mathlib/RingTheory/Trace/Defs.lean:71 is the trace of multiplication, hence the usual field trace (Stacks Tag 0BIF). `CyclotomicField` in Mathlib/NumberTheory/Cyclotomic/Basic.lean:654 and its cyclotomic-extension instance :674 give F'(μ_p). The assumption char F' ≠ p ensures p is nonzero in F', so that instance applies. Existence is also supplied by primitiveZModChar and primitiveChar, but the definition fixes Ψ and does not require identifying it with that choice.
3. `Algebra.trace_surjective` (Mathlib/RingTheory/Trace/Basic.lean:521) has precisely finite-dimensionality and separability hypotheses. They hold for k₀ over its prime field: `Module.Finite.of_finite` (Mathlib/RingTheory/Finiteness/Basic.lean:241), `PerfectField.ofFinite` (Mathlib/FieldTheory/Perfect.lean:308), and `Algebra.IsAlgebraic.isSeparable_of_perfectField` (:338). Apply the inequality-preserving function from `AddChar.compAddMonoidHom_injective_left` (Mathlib/Algebra/Group/AddChar.lean:241) to Ψ ≠ 1; the composite of 1 is definitionally 1. This is a one-line specialization of the injectivity theorem with the trace-surjectivity witness, giving ψ ≠ 1. No theorem about the value Tr(1) is used.
4. `AddChar.IsPrimitive.of_ne_one` (Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean:84) specialized to k₀ and ψ ≠ 1 gives the last clause directly. Its conclusion unfolds by `IsPrimitive` (:61) and `mulShift` (Mathlib/Algebra/Group/AddChar.lean:438, evaluation :441) to ∀ a ≠ 0, (x ↦ ψ(ax)) ≠ 1. Thus it is one Mathlib application for this clause.

This is a Mathlib leaf under the project's convention permitting a few Mathlib declarations, one per clause, and one-line specialization. No new intermediate lemma or renamed copy of the definition is needed. The legacy Mathlib search is retained; all additional searches were actually run through msearch.py and are in searches.jsonl. Loogle found composition and injective precomposition; LeanFinder found the primitive theorem and canonical construction, then the second phrasing found injective precomposition; LeanSearch found composition. The later grep queries locate and confirm the exact local declarations and lines. No unavailable search was recorded as absence.

## Not duplicates

There are no new nodes and hence no new/existing duplicate pairs. Whole-DAG and blueprint searches for additive characters, primitive characters, cyclotomic extensions and trace nondegeneracy were read. `sk-def-char` is recorded in blueprint.same_as because it states the same character convention with the additional extension-field notation. It is not used circularly as a dependency.

## Review by Q142

I reviewed delivery-errors B–E with the detailed blueprint and the actual Mathlib source open. The item is delivered as a leaf, so there are no numbered DAG proof steps or new nodes to inspect; the four numbered clause checks above are the complete mathematical identification and their exact declarations and hypotheses. In particular I checked that arbitrary Ψ is preserved, that the codomain really is a multiplicative group, that trace means the field trace rather than an absolute trace with another base field, that finite-dimensionality and separability follow from a finite field, and that the primitive theorem assumes only nontriviality and a field domain. I opened both existing statement-dependency nodes: def-weil-l-adic-numbers states the field Q_ell, and def-weil-algebraic-closure states the algebraic-closure notion for both k and Qbar_ell; neither is used for a property it does not state. No scheme convention, SGA reference, self-reference or hidden off-unit tool is used.

For small cases: k₀=F_p has identity trace, so ψ=Ψ. In characteristic 2 the only nonzero scaling in F_2 is 1, so the primitive assertion is exactly nontriviality; no sign exception occurs. For F_4/F_2, Tr(1)=0, but if t²+t+1=0 then Tr(t)=t+t²=1; the induced nontrivial character is therefore still nontrivial. This verifies the important case p dividing the extension degree and explains why the proof must not evaluate only at 1. The excluded scale a=0 does give the trivial character, as mulShift_zero states. Trivial Ψ would give a trivial composite and is explicitly excluded. A nontrivial additive character on an algebraic closure need not be injective, and the first clause asserts no such thing. Distinct coefficient characteristic matters for choosing Ψ, while trace surjectivity and scaling primitivity use no extra coefficient restriction. No case forces an unstated hypothesis.

I did not produce Lean files, run compilers, edit the shared repository, edit launcher tools, or start agents. Since the leaf has no proof steps there is no long step hiding a lemma and citations.json is correctly empty. The preserved blueprint_update and import flags still record the historical import; the substantive current statement and mathlib_match now resolve it.

## Unfinished work

None in the mathematical delivery. The required remote dry run and push are performed after this report is written; their results are reported by the delivery command.
