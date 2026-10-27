# Stage-1 report: lem-sfb-shifted-cup-adjunction-transpose

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-shifted-cup-adjunction-transpose.json`: item, statement; split into five steps, unchanged statement and statement dependencies. Mathlib has the separate adjunction ingredients but no declaration found for the complete shifted-unit transpose assertion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-tensor-unit-monoid.json`: new statement, Mathlib leaf `CategoryTheory.Mon.trivial`, `Mathlib/CategoryTheory/Monoidal/Mon.lean:270`; its monoid instance is at lines 130–134. This is the input monoid needed by the existing lax-monoidal transport theorem, not another cup-transpose lemma.
- `citations.json`: eight verbatim citations for every step/node pair.
- `report.md` and the actual search command's `searches.jsonl`.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag/id and for shifted cup, cup transpose and rightAdjointLaxMonoidal. The monoidal and cup declarations found concern site-specific functors, braiding, projection formula or unshifted ingredients; none states all the clauses for arbitrary additive monoidal adjunctions with the specified shifts. The new tensor-unit construction is in Mathlib, not a project attachment.

## WANTED

WANTED: an exact non-SGA expository reference for the generic shifted-unit cup transpose, for lem-sfb-shifted-cup-adjunction-transpose. The current blueprint direct-image proof, paragraph (3), supplies the contextual route but does not contain this internal-bar normalization. Its missing generic argument is supplied here as an agent proof. The generic ingredients are present in the local Mathlib source and in the existing DAG leaves; no external source was downloaded or represented as read.

## Findings and corrections

The item had an empty proof. No statement error was found and no hypothesis or conclusion was changed. The proof now spells out the inverse tensor-comparison direction, the counit naturality square, the comparison h_n, the exact compatibility equation for r, and precomposition with h_(p+q)^(-1). No braiding or claim about cohomology classes represented by generators is used. The degree-zero identity follows separately from the unit mate, without assuming normalization of the freely chosen r_(0,q).

The nearest-blueprint command prints `None`: the inherited created.item chain ends at `Sheaf.SixFunctors.CtfStabilityDirectImages`, which is not a DAG node. The item already records a null blueprint.from.node. I retained that truthful result and its via list, with a specific place, and gave the new leaf the same result with this item prepended. The direct-image paragraph is contextual, not falsely claimed as a source proof. The source file was read through `literature/blueprint/latest/` as required.

The unit record is not changed: this generic algebra lemma is neither the unit's key statement nor a replacement for its direct-image preservation route. All off-unit citations are already Mathlib leaves and serve as general categorical tools.

## Not duplicates

lem-sfb-tensor-unit-monoid vs det-def-sfb-ring-object-monoid: the latter defines arbitrary monoid objects and their axioms; it does not assert that the tensor unit with left-unitor multiplication satisfies those axioms.

lem-sfb-tensor-unit-monoid vs det-def-sfb-ring-object-transport: the latter transports a given monoid along a lax functor, and needs the former as its input for the tensor unit; it does not construct that input.

Whole-DAG searches for tensor-unit/monoid terminology, Mon.trivial and the exact new id, and whole-blueprint searches for `unit monoid` and `trivial monoid`, found no node stating this fact. Whole-blueprint searches for `monoidal adjunction` and `shifted-unit` found no duplicate of the item. No Stacks tag is attached to the new leaf: its exact source is Mathlib's construction, so there are no same-tag pairs to justify.

## Review by NF

I read the chapter and unit records, SETUP's three blueprint levels, GOAL, the worker/stage-1 instructions and delivery-errors B–E, including the duplicated historical section. For the item I read the current blueprint paragraph (3); it establishes the direct-image context and omits this generic cup calculation. I therefore kept the inherited source as context and explicitly marked the proof as agent-written. For the new leaf I read Mon.lean:130–134 and 266–270: the unit is identity, multiplication is the left unitor, and associativity and both unit laws are proved there. The hypotheses are only a monoidal category, with no braiding or additive assumption. I also read the local mate construction at Functor.lean:947–950, the compatible-adjunction class and its instance at 1002–1015, the normalized counit equations at 1030–1040, and the monoidal unit/counit instances at NaturalTransformation.lean:137–156.

Step 1 uses the full statement of lem-sfb-monoidal-adjunction-mates for existence of the lax right adjoint and its unit mate, and lem-sfb-monoidal-adjunction-unit-counit for both monoidal transformations. The latter defines monoidality with the tensor and unit equations. Expanding the composite lax structure of LF and composing with the inverse comparisons gives exactly the displayed normalization; strongness of L and mate compatibility are hypotheses of the item. No assertion that F is strong is used.

Step 2 uses the new leaf to make I_D a monoid, then clause 1 and the explicit multiplication/unit formulas of det-def-sfb-ring-object-transport. I checked those formulas against M and e; F preserves the identity, so its transported unit is precisely e. This is the whole reason for the new leaf, and is strictly less than the item's adjunction/shift claims.

Step 3 uses lem-weil-pbc-adjunction-of-natural-bijection: its statement explicitly gives inverse transpose epsilon followed by L of the arrow, as well as naturality of the counit. The two adjoint equations have source L(S_p) and L(S_q), respectively. The r compatibility is an assumption of this item, here written as an equation with h_(p+q) on the right; it is not inferred from shift compatibility alone.

Step 4 uses that same inverse-transpose statement and the monoidal-counit statement from step 1. I checked every source and target in the calculation: L(C tensor C), LF(I tensor I), L(S_p tensor S_q), and L(S_(p+q)) appear in the required order. Counit naturality applies to m:I tensor I -> I, tensorator naturality applies to a:S_p -> C and b:S_q -> C, and the h-equations remove exactly the chosen comparison maps. No swapping of factors or additional sign convention is inserted. These are elementary substitutions from the cited statements, not an unnamed tensor-mate lemma.

Step 5 uses the explicit unit mate in lem-sfb-monoidal-adjunction-mates. With the coherent zero-shift identifications h_0 is ell and shifting the identity is the identity; its adjoint is e. It does not assert cup associativity for arbitrary r, which the item does not require.

I tested the identity adjunction with trivial shifts: h is identity and the formula reduces to the defining ordered product for any common choice of r. With negative p or q there is no induction or nonnegative-degree argument, only the given isomorphisms. For p=q=0, the unit equation holds independently of r; no extra unit-normalization hypothesis on r is introduced. Zero morphisms and the zero category satisfy all the equalities. The proof never uses symmetry, so it applies in the nonsymmetric monoidal setting stated. Every proof step is under 2000 characters (lengths 651, 339, 527, 896, 305); no long hidden lemma remains. All non-elementary facts are supplied by cited node statements, whose relevant sentences/formulas were checked verbatim in citations.json. The union of uses is exactly proof_deps. The new Mathlib node is statement-only, with no proof or proof dependencies. Its search records are the actual successful or empty responses recorded by msearch, including the unsuccessful spelling of the instance and the later exact Mon.trivial search.

## Unfinished work

No mathematical clause remains unfinished at this split level. Required server checks and delivery are run after this report is written; their terminal outcomes determine the final response. No Lean was written, no compiler/Lake/build tool was run, and no shared repository or launcher file was modified.
