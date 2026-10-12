## What changed

Replaced the body of `Algebra.exists_presentation_localized_conormal_basis`, preserving its
existing signature byte for byte. The proof handles a zero localization with the empty basis
of the original presentation. For a nonzero localization, it applies the fixed-size
stabilization construction, then proves the variable-count bound directly from
`Algebra.Presentation.localized_conormal_equiv` and Mathlib's
`Module.Basis.card_le_card_of_linearIndependent`.

Added the proof-only imports `Sheaf.RingTheory.SmoothStableConormalBasisAux` and
`Sheaf.RingTheory.PresentationLocalizedConormalSplit`. The Mathlib rank and coordinate-basis
results are already available through the necessary imports; their redundant direct imports
were tested and removed.
The construction module's public imports are needed for its statement. No definition,
existing public signature, visibility, or target statement changed; no change record is needed.

## Proved and sorry left

Original hole closed:

- `Algebra.exists_presentation_localized_conormal_basis`
  (`lem-weil-pbc-smooth-stable-conormal-basis`). Its body is now a checked reduction, but its
  axioms still include `sorryAx` from the construction below: this is not an axiom-free proof.

New hole added:

- `Algebra.exists_stabilized_presentation_localized_conormal_basis`
  (`lem-weil-pbc-smooth-stable-conormal-basis-unbounded`, in
  `Sheaf.RingTheory.SmoothStableConormalBasisAux`). This construction asserts exactly
  `n₀ + r` variables and a `Fin q` basis of numerator relations, without a smoothness
  assumption or a variable-count bound. Its complete construction proof is in its docstring
  and node.

The first worker's rank hole `Algebra.localized_conormal_basis_rank_le_variables` was false
without a nonzero-localization assumption. The second reader proved the correctly restricted
rank step and inlined it into the original theorem, deleting its unnecessary new module/node.
The first worker's construction hole
`Algebra.exists_presentation_localized_conormal_basis_unbounded` was replaced by the fixed-size
construction above. Neither superseded declaration is delivered.

Thus this is a decomposition: one original hole closed and one new hole added, net zero
for these directly edited declarations. Actual target-closure and module-pruning figures
belong to the pinned-baseline sorry ledger and were not measured here. It closes the independent rank argument and the zero-localization case,
and leaves the stabilization/denominator-clearing construction open. No global sorry-ledger
or global pruning claim is made. Both delivered modules compile without errors or warnings.
A scratch `#print axioms` check of the main theorem and the remaining construction showed only
`propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. The rank step, checked
as a temporary standalone theorem before inlining, used only the three permitted axioms.

## No longer needed

Removed direct proof-only import `Sheaf.RingTheory.SmoothLocalizationConormalSplit` and its
old direct proof dependency `lem-weil-pbc-smooth-localization-conormal-split`, replacing the
quotient-form splitting route with the existing presentation-form splitting theorem.

The other old direct proof dependencies
`def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-finitely-presented-algebra`, and
`def-weil-pbc-module-localization-away` are no longer direct proof dependencies of the main
node. They remain statement dependencies and dependencies of the construction node, so are
not globally pruned. The new rank module/node was removed before delivery because the rank
argument is a direct application of existing library and Mathlib results.

## Where the brief, the DAG or earlier work was wrong

The first worker's unrestricted rank lemma is false. Over the zero ring the zero module has a
basis indexed by every finite type (`Module.Basis.uniqueBasis`), so even a zero-variable
presentation can admit a `Fin 1` localized conormal basis satisfying the relation-value
condition. For instance take `R = A = ℤ`, `a = 0`, the identity presentation with no variables
and one redundant zero relation; `A_a` is the zero ring and hence smooth. Its `Fin 1` basis
has the required zero vector value, but `1 ≤ 0` is false. The original existential theorem
is unaffected: it can choose `c = 0`, as the repaired proof does.

The new rank node had the placeholder statement `stmt2`, omitted the splitting dependency,
and stored prose instead of its verbatim Lean signature. It has been removed. The construction
node also lacked a verbatim Lean signature, complete proof details, the blueprint tag in its
Lean docstring, and all required search kinds. These have been repaired. The report previously
called the result simply proved despite adding two holes; the hole accounting is now explicit.

WANTED: `literature/stacks-project/smoothing.tex`, Tag 07EZ, proof of (e), for
`lem-weil-pbc-smooth-stable-conormal-basis-unbounded`. This machine has no local copy. The
second reader checked the published source at https://stacks.math.columbia.edu/tag/07EZ and
recorded the detailed reconstruction as agent-written. LeanSearch was attempted and returned
Internal Server Error; successful LeanFinder, Loogle, and Mathlib-source searches are recorded.

## New nodes

`lem-weil-pbc-smooth-stable-conormal-basis-unbounded` records the fixed-size stabilization,
the conormal product equivalence, denominator clearing, and extension of numerator relations
to a finite generating list. It remains strictly below the original theorem: it neither assumes
smoothness nor asserts the bound on the number of variables. Its variable and basis sizes are
fixed by the input, so it is a concrete construction subproblem, rather than the original
existential statement under another name. Its `lean.statement` is copied verbatim from the
new theorem. There are no change records and no delivered rank-bound node.

## Second reading by C4

1. Compared every delivered existing module with the repository using `diff`; the original
   declaration signature is byte-for-byte identical. Only imports and its proof body changed.
   The other delivered module is new. No definitions or visibility changed. Verdict: pass.
2. Compiled the modules locally in import order through `lcompile.py`; no errors or warnings.
   Searched for forbidden declarations and data holes; none. Exactly one `sorry` remains, in
   the named construction theorem listed above. Scratch axiom checks show precisely the
   permitted axioms plus the expected construction `sorryAx`. Verdict: pass as a decomposition.
3. Checked the split statement against Tag 07EZ(e), including `r = 0`, `q = 0`, empty variable
   sets, and zero localization. Its conormal construction and finite generating list work in
   these cases. Repeated searches with different phrases using LeanFinder, Loogle, grep, and
   attempted LeanSearch. Mathlib's `Generators.exists_presentation_of_basis_cotangent` requires
   an unlocalized basis and adds an invertible variable, so does not supply the fixed-size
   localized construction. No duplicate was found in either library root. The false rank
   hole was eliminated. Verdict: pass for the remaining construction.
4. Used the existing presentation-form conormal equivalence and the Mathlib rank estimate
   directly, retaining only one construction hole. Removed the old splitting import and the
   redundant new rank module. Checked `dag/units/sk-thm-p1.json`: neither this tool node nor
   the removed splitting node realizes a unit statement or step. The unit's `realized` routes
   and all chapter/unit steps stay intact. Verdict: pass.
5. Checked both delivered nodes against the Lean: their declarations, verbatim signatures,
   proof steps, and unions of `uses` in `proof_deps` agree. The new node has its source,
   complete proof, search records, `status`, `created`, `blueprint`, chapter/unit, and Lean
   record. Only permitted fields of the existing node change. Verdict: pass.

Changes made in the second reading: fixed the zero-ring fault; proved and inlined the rank
argument; replaced the weak unbounded construction by its fixed-size form; expanded its
proof/source docstring; repaired the node metadata/search records; removed the rank module
and node and two redundant Mathlib imports; corrected the pruning report and decomposition accounting.

Independent rank searches: LeanFinder query "A linearly independent family in the finite free
module over a nonzero commutative ring has at most its rank elements" found
`Module.Basis.card_le_card_of_linearIndependent`; Loogle confirmed that declaration;
Mathlib grep for `card_le_card_of_linearIndependent` found its implementation in
`LinearAlgebra/Dimension/StrongRankCondition.lean`. These yielded the direct proof above.
LeanSearch for a basis of a direct summand returned Internal Server Error. The item node's
existing search history is preserved because stage 3 does not own that field.
