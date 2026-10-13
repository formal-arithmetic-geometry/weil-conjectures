## What changed

Replaced the saved invalid split with a categorical reduction of the original theorem.
The assigned module preserves its statement and public imports. It now imports two new
proof modules. The transition-epi module proves that every shifted quotient transition
is epi directly from hc, hS, naturality, abelian images and quotient projections.
The transition-exact-bound module isolates the Artin--Rees kernel computation.
The main proof combines these facts using ShortComplex.Exact.gIsCokernel and the
uniqueness of cokernels, including the required projection factorization equation.
The unit sk-thm-p1 route is unchanged; this node realizes none of its fixed steps.
All three modules compile. This is a decomposition, not a sorry-free Artin--Rees proof.

## Proved and sorry left

Closed the assigned hole
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_comparison_bound`.
Proved the new declaration
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_transition_epi` with no sorry.
Added one hole:
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_transition_exact_bound`, node
`lem-weil-pbc-formal-kernel-quotient-transition-exact-bound`.
No other sorry remains in delivered files. Thus one hole closed and one added (net zero).
The new exactness statement omits epimorphy and any quotient isomorphism; those are
proved and assembled separately in Lean. Its docstring gives the affine computations,
uniform bound and locality argument, including zero/unit ideals and empty schemes.

## No longer needed

Removed these direct proof imports from the assigned module:
- Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
- Sheaf.RingTheory.AdicCompletionNoetherian
- Mathlib.RingTheory.Filtration
- Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
- Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

The old direct proof-dependency nodes no longer used by the assigned proof are
`lem-weil-pbc-coherent-formal-modules-affine`,
`lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-artin-rees`,
`lem-weil-pbc-coherent-kernel-cokernel-locnoeth`, and
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`.
They remain in the deferred exactness-bound node's proof plan, whose module now imports
them as plain proof imports. They are not claimed as globally pruned. No existing node or module is globally dispensable.
Deleted the earlier attempt's unpublished BoundExists and ComparisonStep modules and
nodes. Neither is used in this delivery.

## Where the brief, the DAG or earlier work was wrong

The missing compiled ShiftedQuotient module reported by the previous worker is now
available. The previous ComparisonStep statement had invalid syntax and asserted the
comparison for arbitrary b without a bound hypothesis. Its caller ignored the hb it
obtained. Both proposed nodes copied the parent's statement instead of their own
signatures and lacked complete proof plans; both have been replaced.
The repository does not contain the cited Stacks coherent.tex or the unit source text;
Stacks 087X was read online at https://stacks.math.columbia.edu/tag/087X.
The unit record was read locally. No repository source or target signature was edited.
No definition, existing statement or public visibility was changed.

## New nodes

`lem-weil-pbc-formal-kernel-quotient-transition-epi` records the proved surjectivity step:
a common high kernel maps epimorphically onto both stabilized images, and naturality
identifies the induced S transition. Quotient projections then give epi transitions.

`lem-weil-pbc-formal-kernel-quotient-transition-exact-bound` records the remaining
Artin--Rees bound identifying the transition kernel with the ideal-product image.
Its statement, full proof in words, source, dependency plan and Lean record are supplied.
No change records or forced adaptations are required.


## Second reading by Y3

1. Compared the existing module with the repository using diff and an exact text
   comparison of its theorem signature. Verdict: unchanged byte for byte, including
   hc, hS, the uniform bound, every d and n, and the projection factorization equation.
   Its public import and visibility are unchanged. The delivery introduces no definitions
   and changes no target or existing interface; no change record is required.
2. Compiled all three modules in import order with lcompile.py, without errors or
   unexpected warnings. Scanned for forbidden declarations and all sorry occurrences.
   The sole sorry is the entire proof of the named transition-exact-bound theorem.
   A scratch copy with #print axioms shows propext, Classical.choice and Quot.sound for
   transition_epi, and those plus sorryAx for the comparison and exactness-bound
   declarations. Verdict: the categorical reduction and epi result are kernel-checked;
   the Artin--Rees step is explicitly still open. No arbitrary witness is made into data.
3. Read the new theorem statements, docstrings, nodes and Stacks 087X online.
   The epi result is valid for every shift: hS makes both j components mono; hc
   identifies a common high kernel image at the lower level; naturality and mono
   cancellation identify its epi factor with the S transition; quotient projections
   transfer epimorphy. The exactness hole asserts only the zero composite and equality
   of the transition kernel with the ideal-product image, without surjectivity or the
   quotient comparison isomorphism. This is a strict part of the argument, assembled
   with the independently proved epi result by cokernel uniqueness, not a renamed
   restatement. Checked n=0, c=0, d=0 where permitted, zero modules, the zero ideal,
   unit ideal and empty scheme. The affine formula is L/I^(n+1)L and the transition
   kernel I^(n+1)L/I^(n+2)L, so these cases satisfy the assertion. Independent msearch
   LeanFinder and grep queries with different wording found completion transition
   lemmas but no matching bound; direct rg found the existing affine kernel-image
   comparison and formalTransition_epi, neither of which supplies this theorem.
   Loogle found Abelian.instEpiFactorThruImage, already used by inference in the proof.
   Verdict: no duplicate; no split-off hole could be closed in a few minutes.
4. Checked the proof from the comparison down through gIsCokernel and cokernel
   uniqueness, including its equation at WalkingParallelPair.one. These are existing
   Mathlib results; no shorter available sheaf bound was found. The original proof-only
   imports have moved to the deferred exactness module, not vanished from the closure.
   All five old proof dependencies no longer directly used are now listed above.
   Read dag/units/sk-thm-p1.json: the assigned node is absent from every realized
   statement/step list. Verdict: only a below-unit tool reduction; unit route preserved.
5. Compared all three Lean signatures with their node lean.statement records, checked
   new-node fields and the uses/proof_deps unions. The existing node changes only
   proof, proof_deps and proof_origin; its proof describes exactly the Lean assembly.
   The new epi node describes the proved image-factor argument. The exactness node
   retains the affine equivalence, Noetherian completion, Artin--Rees, coherent closure,
   ideal-product sections and shifted-quotient dependencies of its remaining proof.
   Verdict: Lean and DAG agree after the documentation repair below.

Changed: supplied source and blueprint references in both new module docstrings;
expanded the exactness docstring and node proof with the explicit inverse-image
Artin--Rees formula and the simultaneous choices l >= m+a and l >= m+c;
restored its five planned dependency imports as plain proof imports; added independent
search evidence to the new nodes and completed the direct-dependency pruning list.
No theorem signature or existing proof was rewritten. Recompiled the changed set and
checked axioms. This delivery closes one assigned hole and adds one strictly smaller
hole; net zero, a decomposition, with a separately sorry-free epi theorem.
