## What changed

Repair of the return at ad0f264db: removed the duplicate private theorem
`AlgebraicGeometry.Scheme.Modules.coherent_iso`. The zero-filtration proof now imports
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum` and directly applies the existing
isomorphism clause of `AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`.
The cited downstream `coh_iso` is private and its module imports this item; importing it
here would form an import cycle. The reused general ringed-space theorem avoids that
cycle and proves the required instance without duplicating an isomorphism lemma.
Added the existing item node to the sandbox with its proof route and dependencies
updated to match the delivered support-induction proof. No signatures changed.
The second-reading record below predates this repair and requires a fresh reader.

Added the main support-induction proof in `CoherentFiltrationIntegralSubschemes`. The proof handles the empty-support, reducible-support, irreducible-support, adic-reduction, and generic-point cases. Added three named intermediate modules for extension, adic reduction, and the generic-point step; their statements are documented and imported by the main proof.

## Proved and sorry left

One of one original holes is closed; three strict intermediate holes were added, so
this is a decomposition, not a complete proof of the target closure. The repair adds
no new hole. It also uses the existing library theorem
`AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`, whose library proof
currently contains `sorry`; that existing declaration is not delivered or changed.

The target declaration `exists_coherent_filtration_integral_subschemes` is proved from the three intermediate declarations and the existing support lemmas. Sorry remains in `coherentIntegralFiltration_of_shortExact`, `coherentIntegralFiltration_of_generic_annihilated`, and `coherentIntegralFiltration_generic_step`; each has its own node and complete proof description.

## No longer needed

The duplicate helper `coherent_iso` is removed; its finite-local-generator transport
proof is no longer needed in this item. The downstream module
`CoherentPropertyDevissageIntegralSubschemes` is not imported. The added proof-only
import `CoherentKernelCokernelSum` supplies precisely the isomorphism clause used
in the length-zero filtration. No previously delivered import was removed in this repair.

Compared with the repository baseline, the main proof also removes the direct
imports `Sheaf.Algebra.Homology.ModuleStalkExact`,
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`, and
`Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills`. Their nodes
`lem-weil-pbc-module-stalk-exact`, `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`,
and `lem-weil-pbc-coherent-support-power-ideal-kills` are not direct dependencies
of the main support-induction proof; they remain part of the intermediate arguments.

The main proof does not use `CoherentFormalModule`, `CoherentGenericPointIdealInclusion`, `ClosedImmersionCoherentEquivalence`, `ClosedPushforwardStalks`, `IdealModuleProductStalk`, `Modules.IdealTimesQuasiCoherentAffineSections`, `ReducedInducedClosedSubscheme`, or `TensorPullback` directly; these imports were removed from the item module. Their statements remain available to the named intermediate nodes' future proofs.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery and second reading missed the existing coherence-isomorphism
fact and duplicated it as a private helper. The return is repaired by using the
existing general theorem instead. The prior delivery also omitted the item node
update required by its decomposition; the sandbox now includes that update.

The DAG proof plan is mathematically sound but too large for a direct Lean proof in this item. The argument is decomposed into three strict intermediate statements corresponding to the extension, adic, and generic-point steps.

## New nodes

`def-weil-pbc-coherent-integral-filtration`, `lem-weil-pbc-coherent-integral-filtration-extension`, `lem-weil-pbc-coherent-integral-filtration-adic-reduction`, and `lem-weil-pbc-coherent-integral-filtration-generic-step`.

## Earlier second reading (a previous round; superseded)

The main theorem statement is unchanged. The three intermediate statements are strict subarguments: extension concatenation, adic reduction, and generic-point reduction. Their remaining proofs are named and documented for parallel takeover.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered item module against the repository version. The target declaration
   `exists_coherent_filtration_integral_subschemes` has the identical signature and unchanged
   statement; only its proof and proof-only imports changed. Verdict: passed.
2. I compiled all five delivered modules with `lcompile.py --all`; compilation completed without
   errors or warnings. The three remaining `sorry`s are exactly the named split-off theorems
   `coherentIntegralFiltration_of_shortExact`,
   `coherentIntegralFiltration_of_generic_annihilated`, and
   `coherentIntegralFiltration_generic_step`; no definition contains `sorry`. Verdict: passed,
   pending completion of those declared nodes.
3. The split-off declarations are strict intermediate results (extension, generic annihilation,
   and generic-point step), each weaker than the target and each required by the main proof. Their
   statements are mathematically the corresponding clauses of the Stacks 01YF argument and have
   matching DAG nodes. No duplicate declaration was found in the repository or Mathlib. Verdict:
   passed.
4. The proof follows support induction: zero support, reducible support via a short exact
   sequence, irreducible support via generic annihilation, and the generic-point reduction. The
   unit route through the filtration predicate and its three supporting steps is retained. Imports
   removed from the item are listed above; proof-only imports added to the item are private.
   Verdict: passed.
5. The DAG records for the filtration predicate and all three split-off theorems match the Lean
   module names, declarations, and statements. The unit is `sk-thm-p1`, and the report records the
   remaining holes and their nodes. Verdict: passed.

I changed only the report by adding this second-reading record; no Lean declaration or DAG
statement was altered during review.

## Second reading by N1

1. I compared the delivered item module against the repository version. The target theorem
`exists_coherent_filtration_integral_subschemes` has the identical signature and statement;
only proof-only imports, helper proofs, and the proof body changed. The three added modules
contain new intermediate declarations and do not alter an existing repository declaration.
Verdict: passed.

2. I compiled all five delivered modules with `lcompile.py --all`; all compiled without errors
or warnings. The only remaining `sorry`s are the three named split-off theorems
`coherentIntegralFiltration_of_shortExact`, `coherentIntegralFiltration_of_generic_annihilated`,
and `coherentIntegralFiltration_generic_step`; no definition contains `sorry`, and no forbidden
axiom or unsafe construct was introduced. Verdict: passed.

3. The split-off statements are strict intermediate results: extension concatenation,
adic reduction, and the generic-point step. Each is weaker than the target and is required by
the support-induction proof. Their source docstrings describe the corresponding Stacks 01YF
arguments, and the node records identify the declarations. No duplicate declaration was found
in the repository or Mathlib. Verdict: passed.

4. The proof follows closed-support induction: zero support, reducible support by the existing
support-union exact-sequence theorem, irreducible support via generic annihilation, and the
generic-point step. The unit route through the filtration predicate and its three supporting
steps is retained. Removed imports and their no-longer-direct proof dependencies are listed
above; `CoherentKernelCokernelSum` is the needed proof-only coherence-isomorphism import.
Verdict: passed.

5. The item node and the four added node records match the Lean module names and declarations,
and all use unit `sk-thm-p1`. The item node proof and proof dependencies record the actual
support-induction route; each split-off theorem has a matching node and complete proof
provenance in its declaration docstring. Verdict: passed.

I changed only this report section during the second reading.
