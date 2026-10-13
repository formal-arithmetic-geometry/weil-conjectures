## What changed

Corrected and reduced `AlgebraicGeometry.coherentFormalModule_kernel_quotient_aux`.
Its inputs stay the same; its output now chooses `d ≥ c`, and uses d for the shifted
quotients and eventual-kernel equation. This repairs the existing false fixed-bound
statement following Stacks 087X. No target statement changes.

Added four modules:

- `Sheaf.AlgebraicGeometry.CoherentFormalModuleShiftedQuotient` explicitly constructs
  the quotient functor and its descended map using quotient reductions and cokernel
  descent. Its data use no choice from an existence theorem.
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotientInclusionBound` proves
  eventual kernel vanishing for any inverse system embedded componentwise into F.
  This is entirely a monicity/cokernel argument and does not need Artin--Rees.
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotientAdicBound` proves
  coherence and annihilation of every quotient term, then assembles coherent adicness
  from the strictly smaller successive-comparison statement.
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotientComparisonBound` states
  the remaining eventual successive quotient comparisons, with a complete affine
  Artin--Rees proof in its docstring and node. It imports the existing declarations
  needed for that proof plan.

The main proof chooses a sufficiently large bound, packages the explicit quotient
functor with its adicness proof, takes identity level isomorphisms, proves the two
compatibility equations, and uses the proved kernel-vanishing theorem. Thus the
remaining hole is only the successive reduction comparison; no object is selected
from an unproved arbitrary existence claim.

The sole external declaration user,
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelConstruction`, is forcibly adapted
without changing its signature or visibility. Its original imports and docstring are
unchanged. It retains the stabilized system S and transports both stabilization and
its image identifications from c to the larger d using hc and Subobject.isoOfMkEqMk.

Change record: `coord/changes/coherentFormalModule_kernel_quotient_aux.md`.

## Proved and sorry left

Closed the hole in the **corrected**
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_aux`
(node `lem-weil-pbc-formal-kernel-quotient-aux`). The old false fixed-bound statement
is not claimed to have been proved.

New declarations with complete proofs:
`AlgebraicGeometry.shiftedQuotient_kill`,
`AlgebraicGeometry.formalShiftedQuotientι_comp`,
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_inclusion_bound`, and
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_adic_bound`.
The definitions `AlgebraicGeometry.formalShiftedQuotient` and
`AlgebraicGeometry.formalShiftedQuotientι` have real data and proved structural laws.
The adapted `AlgebraicGeometry.coherentFormalModule_kernel_construction` remains proved.

Exactly one added and remaining sorry:
`AlgebraicGeometry.coherentFormalModule_kernel_quotient_comparison_bound`
(node `lem-weil-pbc-formal-kernel-quotient-comparison-bound`). It asserts only eventual
successive quotient isomorphisms of an explicitly defined system. It asserts neither
coherence, annihilation, a morphism to F, its compatibility, nor kernel vanishing.
Those parts are proved separately in Lean. The delivery is a correction and
one-hole decomposition: one upper hole closed and one strictly smaller hole added;
net holes closed minus added is zero, not a completed Artin--Rees proof.

All six delivered modules compile together in import order; each takes under ten
seconds. The original construction proof fails against the corrected auxiliary,
while the adapted proof compiles. No sorry occurs inside a definition or private helper.

## No longer needed

Removed these direct proof imports from the assigned quotient module:
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`,
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`,
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`Sheaf.RingTheory.AdicCompletionNoetherian`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, and
`Mathlib.RingTheory.Filtration`.

The first, second, third, fifth, and seventh are retained where needed in the new
comparison/adicness modules. The separate quasi-coherent kernel and cokernel/image
steps (`lem-weil-pbc-quasi-coherent-module-kernel` and
`lem-weil-pbc-quasi-coherent-module-cokernel-image`) are not required by this proof:
coherent kernel/cokernel closure gives coherence of the image, and the existing
coherence criterion gives its quasi-coherence. The corresponding direct imports
are removed, but they may remain transitively reachable through other modules.
No whole module is claimed to leave the targets' import closure.

Removed no imports from the forcibly adapted caller: its edits are limited to the
lines forced by the changed interface. Its DAG proof dependencies now name the
stabilized and corrected quotient auxiliaries it actually applies.

## Where the brief, the DAG or earlier work was wrong

The existing STATEMENT-DISPUTED comment was mathematically correct. Stabilization
of images at c supplies no Artin--Rees bound for the kernel inside the source.
For X=Spec Z, I=(2), F_n=Z/2^(n+1), H_n=Z/2, and reduction alpha, c=0 stabilizes the
termwise kernels S_n=2Z/2^(n+1). The stipulated quotient sequence starts with 0
then Z/2, so its first successive reduction cannot be an isomorphism. The old
auxiliary silently used the stronger choice of c in Stacks 087X. The corrected
auxiliary enlarges c; the caller already existentially chooses its bound, so its
unchanged statement is recovered by transporting the image identifications.

The final kernel-vanishing step did not need the planned second Artin--Rees
argument once the shifted quotient and its inclusion are explicit. Descent to
S_(n+d), followed by monicity of j_(n+d), proves it directly. Coherence and
annihilation also follow from existing declarations; only eventual quotient
comparisons need the remaining affine argument.

The local literature/stacks-project/coherent.tex source is absent on this machine.
Checked the full statement and proof of Stacks tag 087X at its official page,
https://stacks.math.columbia.edu/tag/087X. LeanSearch returned Internal Server Error,
recorded as unavailable, not as a negative search. LeanFinder and local searches
found quotient-system and subobject tools but no matching theorem. The blueprint
ancestor script returns None for the assigned auxiliary; new node ancestry records
that fact, with their exact 087X clauses and the auxiliary in via. The unit's
statement and realized proof steps are not changed.

## Forced adaptations

`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelConstruction` is unclaimed.
Original compiler error against the delivered changed auxiliary:

```text
CoherentFormalModuleKernelConstruction__probe.lean:97:26: error: Application type mismatch:
The argument K has type ℕ but is expected to have type CoherentFormalModule X I
in the application Exists.intro K
```

Changed lines: replace the quotient witness pattern at line 95 by
`⟨d, hcd, K, ι, e, heq, hι, hker⟩`; add hd proving stabilization at d by transitivity
of hc, and hSd transporting hS through the equality of images; use d, hd, hSd in
the final existential assembly. These lines are necessary because the auxiliary
now chooses d and its quotients are at shift d. All existing declaration signatures,
visibility, imports, and docstrings remain identical. The original compiles against
the baseline and the adaptation compiles against the changed dependency; deliver3.py
also performs both counterfactual checks.

## New nodes

`lem-weil-pbc-formal-shifted-quotient`: explicit quotient objects, transitions, functor
laws, and the inclusion defined by cokernel descent. Its construction is fully proved.

`lem-weil-pbc-formal-kernel-quotient-inclusion-bound`: the general monicity/descent
kernel-vanishing lemma, fully proved and independent of Artin--Rees.

`lem-weil-pbc-formal-kernel-quotient-adic-bound`: combines proved coherence and
annihilation with the eventual successive comparison bound. No local sorry remains.

`lem-weil-pbc-formal-kernel-quotient-comparison-bound`: the single remaining hole,
strictly limited to the canonical successive quotient comparisons. Its source and
complete affine Artin--Rees argument are included. Zero ideals, unit ideals, zero
modules, d=0 when allowed by the bound, and the empty scheme are covered.


## Second reading by V2

1. Compared all six delivered modules with the repository. Four are new. The only
   existing signature change is the declared enlargement of the auxiliary bound,
   with its change record. The construction caller's signature and visibility are
   byte-for-byte unchanged. The fixed-bound counterexample is valid, and allowing
   a larger bound repairs exactly that error without changing a target statement.
2. Compiled all six modules in import order with no errors or warnings. Searched
   for forbidden declarations and holes: exactly the named comparison theorem has
   `sorry`; no definition does. Scratch-copy `#print axioms` checks on every new
   public declaration and both existing theorems show only propext, Classical.choice,
   Quot.sound, and sorryAx where the comparison or an upstream theorem remains open.
   The explicit quotient functor and descended map and the inclusion-bound theorem
   use only the three permitted axioms. No arbitrary data are taken from an open
   existence theorem. Independently reproduced the original caller's type error
   against the changed auxiliary; the adapted caller compiles. Its changed lines
   are necessary to retain the original conclusion at the newly chosen bound.
3. Read the single split-off comparison theorem and checked Stacks 087X directly.
   On each affine, hc identifies S_m with L/(L intersect I^(m+1)M) by choosing a
   sufficiently late l; naturality and monicity identify its transitions. A uniform
   Artin--Rees bound identifies the shifted quotient with L/I^(n+1)L. Its successive
   quotient comparison is canonical and glues by uniqueness after epic projection.
   This is strictly the remaining comparison clause, not a restatement of the
   corrected item. Checked zero and unit ideals, zero modules, empty schemes, and
   the Spec Z example (shift zero fails, a positive shift works). Fresh LeanFinder
   and Loogle searches for stabilized adic subsystems and IsAdicComplete returned
   only completion/transition/lifting tools; local rg searches found no completed
   replacement theorem. This affine sheaf argument cannot be closed in a few minutes.
4. Read from the corrected auxiliary down through the explicit constructions,
   adicness assembly and monicity proof. These use the simpler cokernel route where
   applicable; only comparisons retain the affine Artin--Rees route. Public imports
   are needed by signatures; proof imports are plain imports. The comparison's
   planned-dependency imports remain for its open proof. All seven old direct proof
   dependencies are removed from the auxiliary itself: coherent-formal-modules-affine,
   adic-completion-noetherian, artin-rees, coherent-kernel-cokernel-locnoeth,
   ideal-times-quasi-coherent-affine-sections, quasi-coherent-module-kernel, and
   quasi-coherent-module-cokernel-image (all with prefix lem-weil-pbc-). The first
   five remain used below it; the last two are bypassed. No whole module is claimed
   pruned. Checked dag/units/sk-thm-p1.json: its realized statement and steps are
   unchanged, and this auxiliary's internal reduction bypasses none of them.
5. Compared all six nodes with the code, including proof steps, their dependency
   unions, sources, new-node fields, and Lean statement records. Added the missing
   pqf-lem-coherent-ft-locnoeth dependency to the adicness node, since its proof
   explicitly applies that coherence criterion. Other proof routes agree.

Changes in this second reading: clarified the comparison docstring's use of hc
and its canonical comparison/gluing argument, corrected that one DAG dependency,
and added this review. No Lean signature, definition, proof body, or import changed.
The delivery remains a correction and one-hole decomposition, with net zero holes
closed; it is not an axiom-free proof of the whole auxiliary.

## Forced adaptations

### Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelConstruction
Original against changed dependencies failed:
```
/tmp/forced-adaptation-uev2kvw1/lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleKernelConstruction.lean:97:26: error: Application type mismatch: The argument
  K
has type
  ℕ
of sort `Type` but is expected to have type
  CoherentFormalModule X I
of sort `Type (u + 1)` in the application
  Exists.intro K

(with the modules compiled into /tmp/forced-adaptation-uev2kvw1/.lbuild) [2.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
