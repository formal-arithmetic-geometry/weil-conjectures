## What changed

TheoremFormalFunctions constructs the canonical quotient maps by liftQ, proves their
factorization and transition equations, obtains kernel and stable-image bounds from
MLCohomologyPowersIdeal, and applies a new, fully proved module-theoretic limit lemma.
The latter proves injectivity and surjectivity by representatives and the kernel bound.
The degree-zero assertion transports the comparison through rightDerivedZeroIsoSelf,
including the quotient, completion, system-limit and projection maps. Existing signatures
and public imports are unchanged.

## Proved and sorry left

Closed AlgebraicGeometry.theorem_formal_functions and
AlgebraicGeometry.globalSections_formal_functions (2 original holes).
Added one hole: AlgebraicGeometry.formalFunctions_power_le_ker, node
lem-weil-pbc-formal-functions-power-kernel, in FormalFunctionsPowerKernel.
This is a decomposition, with net one fewer hole in this delivery, rather than an
unconditional proof of formal functions: the main theorem still uses the existing
MLCohomologyPowersIdeal bounds and the new geometric kernel inclusion.
The new adicCompletion_iso_of_stable_ranges has a complete proof and no sorry.
No sorry remains in the assigned module or in AdicCompletionStableRanges.

## No longer needed

Removed the proof import Sheaf.Paper.PQFCohomology. Its theorem
AlgebraicGeometry.sheafCohomologyAndHigherDirectImages is not used: the definitions
and the Mathlib degree-zero natural isomorphism suffice. Thus pqf-def-cohomology is
no longer a direct proof dependency of this node. It remains a statement dependency,
and MLCohomologyPowersIdeal also imports its module; no claim of transitive pruning
is made. The node def-nagata-extended-ideal is also no longer a direct proof dependency:
its kernel argument is now in lem-weil-pbc-formal-functions-power-kernel, which
still depends on it. The remaining original direct dependencies are retained.
No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The source-level identification of H^0 with
Gamma is a natural isomorphism, not definitional equality in the current library.
The delivery explicitly transports all maps using that natural isomorphism.
MLCohomologyPowersIdeal states its ranges before restriction of scalars; the underlying
maps and carriers agree, and the proof makes this conversion explicit.
The cited local coherent.tex is absent on this machine; the source proof was read at
https://stacks.math.columbia.edu/tag/02OC. LeanSearch returned HTTP 500; those searches
are recorded as unavailable. LeanFinder, Loogle and local grep searches were run.
New statements were checked on n=0, c=0, zero and unit ideals and the zero module;
no finiteness or Noetherian hypothesis is needed for the pure module lemma.

## New nodes

lem-weil-pbc-formal-functions-power-kernel states only the ideal-power kernel inclusion
needed to factor the cohomology reductions; it has no properness, coherence or
Noetherian assumptions and contains the only added sorry. Its docstring and node
explain the scalar-endomorphism and quotient-image argument.

lem-weil-pbc-adic-completion-stable-ranges records the fully proved pure module argument
from stabilized ranges and cofinal kernels, with canonical projection equations.
It contains no geometry and does not assume the formal-functions conclusion.
There are no change records or forced adaptations.

## Second reading by H3

1. PASS. Compared the entire assigned module with the repository using diff and
   separately checked both existing theorem signatures byte for byte. Only proofs,
   proof-local options and plain proof imports changed. Existing public imports,
   definitions, visibility, statements and docstrings are unchanged. The two other
   delivered modules and their two nodes are new; no change record is needed.
2. PASS. Compiled all three modules in import order through lcompile.py without
   errors or warnings. A scratch copy with explicit #print axioms showed only
   propext, Classical.choice and Quot.sound for adicCompletion_iso_of_stable_ranges;
   both formal-functions conclusions and formalFunctions_power_le_ker additionally
   depend on sorryAx, as reported. The sole textual sorry is the entire proof of
   the named kernel-inclusion theorem. There are no forbidden declarations or
   hollow definitions. Representative choices occur only inside a theorem proof.
3. PASS. The kernel inclusion is a strictly smaller geometric assertion, not a
   renamed formal-functions conclusion. Scalar multiplication factors through
   J^n F and hence has zero composite with its cokernel; the existing
   moduleCohomology_scalar_endomorphism supplies the cohomology calculation.
   Tested the argument at n=0, I=0, I=top, F=0 and the empty scheme; it requires
   no properness or finiteness. Its complete docstring proof and node agree.
   Fresh LeanFinder and Loogle searches and Mathlib/local rg searches using
   annihilation, scalar and derived-functor terminology found no replacement
   for this inclusion or the stable-ranges lemma. The existing scalar-endomorphism
   theorem is one ingredient, not the inclusion itself. Closing the remaining
   sheaf ideal-power factorization is substantial, so no extra hole was added.
4. PASS. Read the proof from the two original conclusions downward and checked
   Stacks 02OC (https://stacks.math.columbia.edu/tag/02OC). The pure module proof
   constructs the canonical cone, proves injectivity using the shifted kernel
   bound, and obtains compatible quotient representatives using stable ranges.
   Its indexing also handles c=0 and level zero, and it assumes no unjustified
   surjectivity of the reduction maps. The degree-zero proof transports every
   comparison through the natural right-derived-zero isomorphism. New proof-only
   imports are plain imports; the new modules expose imports used by their
   signatures. The sk-thm-p1 realized statement and steps are unchanged and none
   is bypassed. The report now lists every old proof dependency removed directly.
5. PASS. Compared the old and new main node: only proof, proof_deps and proof_origin
   change. Their uses agree with the Lean reduction. Both new nodes contain the
   required source, searches, provenance, chapter, unit and verbatim Lean statement;
   their proof-dependency lists equal the unions of their step uses. The stable-
   ranges node records the actual representative proof, while the kernel node
   records the true remaining geometric argument.

Changed only this report: completed No longer needed with the removed direct
proof dependency def-nagata-extended-ideal and clarified its retention through
FormalFunctionsPowerKernel. No Lean or node repair was necessary. Two original
holes are closed, one lower hole is added, so the delivery has net one fewer hole;
this does not claim that formal functions is free of inherited sorry dependencies.
