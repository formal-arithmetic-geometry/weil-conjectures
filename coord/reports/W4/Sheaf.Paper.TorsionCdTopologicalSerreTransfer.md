## What changed

This is a partial mathematical repair and a proof of the valid portion of the supplied
plan. The unrestricted item theorem is preserved with exactly its original signature
and its original whole-theorem `sorry`. It is flagged `STATEMENT-DISPUTED` for mathematical
re-review because its accepted proof applies an approximation theorem whose generality
has since been refuted. The flag does not claim a counterexample to the vanishing
conclusion. The declaration docstring and its DAG proof now distinguish the valid steps
from the unresolved step instead of presenting the obsolete argument as a proof.

Two separate, proved modules make the valid argument concrete:

- `Sheaf.Paper.CondensedSectionsIndVanishing` proves
  `AlgebraicGeometry.ProEtale.condensedModuleSections_ind_isZero`: fixed-degree ordinary
  derived module-section vanishing passes from any object property to its filtered
  ambient colimit hull on a qcqs scheme. This is step 3, independently of coefficients,
  finite-complex presentations, and Noetherianity. The proof uses the canonical good
  truncation continuity cocone, the actual degree-zero module diagram, preservation
  of its colimit by the single-complex functor, and zero-ness of a colimit of zero objects.
- `Sheaf.Paper.NoetherianTorsionCdTopologicalSerreTransfer` proves
  `AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes_of_locallyNoetherian`.
  This is a separate specialization, with the additional `IsLocallyNoetherian X`
  hypothesis required by the repaired approximation theorem. The proof applies the
  existing finite-complex estimate with c=d+2, uses weak-Serre-hull minimality to obtain
  an ind presentation, removes the identity pullback with `CondensedRing.upperStarId`,
  and applies the first new theorem. It does not replace the unrestricted item.

All three final files compiled individually through `lcompile.py --all` with no errors
or warnings (13.3s, 6.1s and 10.8s). The delivery also reruns compilation and axiom
probes on the final files. An initial preflight found and I corrected a metadata-only
signature-extraction mistake: the Noetherian node record started at the word theorem
in its docstring rather than at its declaration. No Lean statement changed. No definitions, targets, source-library files, existing theorem signatures,
or consumer signatures are changed. No interface change record is required: all existing
public imports and signatures are preserved, and the new modules contain only theorems.

## Proved and sorry left

Original item holes closed: **0 of 1**. Holes added: **0**. Holes split off: **0**.

The original remaining whole-theorem hole is
`AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes`
(node `lem-sfb-torsion-cd-topological-serre-transfer`). Its missing step is specifically
an unrestricted-affine replacement for the refuted filtered-heart kernel-closure
argument; the continuity step does not solve this structural problem.

Both new declarations listed above have complete Lean proofs and no direct `sorry`.
The Noetherian specialization uses the already stated
`finite_constructible_complex_heart_cohomology_vanishes` and
`finite_complex_heart_filtered_approximation`, whose existing holes belong to their
own modules and are not copied or added by this delivery. This is the stage-3 proof
from stated dependencies, not a claim that their remaining axioms are discharged.

Edge cases: the new filtered-colimit result allows every integer q, including negative
q, and every commutative condensed coefficient object. It imposes no finite-stage
chain-map lifts. Its indexing universe is exactly u+1. The Noetherian result retains
all six original coefficient alternatives, including the zero finite ring and all
continuous norm-topological algebraic-closure functions, the strict bound q>d+2,
empty schemes, and d=0. Affineness supplies compactness and quasi-separatedness.

## No longer needed

No original imports, nodes, modules, or declarations are pruned. The original public
imports are unchanged. The direct final-step reference to
`lem-weil-pbc-condensed-qcqs-pushforward-continuity` is replaced by the proved helper
`lem-sfb-condensed-sections-ind-vanishing`, which still uses that continuity theorem.
This is a factoring of the valid step, not removal of the continuity dependency.

The arbitrary-affine approximation assertion is no longer available as a valid proof
step. Its repaired Noetherian version is retained and used only with its actual
hypotheses in the separate Noetherian theorem. Nothing is withdrawn, including any
upstream declaration or quarantined module.

## Where the brief, the DAG or earlier work was wrong

The stage-3 dependency promise does ensure that the declared dependencies exist, but
it does not make their hypotheses fit. The live
`finite_complex_heart_filtered_approximation` takes `[IsLocallyNoetherian X]` and
`[CompactSpace X]`. The item only has `[IsAffine X]`; affineness supplies the latter
but cannot supply the former. Its docstring and original DAG step 2 still claimed
that the dependency applies without Noetherianity.

The mathematical correction is already recorded in
`coord/reports/NN/lem-sfb-finite-complex-heart-filtered-approximation.md` and that node's
independent review. Their counterexample takes an algebraically closed field k of
characteristic ell and X=Spec(C_lc(beta(N),k)), a non-Noetherian w-contractible affine,
with Lambda=Q_ell. Multiplication by the continuous extension of n |-> ell^n on
Lambda_X has an invisible nonzero kernel. Writing B for its image and Q for its
cokernel, Lambda_X and Q belong to the filtered finite-complex-heart class, while
B=ker(Lambda_X -> Q) does not. The review proves the latter using failure of injectivity
of the counit L_0 Gamma(B) -> B, an invariant which is injective on all finite-complex
hearts and their filtered colimits. This avoids the insufficient argument that an
invisible kernel alone refutes the larger heart class. HRS Lemma 8.6(2) supplies the
local bound even in this example, so the bound does not repair kernel closure.

I read HRS Lemma 5.3 and Section 8, including (8.1), Proposition 8.2 and Lemmas 8.5--8.6,
and the existing counterexample analysis. Stable derived Ind-completion does not by
itself give the disputed closure of this degree-zero presentation class. The example
has exact global sections and therefore is NOT a counterexample to this item's
vanishing conclusion. No claim to refute that conclusion, and no unsupported replacement
lemma for it, is made. The original theorem must remain open until an independent
arbitrary-affine argument or a genuine counterexample is found. Adding Noetherianity
to it would weaken the statement and would also fail to serve the non-Noetherian
profinite-base consumer, so that change was not made.

Searches used the mandated msearch wrapper (LeanFinder, LeanSearch, Loogle, and grep)
and project-wide rg. Their exact queries and results are in the sandbox search log
and the two new node records. No existing declaration of either new result was found.
Blueprint searches for filtered-colimit vanishing and torsion-dimension transfer found
no exact imported blueprint statement. The unit's own statement and steps are retained.

## New nodes

`lem-sfb-condensed-sections-ind-vanishing` records the completely proved, coefficient-
independent fixed-degree filtered-colimit step, in its own module. It is strictly a
part of the argument, has no torsion-dimension or weak-Serre hypothesis, and adds no hole.

`lem-sfb-noetherian-torsion-cd-topological-serre-transfer` records the completely proved
Noetherian specialization, in its own module, from the repaired existing dependencies
and the preceding lemma. It adds no hole and does not identify its stronger hypothesis
with the unrestricted original statement. There are no change-record paths because
no existing interface or definition changes.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
