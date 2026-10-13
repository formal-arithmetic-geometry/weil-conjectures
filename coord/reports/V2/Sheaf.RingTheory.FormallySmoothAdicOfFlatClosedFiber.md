## What changed

The original theorem's signature and visibility are unchanged. Its proof now constructs the flat
map of maximal-ideal completions, proves locality from the commuting square and the maximal-ideal
formulas, transfers the closed-fibre hypothesis, applies the complete case, and descends the lift.
Two private helpers in the item prove the kernel formula for completion evaluation and the entire
reverse completion reduction (Tag 07ED). The latter constructs the test-ring action via the
finite quotient A/m_A^(2k), proves compatibility with the extended target map by approximation,
and restricts the completed lift.

Added Sheaf.RingTheory.FormallySmoothAdicClosedFiberCompletion. Its public theorem is proved
from existing LocalCompletionQuotient, FormallySmoothAdicCompletion and FormallySmoothAdicRingEquiv.
The proof explicitly verifies both scalar compatibility through the residue-field isomorphism
and equality of the transported ideals. It uses a proved private algebra-equivalence transport
helper. Added Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiberComplete for the remaining
complete-ring argument, with the original steps 2–10 and their cited inputs in its node/docstring.
No existing definition or public import changed. No forced adaptations.

Search: LeanFinder returned eight discrete formal-smoothness/flatness results; Loogle returned
completion equivalences. LeanSearch was unavailable (Internal Server Error), so no absence
verdict is inferred from it. Grep found no direct result in Mathlib or WeilConjectures. Blueprint
searches for 07ED, 07NQ and the complete/closed-fibre phrases found no duplicate. The nearby
FsAdicClosedFiberModel cannot be imported: it reaches this very criterion through
FormallySmoothAdicLift. The Stacks source is not locally populated in this clone, so Tags 07NQ
and 07ED were read from the Stacks website. Only the assigned sandbox was written directly.

## Proved and sorry left

Closed the item's sole original hole:
- RingHom.formallySmoothAdic_of_flat_closedFiber
  (lem-weil-pbc-flat-formally-smooth-closed-fibre-adic).

Also proved the new RingHom.formallySmoothAdic_closedFiber_completion
(lem-weil-pbc-fs-closed-fibre-completion-transfer), its private transport helper,
and the item's private completion_eval_ker and formallySmoothAdic_of_completion.

One hole is added and remains:
- RingHom.formallySmoothAdic_of_flat_closedFiber_complete
  (lem-weil-pbc-flat-fs-closed-fibre-complete-case), whose entire proof is `by sorry`.

This is a decomposition, not a sorry-free proof of the criterion. One original hole closed,
one narrower complete-case hole added; net zero direct holes. The remaining theorem genuinely
assumes both rings are complete; the reduction constructs their completions, separately proves
the closed-fibre transfer, and proves descent by solving the original lifting problems. It is
not an application of an identical renamed statement. Existing dependencies may still contain
sorry; they remain the next proof items. All three delivered modules compile without warnings.

Edge cases checked in the proof design: k may be any positive integer (the quotient argument
uses k+k, without selecting a smallest exponent); field sources and zero maximal ideals require
no branch; I=0 gives the same completion-quotient construction; no flatness hypothesis is needed
for the fibre comparison. The complete-case proof retains empty parameter lists and uses Cohen
rings in positive residue characteristic, including equal-characteristic targets presented as
quotients of them. No arbitrary witness was installed as data of a new definition.

## No longer needed

Removed these direct proof imports from the original module:
- Sheaf.RingTheory.AdicFieldDifferentialsInjective
- Sheaf.RingTheory.CompleteLocalMapCohenPresentation
- Sheaf.RingTheory.FlatOverRegular
- Sheaf.RingTheory.FormallySmoothAdicBaseChange
- Sheaf.RingTheory.FormallySmoothAdicCompletion
- Sheaf.RingTheory.FormallySmoothAdicGeometricallyRegular
- Sheaf.RingTheory.LocalCompletionQuotient
- Sheaf.RingTheory.PowerSeriesFieldCohenFsAdic
- Sheaf.RingTheory.PowerSeriesParameterQuotient
- Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
- Sheaf.RingTheory.RegularLocalQuotientKernelParameters

These dependencies are retained in the pending complete-case node or in the proved
closed-fibre-comparison node; they are relocated, not mathematically pruned. None of the original
mathematical proof-dependency nodes is claimed unnecessary in the total new route. No unit
statement or realized unit step is bypassed. Net closure pruning: none.

The following old direct `proof_deps` are relocated to the two new nodes, rather than
claimed mathematically unnecessary:

- lem-weil-pbc-local-completion-quotient
- lem-weil-pbc-fs-adic-completion
- lem-weil-pbc-complete-local-map-cohen-presentation
- lem-weil-pbc-regular-local-generators-regular-sequence
- lem-weil-pbc-quotient-local-structure
- lem-weil-pbc-fs-adic-field-geometrically-regular
- lem-weil-pbc-regular-local-quotient-kernel-parameters
- lem-weil-pbc-nakayama-local-generators
- lem-weil-pbc-regular-local-cotangent-dimension
- lem-weil-pbc-power-series-parameter-quotient
- lem-weil-pbc-flat-over-regular
- lem-weil-pbc-tensor-quotient-base-change
- lem-weil-pbc-flat-module-base-change
- lem-weil-pbc-flat-quotient-tensor-injective
- lem-weil-pbc-surjective-image-noetherian
- lem-weil-pbc-fs-adic-base-change
- lem-weil-pbc-power-series-field-cohen-fs-adic
- def-weil-pbc-multivariate-power-series
- def-weil-pbc-kahler-differentials
- lem-weil-pbc-jacobi-zariski-differential-maps
- lem-weil-pbc-fs-adic-field-differentials-injective

## Where the brief, the DAG or earlier work was wrong

No statement change. The original lead note warns that characteristic-p field power series are
not formally smooth over Z: F_p does not lift to Z/p². The complete-case proof uses the actual
07NN Cohen-ring presentation in positive residue characteristic, so its unrestricted lifting
step uses the Cohen-ring Z-smoothness clause rather than that false field variant. The node and
its original signature remain unchanged. The new fibre comparison removes the informal
"transport" gap by proving the two scalar actions and ideal maps agree.

## New nodes

lem-weil-pbc-fs-closed-fibre-completion-transfer:
RingHom.formallySmoothAdic_closedFiber_completion, in
lean/Sheaf/RingTheory/FormallySmoothAdicClosedFiberCompletion.lean. This is the closed-fibre
part of the completion reduction. It is proved, including the change of residue scalars.

lem-weil-pbc-flat-fs-closed-fibre-complete-case:
RingHom.formallySmoothAdic_of_flat_closedFiber_complete, in
lean/Sheaf/RingTheory/FormallySmoothAdicOfFlatClosedFiberComplete.lean. This isolates the genuine
complete-ring special case (the Cohen presentation, fibre equations, base-change isomorphism,
and derivation correction). Its one remaining hole is public, named, and has the source and a
complete proof in words in both the docstring and node. No change record is needed because all
existing public interfaces are identical.

## Second reading by V2

1. Compared the original module with the repository by diff and extracted the full existing
   theorem signature: it is byte-for-byte identical. Public imports, visibility, definitions,
   hypotheses and conclusion are unchanged. Only proof imports, private helpers and the proof
   change. The original node changes only proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled all three modules in import order using lcompile.py. Separate scratch copies with
   #print axioms checked every delivered theorem, including the three private helpers.
   completion_eval_ker, formallySmoothAdic_of_completion, formallySmoothAdic_of_algEquiv and
   formallySmoothAdic_closedFiber_completion use only propext, Classical.choice and Quot.sound.
   The original criterion and the complete-case theorem additionally use sorryAx. Exactly one
   sorry remains, in the named complete-case theorem; no definition or data construction has a
   hole, and no forbidden declaration mechanism is present. Verdict: valid decomposition.
3. Read Stacks Tags 07NQ, 07ED and 07NN and the existing Cohen presentation, parameter quotient,
   field/Cohen smoothness, quotient completion and scalar-transport declarations. The complete
   case adds precisely maximal-ideal completeness for both rings; it retains localness,
   Noetherianity, flatness and the canonical fibre action. Its statement is true and strictly
   narrower, while the 114-line completed-lift descent and the fibre comparison do genuine
   work. The fibre comparison needs no flatness: Ihat=I Bhat follows from hcomm, and the residue
   scalar and ideal comparisons are explicitly proved. Checked k=1, field sources, I=0,
   empty parameter lists, characteristic zero, and positive residue characteristic. The latter
   uses Cohen rings over Z, including presentations of equal-characteristic targets, and never
   the false Z-smoothness of F_p. Repeated LeanFinder with a differently worded complete-local
   query (eight discrete/flatness hits), Loogle AdicCompletion/RingEquiv (no hits), and rg on the
   current Sheaf, upstream and Mathlib sources. No direct adic criterion was found; the nearby
   closed-fibre model is circular. The remaining Cohen/derivation argument is substantial and
   cannot be closed by a short application of an existing theorem. Verdict: pass.
4. Checked the target proof from the top: FlatCompletion constructs the commuting flat map;
   Mathlib maximal-ideal identities prove locality; the separately proved fibre transfer
   supplies the complete-case hypothesis; finite quotients at k+k and k construct the genuine
   completed lifting problem and its restriction. The kernel computation uses Mathlib directly.
   Public imports serve signatures and all proof imports serve the written reductions. The
   old dependencies are retained in the pending complete argument or the proved comparison;
   the report now enumerates every removed direct dependency. Read sk-thm-p1.realized: these
   auxiliary nodes are below its realized steps; no unit step or statement is bypassed.
   Verdict: pass; no mathematical pruning is claimed.
5. Checked all three nodes against their Lean statements and proof routes, including the
   canonical quotient actions and the two completeness instances. proof_deps equals the union
   of step uses for each node. New nodes have sources, creation records, blueprint ancestry,
   search records and verbatim normalized Lean signatures. Verdict: pass.

Changes in this second reading: expanded the complete-case docstring and matching node to
explain descending induction along the square-zero filtration, continuity of each successive
lift (the exponent doubles), and compatibility of the kernel action with the original map.
Marked the unavailable LeanSearch result explicitly unavailable in both new nodes. Added the
full relocated-dependency list above. No proof, signature or definition required repair.
