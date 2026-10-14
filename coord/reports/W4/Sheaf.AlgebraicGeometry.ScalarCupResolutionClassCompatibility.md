## What changed

Marked `scalarCup_resolution_class_compatibility` as STATEMENT-DISPUTED, preserving
its complete signature and its original `sorry`. The inherited reduction depended
on a scalar/derived comparison with the same missing sign. That unlanded candidate
module and node are excluded from this delivery; their contents and the compiled
reduction are archived under scratchpad/inherited-attempt.

Added four proved private diagnostic lemmas to the item module:

- `scalarCup_yoneda_order` reduces the defined scalar cup to the left Ext class
  followed by the right class transported through tensorLeft, with the right
  unitor inserted. It uses the existing exact-functor/unitor transport lemma.
- `oddShiftTensor_component` computes the two shift comparisons on the (1,1)
  tensor summand: moving the left shift out first gives the negative tensor.
- `oddTensorSummand_ne_neg` proves that the (1,1) summand for two copies of Q[-1]
  is not its negative. The existing normalized single-tensor isomorphism reduces
  this assertion to -1 != 1 in Q.
- `oddShiftTensor_not_unsigned` combines those computations into an inequality
  between the left-first shifted tensor map and the unsigned tensor map.

The new imports are proof-only. They supply the exact-functor unitor lemma, the
normalized single-tensor isomorphism, the cochain monoidal instance and Mathlib's
shift summand formulas. No definition, existing signature or other module changes.
The local proof context is documented in
coord/changes/scalar-cup-sign-audit-context.md, as the static interface checker
requests for the section-local open and attribute commands.

Validation: the final item module compiled without warnings in 11.1 seconds.
A final-source copy with #print axioms compiled in 11.0 seconds and verified that
all four private lemmas use only propext, Classical.choice and Quot.sound. The
assigned signature was also checked textually identical to the repository's.
The dry run handles the second-reading section through its documented first-worker
exception; that section has not been written by this worker.

## Proved and sorry left

Original holes closed: 0 of 1.

The original declaration `scalarCup_resolution_class_compatibility`, node
`new-sc-scalar-cup-resolution-class-compatibility`, retains its `sorry` and is
marked disputed. The four private diagnostics listed above are proved. They
establish an obstruction to the proposed comparison, rather than claiming a
formal Lean refutation of the scheme theorem.

New holes: 0. In particular, `scalarCup_derived_global_comparison` is not delivered.
No `sorry` has been moved to another declaration, and no corrected or weakened
version of the assigned statement has been substituted.

## No longer needed

The inherited, unlanded `Sheaf.AlgebraicGeometry.ScalarCupDerivedGlobalComparison`
and node `new-sc-scalar-cup-derived-global-comparison` are discarded as delivery
candidates. Their unsigned conclusion has the same obstruction. This does not
delete any repository module or DAG node.

The saved reduction's proof-only imports of `ModuleCupOnePairingHomology`,
`ModuleCupResolutionRealization`, `ModuleCupResolutionAugmentation` and
`ScalarCupDerivedGlobalComparison` are removed. Its earlier tensor-connectivity
argument is also unnecessary: augmentation compatibility already identifies the
realized derived map, but neither argument fixes the scalar shift sign.

The still earlier, unlanded Ext restatement
`ScalarExtCupResolutionClassCompatibility` is not reintroduced. The unused
ModuleCat.Closed, ModuleCat.AB and ModuleCat.Limits imports of the diagnostic probe
are omitted from the delivered module; the existing imports supply its instances.

No existing globally reachable module is withdrawn, and no unit statement or
unit proof step is bypassed. Global module pruning claimed: none.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the scalar cup uses a left-then-right Yoneda composition,
whereas hc fixes the unsigned (p,q) tensor cycle. In the stated conventions their
values differ by (-1)^(p*q), which can be nontrivial. The proposed scalar/derived
bridge and the route note's step 4 silently identify these two conventions.
Checking only the section formula for scalarTensorCoefficient does not check the
shift comparison; that coefficient map has degree zero and supplies no extra sign.

Here is the missing-sign calculation. Write a and b for closed sections in degrees
p and q of the two resolutions. To represent the degree-q right Ext class on the
whole left resolution, its component in degree r is

    x |-> (-1)^(r*q) pair(r,q)(x,b).

Indeed, the total tensor differential is d(x tensor b) = dx tensor b, while the
q-shifted target differential is (-1)^q d. The indicated factor is exactly what
makes these components a cochain map. Its degree-zero component is the desired
coefficient representative of the right Ext class. The first scalar Ext class is
then applied, by the proved `scalarCup_yoneda_order`. At its degree-p cycle the
component is (-1)^(p*q) pair(p,q)(a,b). Thus the scalar cup yields the signed class;
the assigned conclusion asserts the unsigned class. The identifications defining
moduleExtEquiv normalize actual resolution cocycles to extMk, and the scalar
restriction, scalar unit and tensor coefficient maps introduce no further sign.
Mathlib's shiftFunctorAdd' component formula is an equality transport, so merging
the two shifts does not remove this factor.

The formal diagnostics specialize precisely this calculation to p=q=1 and to
two single rational complexes. They exhibit a nonzero tensor summand and prove
that the left-first shift map is its negative, with no sorry dependency. The
scripted comparison of scalarCup's Yoneda order is valid in every p and q.

A mathematical counterexample, not yet instantiated as a Lean scheme, is
X = P^1_Q x P^1_Q, F = O(-2,0), G = O(0,-2), p=q=1. The two H^1 groups are Q, and
the ordinary resolution cup of their pulled-back generators is a nonzero generator
of H^2(X,O(-2,-2)) = Q. Standard affine-cover resolutions, or their compatible
acyclic refinements, give the required CupResolutionPairing and cycles. The scalar
Yoneda cup above gives the negative of that generator. Over Q it differs from the
class required by the theorem. The cohomology computations follow Stacks,
Cohomology of projective space, Lemma 30.8.1, and the external product is the
Kunneth isomorphism of Lemma 33.29.1:
https://stacks.math.columbia.edu/tag/01XS
https://stacks.math.columbia.edu/tag/0BEC

The source cup uses the unsigned normalization on shifted source units, as the
footnote to Lemma 20.31.1 explicitly explains:
https://stacks.math.columbia.edu/tag/0FP2
The relevant Lean component formulas are
CochainComplex.ι_mapBifunctorShift₁Iso_hom_f and
CochainComplex.ι_mapBifunctorShift₂Iso_hom_f; the latter multiplies the (r,s)
summand by (r*q).negOnePow. The original node's prose equates the signed Yoneda
construction with the unsigned section pairing without accounting for this step.

The statement and target-used scalarCohomologyCup definition have been preserved
as instructed. Resolving the sign convention requires statement/definition review;
another unsigned comparison split cannot resolve it. The prior recovery deadline
and minute-108 split guard no longer block this delivery, which adds no holes.

## Second reading by W4

1. **Interface and accidental changes.** I compared the delivered module with the repository
version. The target declaration `scalarCup_resolution_class_compatibility` has the same
signature byte for byte. The added imports are proof-only, and the added local opens,
attributes, and options are confined to the private `SignAudit` section. Verdict: pass.

2. **Compilation and proof status.** The delivered module compiles with
`python3 /home/ubuntu/weil-launcher/lcompile.py` without errors or warnings. The target
still has its original named `sorry`; no new `sorry`, axiom, unsafe declaration, hollow
definition, or public declaration was added. The four private diagnostic lemmas compile
and their source-copy axiom audit uses only the permitted axioms. Verdict: pass for the
delivered diagnostics; the target remains open as reported.

3. **Statements and nodes.** No public statement was split off. The target statement and
its existing DAG node are unchanged. The `STATEMENT-DISPUTED` marker records the odd-degree
shift-sign obstruction rather than replacing the target by a weaker claim. The diagnostics
are private and do not require DAG nodes. Verdict: pass, subject to review of the disputed
statement by the statement stage.

4. **Shortest route and pruning.** The proof attempt was pruned to the existing scalar
Yoneda order and concrete cochain shift formulas. The abandoned derived-comparison module,
its unsigned split node, and unused proof-only imports are not delivered. No unit statement
or realized unit step is bypassed. Verdict: pass.

5. **Mathematical correctness and route.** The private calculations show that moving the
left shift before the right shift contributes `(-1)^(p*q)` and that the `(1,1)` summand for
two rational single complexes is nonzero and unequal to its negative. This directly exposes
the missing sign in the unchanged unsigned target comparison. The proposed geometric example
in `report.md` explains why the obstruction is substantive. Verdict: pass for the audit;
the original target cannot be certified until its sign convention is repaired.

I changed only this report section after the first worker's delivery. No Lean file, DAG node,
public declaration, or change record was otherwise modified.
