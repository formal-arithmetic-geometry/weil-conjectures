## What changed

Completed and compiled the saved decomposition of
AlgebraicGeometry.Scheme.Modules.coefficientComparison_affine_bijective.
The existing statement and public imports are unchanged. Two proof-only imports,
Sheaf.AlgebraicGeometry.CoefficientSourceAffineTensorPresentation and
Sheaf.AlgebraicGeometry.CoefficientTargetAffineTensorPresentation, state the two
independent tensor presentations. The original node now records these dependencies.

The combining proof transports the generator normalization by naturality and the
support isomorphism, proves equality on pure tensors by linearity, extends it by
TensorProduct.induction_on, and composes two bijections. Repairs to the saved draft
fix the direction of naturality, normalize the source and target module types, and
use the actual linear section map for tensor induction. A declaration-scoped
heartbeat allowance handles the repeated definitional scalar transport. All added
elaboration options are scoped to that declaration; tensor constructors are explicit,
so the original module-level commands stay unchanged.

The formerly missing shared ComparisonMap artifact arrived in the cache refresh
during this session. All three sandbox modules now compile. No shared build,
repository source, or other group's sandbox was changed.

## Proved and sorry left

One original hole closed, by declaration name:
AlgebraicGeometry.Scheme.Modules.coefficientComparison_affine_bijective,
node lem-pc-finite-affine-cech-coefficient-comparison-bijective.
No sorry remains in the assigned module.

Two holes added, both public named theorems with proof exactly := by sorry:

- AlgebraicGeometry.Scheme.Modules.exists_coefficientSource_affine_tensor_presentation,
  node lem-pc-coefficient-source-affine-tensor-presentation.
- AlgebraicGeometry.Scheme.Modules.exists_coefficientTarget_affine_tensor_presentation,
  node lem-pc-coefficient-target-affine-tensor-presentation.

This is a decomposition, not an axiom-free proof of the original statement. Each
presentation has its source and complete proof in words in its docstring and node.
Neither mentions an arbitrary comparison morphism or restates bijectivity of q.
The source presentation works for arbitrary associated-module pullbacks; the target
presentation only describes sections on the inverse-image support. No definition
chooses data from these existence theorems: they are used locally in a proof.

## No longer needed

No existing import removed and no globally pruned module claimed. The original
parent's direct dependencies on FiniteAffineCechIntersectionBaseChange and
ModulePullbackAffineSections are now dependencies of the tensor presentations.
The other two old direct dependencies,
lem-weil-pbc-affine-tilde-gamma-adjunction and
lem-weil-pbc-open-immersion-module-pullback-restriction, are likewise no longer
used directly by the parent proof and remain needed in the presentation proofs.
The four old dependencies are moved, not globally pruned. The combining proof uses no coefficient comparison existence theorem,
but its module supplies the generators and proved support naturality. No unit route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous blocker was genuine: the shared ComparisonMap artifact was absent at
this session's first two compiler attempts. A subsequent automatic refresh supplied
it. No workaround was used.

The saved draft reversed the naturality equation and used section maps without
normalizing the module types, leading to failed rewrites and expensive elaboration.
These proof-only errors have been repaired. The existing affine-section theorem is
for tensorPullback and its adjunction unit; the presentation statements isolate
transport to standard pullback, open restriction, and scalar identifications.

The presentations include empty opens and zero modules, for which both sides are
zero and the generator equations agree. The source allows nonaffine S: the composite
map to Spec Gamma(S) still has affine source B and affine target. The target uses
affineness only for Z, U and B, and needs no flatness. The unit realized fields are
empty; the reduction stays within its existing affine coefficient calculation.

## New nodes

lem-pc-coefficient-source-affine-tensor-presentation describes the R-linear
presentation of sections of g^*(S.toSpecGamma)^*(tilde N) on affine B, taking the
restricted coefficient generator to 1 tensor s. It is the source half of the parent
argument, without any comparison map or target support.

lem-pc-coefficient-target-affine-tensor-presentation describes the R-linear
presentation of sections supported on the inverse image of Z. Its inverse sends
1 tensor s to the pullback generator under coefficientSupportIso. It is the target
half of the argument, without the associated-module source or comparison map.

Both retain sec-picard-framework and sk-thm-picard-coherence and the parent's
blueprint ancestry. LeanFinder, Loogle, and source searches were checked again;
none gives these exact geometric presentations with the standard units.
No existing interface changes, forced adaptations, or change records are proposed.


## Second reading by M2

1. Compared the item module with the repository by diff and checked its theorem
   signature byte for byte. Verdict: unchanged, including every hypothesis and
   conclusion. The only existing node fields changed are proof, proof_deps and
   proof_origin. The two presentation modules and nodes are new. No definitions,
   target statements, visibility or other modules were changed.
2. Compiled all three modules in import order with lcompile.py. Verdict: clean.
   A scratch copy printed axioms of coefficientComparison_affine_bijective,
   exists_coefficientSource_affine_tensor_presentation and
   exists_coefficientTarget_affine_tensor_presentation: only propext,
   Classical.choice, Quot.sound and sorryAx. The scratch copy was removed.
   The only two local sorries are exactly the reported named presentation
   theorems; no prohibited declaration or hollow definition occurs. The two
   equivalence witnesses are eliminated locally inside a proposition proof,
   never used to define data.
3. Read the generator definitions and support naturality, both presentation
   statements and their docstring arguments. Verdict: both are true independent
   parts of the affine tensor calculation, not renamings of the comparison
   theorem. Tested empty B, empty Z, zero coefficients, identity base change,
   arbitrary nonflat base change, and nonaffine S in the source assertion.
   The target intersection is Z times_U B, with section module
   (R tensor_A D) tensor_D N, canonically R tensor_A N. The source composite
   B -> S -> Spec Gamma(S) gives the same tensor module. Their unit formulas
   agree with the actual generators. Stacks Tags 01I9 and 01IA were checked
   directly. Independent LeanFinder, Loogle and source searches found spectral
   formulas in PullbackTilde and the existing tensorPullback affine theorem;
   these still require chart, restriction, scalar and standard-unit transport.
   Neither remaining hole could be closed by a short application of those
   formulas without carrying out that transport.
4. Read the combining proof from the original goal downward. Verdict: its
   naturality equation has the correct direction; support injectivity gives
   equality on 1 tensor s; R-linearity and tensor induction prove conjugacy
   to the two equivalences. Imports used by the statement stay public, and
   the new presentation imports in the parent are proof-only. All four old
   non-comparison proof dependencies are explicitly recorded as moved to the
   presentations, not globally pruned. Read sk-thm-picard-coherence.json:
   realized.statement and its sole realized step are empty; the reduction
   keeps the existing affine coefficient calculation and bypasses no unit.
5. Checked all three nodes against the Lean files, including verbatim new
   signatures, blueprint ancestry, sources, creation records and dependency
   unions. Verdict: the parent records exactly the two presentations and
   proved support naturality; each new node records the affine calculation
   and unit transport used in its natural-language proof.

Second reading changed: added plain proof-dependency imports of
ModulePullbackAffineSections in both new presentation modules and
FiniteAffineCechIntersectionBaseChange in the target presentation, so the
unfinished proof plans retain their library dependencies. No proof term was
changed. Expanded No longer needed to name all four moved parent dependencies
and added the independent search results to both new nodes. One old hole is
closed and two new holes are added: this remains a decomposition, with net
minus one local hole closed, not an axiom-free proof or global pruning claim.
