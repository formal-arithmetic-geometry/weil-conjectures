## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso` with a complete degreewise proof.
The existing declaration `AlgebraicGeometry.augmented_cech_sheaf_quasiIso_restrict`
keeps its signature and visibility. Its three original public imports remain because
its statement uses their declarations. Two ordinary proof imports were added:
`Sheaf.AlgebraicGeometry.CechSheafLocalAugmentationKernel` and
`Sheaf.AlgebraicGeometry.CechSheafLocalPositiveExact`.

The degree-zero step obtains a kernel universal property, derives exactness and
monicity, and applies Mathlib's degree-zero short-complex criterion. The successor
step proves that restriction of the single source is exact by mapping its zero
object, and combines it with positive-degree exactness of the target using
`quasiIsoAt_iff_exactAt`. The constructor of `QuasiIso` assembles the cases.
In particular, the source exactness step does not assume that restriction preserves
homology. No definition or existing statement changed; no other module was adapted.

All three delivered modules compile together using `lcompile.py --all`, in import
order, with no compiler diagnostics. The retained obligations are public theorems
in separate modules, each with a complete proof in words and a matching new DAG node.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.augmented_cech_sheaf_quasiIso_restrict`
(node `lem-pc-cech-sheaf-local-quasi-iso`). The item's module now has no `sorry`.
This is a decomposition, not a proof with no remaining assumptions and not positive
net progress in the sorry ledger: one hole closed and two holes added (net -1).

Every remaining hole added by this delivery:

- `AlgebraicGeometry.augmented_cech_sheaf_restrict_kernel`, in
  `Sheaf.AlgebraicGeometry.CechSheafLocalAugmentationKernel`, node
  `lem-pc-cech-local-augmentation-kernel`.
- `AlgebraicGeometry.cech_sheaf_restrict_exact_positive`, in
  `Sheaf.AlgebraicGeometry.CechSheafLocalPositiveExact`, node
  `lem-pc-cech-local-positive-exact`.

The first obligation concerns only the degree-zero kernel and asserts no
positive-degree homology statement. The second concerns only positive exactness
and takes neither an augmentation nor its component equation. Neither obligation
is the original quasi-isomorphism claim under another name. The combining proof
in the original module is complete Lean, with no holes or local axioms.

Edge cases checked mathematically: there is no covering assumption; if I is empty,
the supplied i has no values; an empty U_i gives zero restricted sheaves; zero F
satisfies the same sectionwise equations. Arbitrarily infinite I uses categorical
products, with no assertion that stalks commute with those products. The e_p are
only global-section-ring linear: the proposed insertion homotopies are transported
only after forgetting to abelian sheaves. The degree-zero inverse is locally linear
because it is inverse to the given module-linear augmentation.

## No longer needed

None. No original import, node, or module is pruned: the original node had no
proof dependencies to remove, and all original imports are needed by the unchanged
statement. No covering, stalk-product interchange, boundary-stalk vanishing,
injectivity of F, quasi-coherence, or affine-cover assumption is introduced.

The already proved `TopCat.Presheaf.exactAt_cechComplex_of_le` is useful future
implementation material, but was not imported: it uses a concrete abelian-group
Cech complex and requires an additional comparison with this categorical
presheaf complex. Likewise `cech_zero_cocycle_compatibility` is formulated on
`Over X`, rather than the binary-intersection presheaf used here. Importing these
without a comparison would not close either new obligation.

## Where the brief, the DAG or earlier work was wrong

The existing node labels the whole insertion-homotopy construction, its transport
through e, and reflection of exactness as elementary. These are substantial Lean
steps and have no attached dependencies. The delivery separates degree-zero
descent from positive-degree contraction and records their complete mathematical
arguments. No mathematical error in the original statement or the unit's route
was found; the unit record has no realized entry that this reduction bypasses.

LeanSearch returned Internal Server Error. LeanFinder, Loogle and direct source
searches were run; the searches and the scope of the candidate matches are recorded
in both new nodes. The general Mathlib homotopy-equivalence result does not itself
construct or transport the local Cech operators.

WANTED: the local copy of
`literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-semicon/lem-pc-cech-resolution.md`,
proof paragraph 1, for both new nodes. This machine has only the tracked literature
lists, not the cited document. The original module and DAG reproduce the argument;
the new proofs in words are marked `proof_origin.by = agent`, expanding that
recorded argument, rather than claiming a fresh inspection of the unavailable
blueprint file.

## New nodes

`lem-pc-cech-local-augmentation-kernel` states the kernel universal property of the
restricted degree-zero augmentation, on precisely the original Cech model and
augmentation. Its proof extracts the singleton i coordinate, uses the pair
cocycle equation, and establishes the local-ring-linear inverse on zero cocycles.
It is stated in `lean/Sheaf/AlgebraicGeometry/CechSheafLocalAugmentationKernel.lean`.

`lem-pc-cech-local-positive-exact` states positive-degree exactness of the restricted
Cech-model complex with no augmentation parameter. Its proof inserts i, cancels
cofaces, transports through e on underlying abelian sheaves, and reflects exactness
using `lem-weil-pbc-module-sheaves-colimits-forgetful`.
It is stated in `lean/Sheaf/AlgebraicGeometry/CechSheafLocalPositiveExact.lean`.

The existing node's `proof`, `proof_deps`, and `proof_origin` now describe the
compiling assembly from these two nodes. Its other fields and its statement remain
unchanged. There are no change records because no existing interface changed.

## Second reading by C1

1. **Interface unchanged — pass.** Independently compared the delivered original module
   with the repository by `diff -u` and compared the entire theorem header byte for byte.
   The sole existing signature, visibility, docstring, and all definitions are unchanged;
   only its proof and two ordinary proof imports differ. The two other modules are new.
   There are no statement changes, change records, or forced adaptations.
2. **Proof and axioms — pass as a decomposition.** Independently ran `lcompile.py --all`:
   all three modules compiled without diagnostics. Read the degree-zero kernel-to-exactness
   and monicity argument and the successor zero-source argument. A scratch copy with
   `#print axioms` for all three declarations compiled and reported only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes from the two reported
   new obligations. There is no hole in the combining proof, definition, private theorem,
   or anonymous proof; no forbidden declaration or kernel bypass occurs. The kernel
   universal property determines its lifts uniquely, so obtaining its proof from
   `Nonempty (IsLimit ...)` makes no forbidden arbitrary data choice.
3. **Split statements — pass.** Read both new signatures, docstrings, and node files.
   Projection to the singleton i coordinate and the (i,j) cocycle equation give precisely
   degree-zero kernel descent. Insertion of i and alternating-face cancellation give
   precisely positive-degree exactness, independently of any augmentation. The inverse
   on zero cocycles is locally linear because the given augmentation is locally linear;
   the positive contraction is transported only on underlying abelian sheaves. Neither
   statement restates the original quasi-isomorphism. Checked empty index type (no i),
   empty U_i, zero F, a singleton family (positive differentials alternate between
   identity and zero), repeated indices, and infinite families (sectionwise products,
   without commuting stalks and products). No case needs a covering assumption.
   Repeated independent searches with LeanFinder (kernel of the first Cech differential),
   Loogle (`CategoryTheory.Limits.KernelFork, CategoryTheory.Limits.IsLimit`), Mathlib
   grep, and `rg` in both library roots found general kernel facts and existing Cech
   results, but no exact match. Read `sheaf_cech_augmentation_quasiIsoAt_zero`,
   `SiteCechComplex.exactAt_cofree`, and `exactAt_cechComplex_of_le`: their different
   categories/coefficient constructions still require nontrivial comparison maps.
   Neither remaining obligation can be closed by applying one of these results directly.
4. **Route and pruning — pass.** The assembly uses Mathlib degreewise criteria directly;
   all three original public imports supply types/constructions in the unchanged
   signature, and both new ordinary imports are used. The original node's old
   `proof_deps` is empty, so `No longer needed: None` is complete. Inspected
   `dag/units/sk-thm-picard-semicon.json`: its realized statement and step lists are
   empty; no realized unit node or prescribed unit step is bypassed. The two new
   obligations preserve the original local insertion/descent argument.
5. **DAG agreement — pass.** The existing node changes only `proof` and `proof_deps`;
   its existing agent-origin attribution already describes this source. Its three steps
   match the degree-zero branch, successor branch, and assembly in Lean. Its dependency
   set is exactly the two new theorem nodes. Both new nodes have matching verbatim Lean
   headers, sources, complete proof steps, search records, creation records, blueprint
   provenance, and the original chapter/unit. Read the positive node's forgetful-functor
   dependency: its statement supplies the faithful finite-exact functor required by
   reflection of exactness. The unavailable local blueprint source remains disclosed
   in the report; no fresh source inspection is claimed.

**Changes by the second reader:** appended this independent review only. No Lean or DAG
repair was necessary. The delivery closes one original named hole and adds two strictly
smaller named holes: it is a decomposition with net -1, not a completed axiom-free proof.
