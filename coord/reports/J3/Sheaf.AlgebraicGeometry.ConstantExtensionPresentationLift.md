## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.ConstantExtensionPresentationLift` by
an unchanged-signature proof from one strictly smaller sheaf-lifting statement. The proof
constructs the empty cover explicitly, extracts finite generation of a constant model from
a separably closed geometric stalk on a nonempty scheme, constructs a finite free
surjection and its kernel short complex, proves short exactness and finite generation of
the kernel, and verifies the final identity by naturality. All additional imports are
proof-only. No definition or existing statement changed.

Added `Sheaf.AlgebraicGeometry.FiniteFreeConstantLocalLift`, containing the remaining
simultaneous local lifting theorem, and its DAG node. This theorem concerns any epi and any
map from a specified finite free constant sheaf. It needs neither a finite ring, a short
exact complex, a constant quotient, nor finite quotient stalks. It supplies neither a
module presentation nor finite generation of a kernel, so it is strictly a part of the
original argument. Source read: https://stacks.math.columbia.edu/tag/093U, extension
paragraph, label `lemma-kernel-finite-locally-constant` (also verified in the source TeX
fetched read-only from the Stacks repository). Updated the original DAG proof to match the compiled argument.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.exists_constantExtension_presentation_lift`, node
`lem-pc-constant-extension-presentation-lift`, from the named remaining theorem. The item's
module contains no sorry. Its empty-base, stalk-model, finite free surjection, kernel
finiteness, short exactness, and comparison-naturality arguments are proved directly.

Added one hole: `AlgebraicGeometry.Scheme.exists_finiteFreeConstant_local_lift`, node
`lem-pc-finite-free-constant-local-lift`, in its own module. This is a decomposition, not a
sorry-free proof of the import closure: one upper hole closed, one lower hole added, net
zero. The new theorem has source and a complete proof in words. Edge cases checked:
empty base permits the empty cover; rank zero permits the identity cover and zero map;
the zero ring causes no exception; noncommutative rings use only left-module linearity.
No arbitrary data is defined by choosing a witness of an unproved existence theorem.

Compilation of the two-module sandbox succeeds without warnings through lcompile.py.
The deliver3.py --no-push dry run printed OK: compilation and preflight pass, with only the
second reading reserved for the independent reader. Nothing was pushed.

## No longer needed

Removed proof dependency `lem-constructible-shortexact-local-lift` from the original node.
Its module `Sheaf.AlgebraicGeometry.EtaleShortExactLocalLift` is not needed by this proof:
it is stated for SheafOfModules over commutative coefficients rather than the required
fixed-coefficient ModuleCat sheaves. It was not imported in the original Lean file, so no
literal import was removed. Its own dependencies are not introduced by this delivery.
The new generic helper uses the ModuleCat case of Mathlib's local-surjectivity API in its
proof plan instead. No unit statement or realized unit step is bypassed. No claim is made
that the removed node is unreachable from every other target branch.

The related `WeilConjectures.ConstructibleSheaf.KernelCokernel` module is not imported:
import_direction.py reports that it already reaches this item and would create a cycle.
The required stalk computation is imported directly from
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`.

## Where the brief, the DAG or earlier work was wrong

The recorded local-lifting dependency's Lean signature has different coefficients, as
the original node's own step 3 already observes. Its declaration cannot be applied to the
item as written. The new helper isolates this gap without adapting another group's module.
The convenient finite-model lemma in KernelCokernel cannot be imported due to a cycle;
its stalk argument works directly from the lower-level constant-stalk API. No mathematical
error in the item's statement was found.

Searches run: LeanFinder returned ring-sheaf generators/presentation APIs; Loogle returned
an algebra finite-free-surjection theorem requiring commutative algebra coefficients;
LeanSearch returned an Internal Server Error and is recorded as unavailable; ripgrep on
Mathlib and both library roots found the coefficient and import-cycle mismatches above.
The existing finite constant model theorem also has commutative coefficients, so it does
not apply to the arbitrary Ring statement here.

## New nodes

`lem-pc-finite-free-constant-local-lift` records precisely the finite free local lifting
step of Stacks 093U. Its module is
`lean/Sheaf/AlgebraicGeometry/FiniteFreeConstantLocalLift.lean`, and its public declaration
is `AlgebraicGeometry.Scheme.exists_finiteFreeConstant_local_lift`. The proof plan uses
basis sections, local surjectivity, a finite intersection of covering sieves, a cover
indexed by the points of X, the constant-sheaf adjunction, and the etale restriction
comparison. No change record is needed because no existing interface changed.

## Second reading by J3

1. **Interfaces: PASS.** Read both delivered modules and diffed the existing module
   against the repository. The sole existing declaration's signature, docstring,
   visibility, and namespace are byte-for-byte unchanged. Only its proof and four
   proof-only imports changed. No definitions or target statements changed; no change
   record or forced adaptation is needed.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled both modules
   in import order with `lcompile.py --all`, without errors or warnings. Compiled a
   scratch copy with `#print axioms` for both declarations: each reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The upper module has no
   sorry; the only delivered sorry is the named local-lifting theorem in its own module.
   No forbidden declarations or hollow definitions occur. The kernel presentation is
   explicitly constructed; existential choices occur inside theorem proofs and do not
   define data from an unproved mere-existence theorem.
3. **Split statement: PASS.** Read the local-lifting signature, docstring, and new node,
   and independently read Stacks Tag 093U's extension paragraph. Simultaneous lifting
   of finitely many sections follows by intersecting their image covering sieves and
   extending the lifted basis linearly. This works for arbitrary left modules, without
   commutativity or a finite coefficient ring. The point-indexed cover has the required
   universe. Empty X allows the empty cover; rank zero allows the zero lift on the
   identity cover; over the zero ring all modules are zero. This theorem provides no
   quotient model, finite presentation, or finite kernel, so it is a strict part of the
   argument rather than a renamed copy of the item. Independent LeanFinder search
   used “morphism from constant free sheaf lifts after restricting to a covering
   family”; Loogle used `"IsLocallySurjective"`. Neither returned the new assertion.
   Ripgrep and direct reading checked FreeLifting, EtaleShortExactLocalLift,
   ConstantExtensionCover, Mathlib EpiMono, and ConstantSheafSections. The nearby
   free-Yoneda lift requires commutative coefficients and a quasi-compact site object;
   the ring-sheaf lifting theorem has different coefficients. Mathlib supplies the
   constituent APIs, not this packaged statement. Closing the helper requires the
   substantial restriction/adjunction construction, beyond a few-minute repair.
4. **Route and pruning: PASS.** Checked the upper proof from its conclusion down:
   empty cover, geometric-stalk model, finite free surjection and kernel, local lift,
   and comparison naturality. The added proof imports respectively supply the helper,
   constant-stalk comparison, module exactness criterion, and finite-module instance.
   Existing public imports are needed for the statement. The report's No longer needed
   section names the only removed old proof dependency and its module. Inspected
   `dag/units/sk-thm-properbasechange.json`: neither the removed dependency nor the new
   reduction bypasses any realized unit statement or step. No global module-pruning
   claim is inferred from removing this dependency on one branch.
5. **DAG: PASS.** Diffed the existing node: only proof, proof_deps, and proof_origin
   changed. Its steps describe the compiled proof, and proof_deps is their uses union.
   The new node records the exact Lean signature, statement dependencies, source,
   complete proof steps, search evidence, provenance, blueprint parent, chapter, unit,
   status, and Lean record. Both Lean declarations carry the matching blueprint id.

Second reading changed only this report by adding the independent checks and verdicts.
No Lean or node repair was necessary. Counts remain one original hole closed and one
strictly smaller hole added: a decomposition with net zero, not a sorry-free closure.
