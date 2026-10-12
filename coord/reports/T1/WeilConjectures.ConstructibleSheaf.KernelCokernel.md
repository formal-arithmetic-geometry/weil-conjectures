## What changed

Proved `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_shortExact` from one new
constant-outer-term covering lemma. No existing signature or definition changes.

The finite-stalk argument is fully proved: apply the geometric stalk functor to the short
exact sequence, use `ModuleCat.isFinitelyGenerated_iff`, and invoke Mathlib's
`Module.Finite.of_exact` with the epi/surjectivity equivalence. This part does not require
finite coefficients or local constancy.

The local-constancy argument takes the existing common trivialising cover, pulls back the
short complex and finite stalk hypotheses, applies the new covering lemma separately on
each member, transports through `Etale.upperStarComp`, and binds the two levels of covers.

Added proof-only imports of `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` and
`Sheaf.AlgebraicGeometry.ConstantExtensionCover`. Updated the parent node's proof route.
Corrected its declaration docstring to use the finite presentation route already required
by the DAG, instead of the invalid splitting-torsor argument.

## Proved and sorry left

The original module's single sorry, in
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_shortExact`, is closed.
Its statement is unchanged. The existing constructible extension proof now calls this
completed reduction.

One sorry remains in the new module:
`AlgebraicGeometry.Scheme.exists_constantExtension_cover`, node
`lem-constructible-constant-extension-cover`. This is the constant-outer-term local argument,
with neither the original arbitrary locally constant hypotheses nor the finite-stalk
conclusion. The original module proves the finite-stalk conclusion and the descent/gluing.

Local compilation of both modules passes with no errors or non-sorry warnings. The delivery
dry run also passes local and server compilation and preflight, except for the expected
second-reading section to be supplied by the next reader.

## No longer needed

Removed the experimental proof-only import `Mathlib.RingTheory.Finiteness.Finsupp`: its
finiteness lemma is already available through the retained imports. No original imports
removed. No existing modules are globally pruned: all three original
public imports are used by the earlier proofs retained in the module. The local-lift and
constant-exact nodes cease to be direct proof dependencies of the parent extension node;
they remain needed by the new constant-extension covering node. The already rejected
`lemma-constructible-torsor-trivialises` remains unused, with no new import or proof work.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery (reviewer X-be294, head be29498f0): the independent
review passed, but landing timed out while another delivery held the merge lock.
The requested repair is to rebuild the delivery on current `origin/sheaf-dag` and
repeat local and server compilation and preflight with `deliver3.py --no-push`.
No mathematical or Lean defect was reported; the reviewed proof and node route
are retained. This repair does not acquire or remove the maintainer merge lock.

The extension theorem's old docstring still claimed local splitting via a splitting torsor,
although the DAG had already corrected that argument. The nonsplit constant extension
0 → Z/2 → Z/4 → Z/2 → 0 over Z/4 shows why that claim fails. The finite-presentation
cokernel argument works for this example and does not split the extension.

The existing local-lift module is stated for `SheafOfModules` over a commutative ring in
universe u, while the target uses `Sheaf ... (ModuleCat Λ)` for an arbitrary ring in
universe u+1. It cannot be applied directly to the target. That adaptation remains within
the new constant-outer-term covering item and is explicitly named in its node proof.
The constant-exact module also asks for finite underlying values; these follow after
trivialising over a nonempty scheme because Λ is finite and the stalks are finitely generated.

Edge cases checked in the mathematical proof: an empty scheme admits an empty cover; a
zero ring has only zero modules; vanishing outer terms cause no failure of the presentation
argument; and the nonsplit Z/4 extension needs only local generator lifts, never a splitting.

## New nodes

`lem-constructible-constant-extension-cover`, in
`lean/Sheaf/AlgebraicGeometry/ConstantExtensionCover.lean`, states the constant-outer-term
local part of Stacks 03RX (3)/093U. The docstring records the full finite presentation,
local generator lifting, cokernel identification and local constant-morphism argument.
After the second reading it imports only Defs and ShortExact, which supply its public
signature; it has no import cycle through KernelCokernel.
Mathlib search found no exact existing declaration; LeanSearch was unavailable and is
recorded as unavailable. No change records are needed because existing interfaces are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered `KernelCokernel.lean` against the repository version. All existing declaration signatures are byte-for-byte unchanged; only proof imports, the corrected docstring, and the proof body were added. The new `ConstantExtensionCover.lean` and node are declared explicitly.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named theorem `exists_constantExtension_cover`, matching node `lem-constructible-constant-extension-cover`; there are no hollow definitions, axioms, unsafe declarations, or other forbidden constructs.
3. Read the split statement and docstring proof. The constant-outer-term cover claim is true and has exactly the hypotheses used by the reduction; it is not duplicated by an existing declaration. The finite-stalk argument uses exact stalks and `Module.Finite.of_exact` without weakening the parent statement.
4. The proof follows the unit route: common outer trivialising cover, constant-extension cover on each member, upper-star transport, and cover binding. The old torsor route is removed; the report records the nonsplit `Z/4` counterexample. The retained proof-only imports are used, and the removed finsupp import is documented.
5. Checked the parent and new DAG nodes: proof steps and dependencies match the Lean route, the new node has complete metadata, and the unit `realized` route remains represented by the parent node.

Changes made in this second reading: appended this review section only; no proof or statement repairs were necessary.


## Second reading by T1

1. **Interfaces: pass.** Read both delivered modules and diffed KernelCokernel against the
repository. Every existing declaration signature and every definition is byte-for-byte
unchanged. The diff consists of two plain proof imports, the extension docstring correction,
and the body of IsFiniteLocallyConstantSheaf.of_shortExact. The new module and node are
explicitly reported; no change record is required for an existing interface.

2. **Proof and axioms: pass as a partial reduction.** Compiled both modules in import order
with lcompile.py --all, again after narrowing imports. No errors or non-sorry warnings.
The only sorry in the delivered files is the entire proof of the public named theorem
exists_constantExtension_cover. There are no forbidden constructs or hollow definitions.
Read the finite-stalk proof: exact stalks, the two outer Module.Finite instances, and
Module.Finite.of_exact prove finite generation of the middle stalk. Read the local proof:
common cover, exact pullback, the constant-extension lemma, upperStarComp transport, and
cover binding supply the locally constant datum. A scratch copy with #print axioms checks
of_shortExact, the split lemma, kernel and cokernel: the first two have only propext,
Classical.choice, Quot.sound and sorryAx; kernel and cokernel have only the three permitted
axioms. The original sorry is replaced by a real reduction, not an axiom-free completion
of the extension theorem.

3. **Split statement: pass.** Its Ring/Finite coefficients, constant outer terms and finite
geometric stalk hypotheses match the node exactly; its conclusion is only a constant cover
of the middle term. It omits the finite-stalk conclusion proved in the parent and specializes
the outer local-constancy problem, so it is strictly part of the argument. Read its full
presentation/cokernel docstring against Stacks 093U and 03RX:
https://stacks.math.columbia.edu/tag/093U and https://stacks.math.columbia.edu/tag/03RX.
The finite-ring hypothesis makes the presentation kernel finite also for noncommutative
left modules. Empty schemes use an empty cover; zero coefficients or zero outer terms
cause no failure. For Z/4 with outer Z/2, generator lifting constructs the nonsplit middle
term without claiming a splitting. The existing local-lift theorem has CommRing and
SheafOfModules hypotheses, so its adaptation remains explicitly open in the split node.
The existing constant-exact theorem is a presentation ingredient, not this conclusion.
Fresh searches used LeanFinder's query "locally constant middle sheaf in exact sequence
with constant finite module endpoints", Loogle ShortComplex.ShortExact (unknown identifier),
and grep IsLocallyConstant/exact/extension and ShortExact/Constant combinations; no exact
replacement was found. Also searched lean/Sheaf and the constructible modules directly.
Closing this lemma requires the substantial presentation argument, not a few-minute repair.

4. **Route and pruning: pass after import repair.** The shortest available stalk route is
Mathlib's exact finite-module lemma, already used. The cover argument preserves the corrected
finite-presentation route below the unit level; dag/units/sk-thm-properbasechange.json's
statement and three realized steps are untouched. All original KernelCokernel imports
support retained earlier proofs, and its two new imports are plain proof imports. Replaced
the new module's broad public Biproduct import with public Defs and ShortExact, exactly what
its signature needs. No globally pruned node or module. The old parent dependencies
lem-constructible-shortexact-local-lift and lem-constructible-constant-exact are both listed
under No longer needed and remain transitive ingredients of the split lemma.

5. **DAG: pass.** Diffed the parent node: only proof, proof_deps and proof_origin change.
Its steps record kernel/cokernel, cover binding via the new lemma, and finite stalks, and
proof_deps is their union. The new node has the source, complete proof steps, dependency
union, search records, created/blueprint/chapter/unit fields, and matching Lean signature.
The remaining formalization adaptation is named rather than silently using a mismatched
local-lift declaration. Maintainer-owned status and audit fields are retained.

Changes in this second reading: narrowed the new module's public imports to Defs and
ShortExact and updated the report accordingly; no statement, definition or proof-body change.
