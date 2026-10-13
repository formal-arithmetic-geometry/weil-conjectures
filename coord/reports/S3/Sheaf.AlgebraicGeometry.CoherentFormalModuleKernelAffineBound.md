## What changed

Replaced the hole in `AlgebraicGeometry.coherentFormalModule_kernel_affine_bound` with a
compiling proof, without changing its statement, universe, visibility, or docstring.
The proof obtains finite completed modules from a finite-level affine comparison, applies
the algebraic bound, and compares the two image submodules through their common value,
the image of the actual kernel in the level-m quotient.

Added `Sheaf.RingTheory.AdicKernelImageBound`, with a complete proof of
`LinearMap.adic_kernel_image_bound` from Mathlib's Artin--Rees theorem. Only the target
module N needs to be finite; the source M need not be finite. The proof lifts f(x)
through the image of the high ideal power of M, subtracts the lift, and checks that
this subtraction vanishes in the quotient using the numerical bound.

Added `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineKernelImageComparison` for
the remaining affine correspondence step. Its theorem compares arbitrary finite
levels l and k over m, with no bound c and no stabilization assertion. It packages
steps 1 and 4 of the original plan, not the theorem being delivered. Updated the
parent node's proof route and added a node for each new theorem. No existing
interface or definition changed; no downstream adaptation is needed.

The second reader made the algebraic helper import `Mathlib.RingTheory.Filtration`
privately and publicly import only `Mathlib.RingTheory.Noetherian.Defs`,
`Mathlib.RingTheory.Ideal.Operations`, and `Mathlib.LinearAlgebra.Quotient.Basic`,
which supply its signature. All three modules compile without errors or warnings
using lcompile.py. The algebraic
proof covers c=0, zero modules, and zero/unit ideals without any excluded cases. For
the comparison, equality at W=U proves the reverse implication; equality of affine
submodules gives equality of the associated quasi-coherent subsheaves, so the forward
implication applies also to non-affine W. Empty U has the zero section ring and zero
completion, with zero quotient submodules on both sides. The completed ideal is the
extension of I(U), rather than an ideal of the wrong ring.

## Proved and sorry left

Closed: `AlgebraicGeometry.coherentFormalModule_kernel_affine_bound`
(node `new-formal-kernel-affine-bound`), 1 of 1 original holes.

Fully proved new algebraic theorem: `LinearMap.adic_kernel_image_bound`
(node `new-adic-kernel-image-bound`), no sorry.

Added and left with exactly `:= by sorry`:
`AlgebraicGeometry.coherentFormalModule_affine_kernel_image_comparison`
(node `new-formal-affine-kernel-image-comparison`). This is one split-off hole.
There are no holes remaining in the item's module and no holes in definitions.
This delivery is a decomposition (one upper hole closed, one strictly simpler
comparison hole added), not a claim of a net decrease in holes or an unconditional
proof of the target closure. No data definition chooses an arbitrary witness from
an unproved existence theorem; the existential modules are eliminated only in a proof.

## No longer needed

Removed direct proof imports from the item's module:
`Mathlib.AlgebraicGeometry.Modules.Tilde`, `Mathlib.RingTheory.Filtration`,
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`,
`Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects`,
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

These dependencies remain needed through the new algebraic theorem or through the
proof plan of the comparison theorem; they are relocated, not pruned out of the
transitive argument. Every original proof dependency is still needed there.
The old parent proof dependencies removed from its direct route are:
`lem-weil-pbc-affine-tilde-gamma-adjunction`, `lem-weil-pbc-artin-rees`,
`lem-weil-pbc-coherent-formal-modules-affine`,
`lem-weil-pbc-coherent-formal-modules-restriction-objects`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, and
`lem-weil-pbc-quasi-coherent-module-kernel`. Each is retained in a new node's
proof dependencies. `lem-weil-pbc-adic-completion-noetherian` remains direct.
No node or module is claimed globally pruned. The unit's realized statement and
steps are unchanged; neither new node replaces a realized unit step.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface fault was found. The original plan is mathematically
consistent with Stacks 087X. The local literature/stacks-project/coherent.tex file
is absent on this machine, so the source was read at
https://stacks.math.columbia.edu/tag/087X and https://stacks.math.columbia.edu/tag/087W.
The level convention is n+1 and is retained in both new statements and the proof.

LeanFinder and Loogle found `Ideal.exists_pow_inf_eq_pow_smul` as the exact algebraic
ingredient. LeanSearch returned Internal Server Error. Repository and Mathlib searches
found no direct stabilization or completed-module kernel-image comparison theorem.
The affine equivalence, restricted object theorem, ideal-product sections theorem,
quasi-coherent kernel theorem, cokernel/image theorem, and tilde equivalence signatures
were read. Their remaining transport and image-identification glue is the new
comparison theorem, with the complete source argument in its docstring and node.

## New nodes

`new-adic-kernel-image-bound`, in dag/nodes/sec-proper-base-change/, records the fully
proved algebraic theorem: high reduced kernel images equal the actual kernel image.
It uses only the existing Artin--Rees node, with quotient and lifting glue proved in Lean.

`new-formal-affine-kernel-image-comparison`, in the same chapter, records the unproved
finite-level affine correspondence, using the existing formal affine equivalence,
restriction, ideal-product, quasi-coherent kernel/image and tilde nodes. It has no
Artin--Rees or stabilization conclusion and is strictly a part of the original argument.
There are no change records because existing statements and public imports are unchanged.

## Second reading by S3

1. PASS. Diffed the existing module against the repository. The only differences
are private proof imports and the theorem body. Independently compared its signature
byte for byte through `:=`: identical. Its universe, visibility, docstring and all
existing definitions are unchanged. The existing node changes only `proof`,
`proof_deps` and `proof_origin`; neither target statements nor unit files change.
The two other modules are new and declare only their respective named theorems.

2. PASS. Compiled the three modules in import order with lcompile.py, without
errors or warnings. Scratch-copy `#print axioms` checks give exactly propext,
Classical.choice and Quot.sound for LinearMap.adic_kernel_image_bound; the comparison
and parent additionally use sorryAx, as reported. There is exactly one textual hole,
the entire proof of the named comparison theorem. No forbidden declarations or
hollow definitions occur. The algebraic proof's lift, subtraction, ideal-power
inequality and reverse inclusion are correct; it does not require a finite source.

3. PASS. Read the comparison statement and its full docstring proof against Stacks
087W and 087X (https://stacks.math.columbia.edu/tag/087W and
https://stacks.math.columbia.edu/tag/087X). It asserts affine correspondence of
arbitrary finite-level image comparisons, without a stabilization bound; it is
strictly the transport part of the argument, not the original theorem renamed.
The completed ideal is the extension of the section ideal. Restricting scalars
preserves its generated submodules, and affine image submodules determine the
quasi-coherent image subsheaves, hence their ranges on all subopens. Equality at
U supplies the converse. Checked l=k, l=m, zero maps/modules, zero and unit ideals,
and empty U: no missing assumptions or false boundary cases were found.
Independent LeanFinder search for global-sections equivalence and kernel-image
quotient correspondence found completion evaluation formulas, not this result.
Loogle search `Submodule.mkQ, LinearMap.ker` found standard quotient formulas only.
Read and searched the formal affine equivalence and reconstruction modules, the
ideal-product affine sections theorem, and the quasi-coherent kernel/image library.
No existing theorem closes the remaining geometric correspondence in a few minutes.
The split-off theorem has a matching node and source-backed complete proof in words.

4. PASS after import repair. The parent genuinely combines the proved algebraic
bound with the geometric comparison, through the common actual-kernel image.
There is no shorter existing route found. All old proof dependencies removed from
the direct parent route are listed above and retained where needed; none is claimed
pruned from the closure. The `sk-thm-p1` realized statement and steps are untouched,
and the replacement occurs below the unit level. Repaired the helper's public
Filtration import: Artin--Rees is needed only in its proof. Public Noetherian.Defs,
Ideal.Operations and Quotient.Basic now expose exactly the signature ingredients.
The comparison's private imports retain its unproved correspondence proof plan.

5. PASS. Read all three delivered nodes. Their Lean records match their declarations;
the parent route names comparison, completion Noetherianity and the algebraic bound;
the algebraic node names Artin--Rees; the comparison node names the six geometric
ingredients used in its natural-language proof. New nodes have source, statement
and proof dependencies, searches, provenance, blueprint ancestry, chapter/unit,
status, created record and Lean record. No unit realization is displaced.

Changed only the algebraic helper's import visibility and signature-support imports,
and this report (explicit removed dependency ids and second-reading findings).
Closed one original named hole, added one strictly simpler named hole: decomposition,
net zero, with no globally pruned module. The fully proved algebraic helper is new
and does not count as closing an original hole.
