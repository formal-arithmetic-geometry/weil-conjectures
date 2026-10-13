## What changed

Proved `AlgebraicGeometry.coherentFormalModules_affine_quotientCone_complete` from
one new affine projection comparison and the existing completion theory. Its signature,
visibility, and the explicit cone definition are unchanged.

Added the fully proved private helper `isLimit_of_complete_quotient_projections`.
For any cone of A-modules with surjective projections of kernel I^(n+1)M and an
I-complete vertex, it constructs the universal lift. The first isomorphism theorem
identifies each quotient with the diagram object. Cone naturality and surjectivity
identify the transitions with `Submodule.factorPow`. Mathlib's
`IsAdicComplete.StrictMono.lift`, `mk_lift`, and `eq_lift` supply existence, the
projection equations, and uniqueness for the strictly increasing sequence n+1.
No chosen object from an unproved existence statement is used.

The main theorem obtains completeness of the restricted finite completed module
using `AdicCompletion.isNoetherianRing`, `AdicCompletion.isAdicComplete_self`,
`finite_module_complete_over_complete_noetherian`, and
`IsAdicComplete.map_algebraMap_iff`. It then applies the proved helper. The scalar
formula is proved separately: evaluation kills r-algebraMap(a), the completion
kernel theorem puts this difference in I^(n+1)B, ideal-product induction puts its
action on x in I^(n+1)M, and the projection kernel formula kills it. Subtraction and
A-linearity give the requested equality.

Added `Sheaf.AlgebraicGeometry.FormalModuleQuotientAffineProjection`, with one
public theorem and its DAG node. This states only surjectivity and the kernel of a
single affine sheaf quotient projection for an arbitrary module over an arbitrary
commutative ring. It assumes neither Noetherianity, finiteness, nor completeness,
and says nothing about limits or completed scalar actions.

Replaced the item's direct proof import of
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` with the
new comparison module. The second reading removed the redundant proof import
`Mathlib.LinearAlgebra.Isomorphisms`.
Updated the theorem node's proof, proof_deps and proof_origin to describe the code.
No other existing module is adapted and no statement or definition is changed.
Both sandbox modules compile cleanly through lcompile.py --all.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.coherentFormalModules_affine_quotientCone_complete`
(node `lem-weil-pbc-coherent-formal-modules-affine-quotient-cone`). Its proof has no
sorry. The private helper also has a complete proof.

Added one hole:
`AlgebraicGeometry.formalModuleQuotient_affine_projection`
(node `lem-weil-pbc-formal-module-quotient-affine-projection`), in its own new module.
Its proof is exactly `by sorry`. The docstring provides the full argument and source.
There are no other sorries in the delivered files.

This is a decomposition: one upper hole closed and one strictly smaller affine
comparison hole added, net zero holes before considering imports. The substantive
limit construction and scalar calculation are now proved. The theorem still rests
on this new hole and on any existing holes reachable from its completion dependencies;
this is not a claim of an axiom-free final result.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` from the
item. It remains a proof dependency of the new affine comparison, so its module and
node are not globally pruned. Likewise the affine tilde/gamma node is now used below
the comparison rather than directly in the main theorem.

No dependency module can be claimed pruned from the targets' import closure.
Removed the redundant added import `Mathlib.LinearAlgebra.Isomorphisms`; the quotient
isomorphism API is already available through the retained imports.

The old direct `proof_deps` entries
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` are no longer direct
dependencies of the item; both are retained below the new comparison.

All other original imports remain necessary for signatures, construction, or the
written completion proof. No blueprint unit statement or realized proof step is
bypassed; the quotient-cone node is not itself in sk-thm-p1's realized steps.

## Where the brief, the DAG or earlier work was wrong

The original plan's completion ingredients are usable. Its phrase identifying
projections with algebraic quotients did not have an interface for this particular
transported projection: the existing ideal-times theorem provides the power-inclusion
ranges and first-power product formula, but not the full arbitrary-positive-power
quotient projection kernel formula over A. That comparison is isolated as the new
node rather than replacing the whole original theorem by another name.

Searches included LeanFinder for complete modules and affine quotient sections,
Loogle for IsAdicComplete.lift, and grep of Mathlib and both library roots. No exact
existing comparison was found. LeanSearch was unavailable with Internal Server Error;
this is recorded as unavailable in the new node, without a negative verdict.
The source files are absent from this machine's literature directory; the Stacks
pages for Tags 087W, 05GG, 01I8 and 01IC were read online. The comparison's argument
is the affine tensor/cokernel correspondence, also recorded in existing DAG nodes.

The new statement was checked mathematically for I=bottom (zero kernel and an
isomorphic projection), I=top (zero quotient and full kernel), the zero module,
m=1, and arbitrary non-Noetherian A. Its positive-exponent assumption matches the
formal system's n+1 indexing and avoids relying on a separate zero-power convention.

## New nodes

`lem-weil-pbc-formal-module-quotient-affine-projection` states the single-level
comparison described above, with source, proof steps, searches, edge cases, and the
verbatim Lean signature. Its proof depends on the existing affine tilde/gamma,
ideal-times, tensor-sections, and quasi-coherent cokernel-image statements. It does
not import or depend on the quotient-cone theorem, so there is no circularity.
No change records are needed because no existing interface changes.


## Second reading by U3

1. Compared both delivered modules with the repository. The only existing module changes
are its proof, the fully proved private helper, and ordinary proof imports. The canonical
cone definition, both existing declaration signatures, their visibility and docstrings
are byte for byte unchanged. There are no interface changes or forced adaptations.
The relevant open change record `triangulated-hom-colimit-proof-context.md` lists this
module as unchanged and requires no adaptation here. Verdict: pass.

2. Compiled both files together with `lcompile.py --all`; no errors or warnings.
Inspected every delivered declaration and searched for forbidden constructs: the only
sorry is the named new comparison theorem; no hollow definitions or arbitrary witness
chosen from an unproved existence theorem. Scratch-copy `#print axioms` checks show only
`propext`, `Classical.choice`, `Quot.sound` for the canonical cone and private limit helper;
the main theorem and comparison also use `sorryAx`, exactly as disclosed. Verdict: pass
as a decomposition, not an axiom-free final theorem.

3. Read the comparison, its node, the actual quotient/power definitions, and the existing
ideal-times, tensor-sections and cokernel-image interfaces. The comparison concerns one
quotient projection and has no finiteness, completeness, limit or completed-scalar
conclusion, so it is strictly a part of the original argument. Checked m=1, I=bottom,
I=top, the zero module and arbitrary non-Noetherian rings: the formula remains correct.
Verified its source against Stacks https://stacks.math.columbia.edu/tag/01I8 and
https://stacks.math.columbia.edu/tag/01IC (tensor correspondence and exactness).
Repeated LeanFinder, Loogle and grep searches with different queries, and searched both
library roots. No accessible exact public comparison was found. A source-only private
`quotient_affine` in `CoherentMapReductionTorsionKernel` proves the sheaf-level part,
but `import all` followed by a scratch application reports unknown identifier in the
current compiled library; it also does not supply the A-linear unit transport asserted
here. No duplicate of it was added. Closing the comparison is not a few-minute application
of the available interface. Its docstring and node give a complete correct argument.
Verdict: pass.

4. Read the main proof from the limiting-cone and scalar conclusions downwards. The
surjective quotient equivalences, successor compatibility, StrictMono lift, fac and uniq
proofs are correct; the scalar argument uses the completion kernel formula and scalar
tower correctly. Retained the useful construction without rewriting it. Tested removal
of proof imports: `Mathlib.LinearAlgebra.Isomorphisms` is redundant and was removed;
`Mathlib.RingTheory.AdicCompletion.LocalRing` is necessary (without it the compiler
cannot resolve `isAdicComplete_self` or `pow_smul_top_eq_ker_eval`). All old direct DAG
dependencies dropped by the proof are now explicitly named under No longer needed.
Read `dag/units/sk-thm-p1.json`: neither this cone node nor the new comparison replaces
any realized unit statement or step. No module is globally pruned. Verdict: pass.

5. Compared node statements and Lean signatures, proof steps and their dependency union.
The original node changes only stage-3-owned proof fields; the new node has its source,
complete proof steps, searches, creation provenance, blueprint ancestry, chapter/unit
and verbatim Lean record. Dependencies match the completion, projection, cone and scalar
arguments; there is no circularity. Verdict: pass.

Changed only the redundant added Mathlib proof import and this report (including explicit
old dependency names). One upper hole closed, one strictly smaller hole added; net zero
holes before import-closure accounting. No proof or statement repair was needed.
