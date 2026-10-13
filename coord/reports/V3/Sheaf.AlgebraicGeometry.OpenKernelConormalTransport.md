## What changed

Proved `AlgebraicGeometry.Scheme.Modules.open_kernel_conormal_transport` in
`Sheaf.AlgebraicGeometry.OpenKernelConormalTransport`, with its public signature
verbatim unchanged. Added four proved private helpers: the closed-immersion ideal
section range, the open-square zero equation, restriction of the actual kernel
with its inclusion, and a general open pullback section comparison with its unit.
All original imports remain necessary; no imports were added. Updated the existing
node's proof, proof_deps and proof_origin to the implemented argument.

The section comparison uses uniqueness of the left adjoints of the two composite
pushforward functors. Its linearity is checked through resLE_app_top. Naturality
on the equality morphisms of opens proves the unit equation explicitly.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.open_kernel_conormal_transport`
(node `lem-sc-open-kernel-conormal-transport`): 1 original hole closed.
Added holes: none. Remaining holes in the delivered module: none.
This is a proof, not a decomposition. All private helpers are fully proved.
Local single-file compilation passed; the required delivery dry run is recorded
by the delivery tool. The only data chosen from a theorem are the prescribed
adjunctions, which are uniquely determined by their unit formulas.

## No longer needed

Removed proof dependency `lem-pc-module-pullback-identity-composition`:
`nonempty_tensorPullbackComp` and `nonempty_tensorPullbackId` are not used.
Their module `Sheaf.AlgebraicGeometry.TensorPullback` remains needed for the
functor definitions through the existing public adjunction import, so no module
is claimed to leave the targets' import closure. No imports were removed.
No other node or module is pruned. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned tensor-pullback composition isomorphism only asserts Nonempty and
would not itself supply the required unit normalization. Instead the proof
constructs the comparison directly with leftAdjointUniq and its unit equation.
The existing globally closed kernel restriction theorem is inapplicable to g:
the proof uses the actual categorical kernel without assuming g is globally
closed or quasi-compact. It only uses closedness of the local resLE morphism.

The proof applies to empty opens as well: the open equality maps and sectionwise
kernel isomorphisms require no points, nonempty opens, affine hypotheses, or
extra quasi-coherence assumptions. No statements or definitions were changed.


## Second reading by V3

1. **Public interface: pass.** Diffed the only delivered Lean module against
   the repository version. The entire signature of
   `AlgebraicGeometry.Scheme.Modules.open_kernel_conormal_transport`, including
   its local scalar instance, both inclusion and unit equations, and the
   quantifier over all sections, is byte-identical. No existing definition or
   visibility changed. The added declarations are four private proved helpers;
   no change record or forced adaptation is needed.

2. **Proof and axioms: pass.** Read the complete proof and compiled the delivered
   module with lcompile.py (17.2 seconds, no errors or warnings). Compiled a
   scratch copy with `#print axioms` for the main theorem and all four helpers
   (19.2 seconds). Each uses exactly `propext`, `Classical.choice`, `Quot.sound`:
   no `sorryAx`. No sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow
   definition occurs. The ideal comparison is constructed by `kernel.lift` and
   proved sectionwise bijective. The chosen adjunctions come from a proved
   existence theorem with its explicit unit formula; no arbitrary data are
   extracted from an unproved existence statement.

3. **Split statements and edge cases: pass.** There are no split-off statements
   or new nodes. Checked the four private helpers: range_kernelIdeal uses
   closedness of its own morphism; open_kernel_zero_iff uses the preimage equality
   to ensure the source open-inclusion map on functions is an isomorphism;
   actual_kernel_restrict_iso requires only closedness of resLE, never closedness
   of g; open_pullback_sections_transport requires no closedness. Empty opens,
   the identity morphism with top opens, and a zero kernel introduce no extra
   assumptions. The inclusion equation uniquely determines the transported
   section t. Read Stacks [01R3](https://stacks.math.columbia.edu/tag/01R3),
   [00A0](https://stacks.math.columbia.edu/tag/00A0), and
   [0096](https://stacks.math.columbia.edu/tag/0096): the implementation proves the
   localization comparison used in the conormal argument, with restriction and
   adjunction supplying its unit compatibility.

4. **Route, search, and pruning: pass.** Independently searched by kernel
   restriction and pullback section terminology with rg, and used msearch grep
   for unit_leftAdjointUniq_hom_app and resLE_app_top. Read the upstream
   range_map_kernelι and injective_map_kernelι proofs, Mathlib's open restriction
   adjunction interface, TensorPullback's identity/composition statements, and
   OpenRestrictionKernelModule. The latter assumes a globally closed morphism,
   so it cannot replace the actual-kernel helper here. The matching small range
   and open-zero helpers in FormallyUnramifiedConormal/OpenRestrictionKernelModule
   are private; importing their unrelated thickening/conormal dependencies to
   reuse them would enlarge this module's route. No shorter public theorem for
   the required normalized section equivalence was found. The three public
   imports supply tensorPullback/its chosen adjunction, ideal-module notation,
   and closed-immersion notation in the public signature; there are no added
   proof-only public imports. Compared all five old proof_deps: only
   lem-pc-module-pullback-identity-composition is unused, and it is already listed
   above. Read dag/units/sk-thm-picard-duality.json: its realized statement and
   step lists do not name this supporting node or the removed dependency; the
   unit route and realized record are unchanged. No module is claimed pruned.

5. **DAG correspondence: pass.** Diffed the node JSON: only proof, proof_deps,
   and proof_origin changed. Step 1 is the explicit kernel-lift comparison and
   sectionwise inverse. Step 2 constructs beta using the two composite
   adjunctions and pushforwardComp/pushforwardCongr; resLE_app_top checks scalars.
   Step 3 evaluates unit_leftAdjointUniq_hom_app and uses naturality on equality
   maps of opens, then transports through delta inverse. Read both cited Mathlib
   leaf nodes: the conjugate-unit leaf supplies exactly uniqueness with unit
   compatibility, and the open-restriction leaf supplies restrictAdjunction and
   its sectionwise unit. The remaining ideal and tensor-adjunction dependencies
   match the code. No new-node fields are required.

Second-reading changes: appended this independent review and recorded explicit
axiom checks and search findings. No Lean proof, signature, import, or DAG repair
was necessary. Holes closed remain 1; holes added remain 0.
