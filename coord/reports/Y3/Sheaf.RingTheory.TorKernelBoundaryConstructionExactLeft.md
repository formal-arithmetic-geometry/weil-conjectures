## What changed

The existing theorem `CategoryTheory.tor_kernel_boundary_construction_exact_left`
is assembled from the two implications of `Function.Exact`, without changing its
signature. Its two new imports are proof-only. Two new modules state these strict
halves. The range half is fully proved using
`CategoryTheory.tor_kernel_boundary_naturality_of`, applied from the identity
presentation of F to q. The kernel half remains open and carries the complete
horseshoe comparison proof in its docstring.

The existing node now records the two actual dependencies of the Lean proof.
The kernel node preserves the original horseshoe proof plan and dependencies;
the range node records the shorter naturality proof.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.tor_kernel_boundary_construction_exact_left` by combining the two
strict halves. Added one hole:
`CategoryTheory.tor_kernel_boundary_construction_exact_left_kernel`
(node `lem-sc-p1-tor-kernel-boundary-construction-exact-left-kernel`).

Fully proved the new declaration
`CategoryTheory.tor_kernel_boundary_construction_exact_left_range`
(node `lem-sc-p1-tor-kernel-boundary-construction-exact-left-range`); it has no
`sorry` and its axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

This is a decomposition of the original item, not a complete proof of exactness:
one original hole closed and one smaller hole added, net zero holes removed.
The assembled theorem still depends on `sorryAx` through the kernel half.
There are no other holes or new definitions in the delivery.

## No longer needed

No imports removed and no modules globally pruned. All five original proof
dependencies remain in the kernel half's horseshoe plan:
`def-sc-p1-tor-kernel-boundary-construction`,
`lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-pbc-free-resolution-ses-split`,
`lem-weil-pbc-tensor-right-exact`, and
`lem-weil-pbc-tor-map-via-resolution-lift`.
The parent's direct dependencies are replaced by the two half-nodes, rather than
claiming these original prerequisites are unnecessary. Construction remains the
public import needed to state each theorem. NaturalityOf is a proof-only import
of the range module.

## Where the brief, the DAG or earlier work was wrong

The first submission left both implications open, gave only summary sentences
rather than a complete natural-language proof for each, and did not update the
existing node to follow the assembled Lean proof. Its range description also
conflated boundaries with the image of Tor(q,M): killing tensor boundaries alone
does not show vanishing on that image. A complete existing naturality theorem
supplies this missing argument without a homology comparison.

The kernel implication still requires the horseshoe homology comparison. It is
not claimed proved by the reduction. The new node retains the original complete
comparison argument and its prerequisites.

## New nodes

`lem-sc-p1-tor-kernel-boundary-construction-exact-left-kernel` states only that a
class killed by the boundary lies in the quotient Tor map's image. Its independent
horseshoe proof plan retains the original dependencies, without using the parent.

`lem-sc-p1-tor-kernel-boundary-construction-exact-left-range` states only vanishing
on the quotient Tor map's image. This is proved by naturality with zero kernel map
from the identity presentation; it is not an additional hole.

No statement or definition change records are needed: all existing signatures
and public imports are unchanged.

## Second reading by Y3

1. Compared the delivered parent with the repository using `diff -u`: the existing
signature and docstring are byte-for-byte unchanged. Only two plain imports and
the proof body change. Both other modules and nodes are new. No definitions or
other existing interfaces change. Verdict: pass.

2. Compiled all three modules in import order with `lcompile.py --all`. There is
one whole-proof `sorry`, in the public named kernel theorem, with a matching node
and full source/proof docstring; no forbidden declarations or hollow definitions.
Explicit `#print axioms` checks verify only the three standard axioms for the
range theorem, and those axioms plus `sorryAx` for the kernel and assembled parent.
Verdict: pass as a decomposition, not as a fully established exactness result.

3. Each new assertion is one strict implication, with no additional hypotheses.
For q=id the kernel is zero and Tor(q,M) is the identity, so both assertions hold.
For N=0 or M=0, Tor(N,M)=0 and both assertions hold. For q:Z -> Z/n and M=Z/n,
Tor(Z,M)=0 and the boundary is an isomorphism, so the kernel implication correctly
asserts a zero kernel, while the range assertion is automatic. The general
kernel proof is the horseshoe argument, including the comparison sign and lift
independence; no projectivity of F is assumed. Independent Lean Finder, Loogle,
and grep searches found generic homology exactness tools and the proved local
naturality theorem. No duplicate of the fixed-map kernel assertion was found.
Verdict: true and strictly smaller; range half repaired and proved.

4. Reviewed the construction and the proved naturality module. The shortest route
for the range half is naturality from id_F to q, with a=id, b=q, c=0; it avoids
rebuilding the horseshoe comparison. Every import has a statement or proof use.
The original prerequisites remain in the kernel plan, and no global pruning is
claimed. `dag/units/sk-thm-picard-duality.json` has empty realized lists; this
below-unit reduction leaves the unit statement, steps and realized record intact.
Verdict: pass.

5. Updated the existing node's proof, proof_deps and proof_origin to match the
assembly. Both new nodes retain the parent's chapter/unit, have matching Lean
statements, source, provenance, searches, creation and blueprint records. The
kernel plan preserves the original prerequisites; the range proof names the
naturality node. Verdict: pass.

Second-reading changes: proved the range half; expanded the remaining kernel
proof docstring; corrected both new nodes' proof plans and provenance; added the
missing parent-node update; rewrote the report to state the exact hole accounting
and distinguish decomposition from proof.
