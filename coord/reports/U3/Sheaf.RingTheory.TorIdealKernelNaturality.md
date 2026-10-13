## What changed

Replaced `ModuleCat.exists_tor_ideal_kernel_naturality`'s single `sorry` by a
compiling proof, with its signature and public imports unchanged. Constructed
both multiplication maps and the semilinear ideal-tensor map using Mathlib's
tensor universal property. Proved the semilinear resolution lift by restricting
scalars and applying `free_complex_maps_to_resolution`; categorical exactness
is transported through the explicit underlying-module exactness criterion.
Proved the final kernel-preservation assertion using the two range descriptions
and commutation. Two new proof imports isolate the remaining homological work.
Updated the parent node's proof route to match the code.

## Proved and sorry left

Closed: `ModuleCat.exists_tor_ideal_kernel_naturality` (one of one original holes).
Its module has no remaining `sorry`.

Added exactly two named holes, each in its own new module:

- `ModuleCat.exists_tor_ideal_connecting_formula`, node
  `lem-weil-pbc-tor-ideal-connecting-formula`, in
  `Sheaf.RingTheory.TorIdealConnectingFormula`.
- `ModuleCat.exists_tor_ideal_comparison_compatibility`, node
  `lem-weil-pbc-tor-ideal-comparison-compatibility`, in
  `Sheaf.RingTheory.TorIdealComparisonCompatibility`.

This is a decomposition, not an unconditional proof: one upper hole closed,
two lower holes added (net -1 before the maintainer's closure accounting).
The first lemma involves only one ring and the connecting formula. The second
assumes the two connecting maps, their formulas, an ideal-tensor map, and an
already constructed resolution lift; it proves compatibility and independence.
Neither is the original assertion under a new name. No new definitions choose
witnesses from unproved existence results: the existential witnesses are used
only inside theorem proofs. No new axioms or changed signatures.

## No longer needed

No existing import was removed. Removed the unused
`Mathlib.RingTheory.Ideal.Maps` import from the new
`Sheaf.RingTheory.TorIdealConnectingFormula` module during second reading.

The parent proof no longer directly uses these old `proof_deps`:
`lem-weil-pbc-free-module-projective`, `lem-weil-pbc-projective-module-flat`,
`lem-weil-pbc-flat-tensor-exact`, `lem-weil-pbc-tensor-right-exact`,
`lem-weil-pbc-snake-lemma-modules`, and `def-weil-pbc-tor-modules`.
They remain in the lower statements' proof plans or statement definitions;
this is encapsulation, not closure pruning. The free-complex comparison
module is still directly used. No module is claimed to have left the targets'
import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or target/interface change was found. The original DAG
called construction and compatibility of cross-ring quotient tensor chain
maps elementary; their Lean glue is substantial and is isolated in the second
new statement. `TorLongExactFirstVariable` and the `TorKernelBoundary*` family
do not supply the required formula for the supplied free resolution: they
concern a fixed ring, and the kernel boundary uses Tor in the opposite variable.
No unit statement or realized step was bypassed.

The local `literature/stacks-project/algebra.tex` is not materialized. The
source was checked on the official Stacks pages for [00M5](https://stacks.math.columbia.edu/tag/00M5),
[00M6](https://stacks.math.columbia.edu/tag/00M6), and
[00LS](https://stacks.math.columbia.edu/tag/00LS). The detailed cycle-formula
argument follows the parent node's six-step plan and is marked agent-written.
LeanSearch was unavailable (Internal Server Error); this is recorded without
claiming an absence result. LeanFinder, Loogle, and local source/DAG searches
found no exact ready-made statement. The blueprint search `Tor ideal` found
no duplicate blueprint node.

## New nodes

`lem-weil-pbc-tor-ideal-connecting-formula`: isolates original Steps 1–3 over
one ring. Its docstring gives the flat tensor rows, cokernel identification,
snake descent, range argument and finite-sum formula. This is independent of
any ring map, comparison, or naturality assertion.

`lem-weil-pbc-tor-ideal-comparison-compatibility`: isolates original Steps 5–6,
given the connecting formulas and one lift. Its docstring gives the quotient
chain map construction, the mapped-cycle calculation, and independence by
injectivity. It does not assert multiplication formulas, ranges, or lift
existence. Tested mathematically on zero/unit ideals, zero modules, identity
maps and noninjective ring maps: the quotient and ideal containment arguments
apply in each case, and both sides vanish where required. No change records
or forced adaptations were needed.


## Second reading by U3

1. Interface: PASS. Compared the delivered parent module with the repository
   using `diff`; the existing theorem signature is byte for byte identical.
   Only its proof and four plain proof imports changed. There are no changed
   definitions, public imports, visibility changes, or forced adaptations.
2. Proof: PASS as a decomposition. All three modules compile locally without
   errors or warnings. Scratch copies with `#print axioms` for all three
   declarations show exactly `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. The only two delivered sorries are the named, documented new
   theorems listed above. No forbidden declaration or hollow definition occurs.
   The multiplication and ideal-tensor maps are explicit constructions; all
   existential witness elimination stays inside proposition proofs.
3. Split statements: PASS. Read both signatures and their complete proof
   docstrings. The single-ring statement is original Steps 1–3; compatibility
   assumes the connecting formulas and a supplied lift and handles Steps 5–6.
   Neither repeats the parent, and neither asserts the other's missing part.
   For I=0 the quotient complex is the exact resolution and Tor_1 vanishes;
   for I=R the quotient complex is zero and multiplication is an isomorphism.
   Zero modules give zero Tor and tensor groups. Identity maps and noninjective
   ring maps preserve the quotient relations because f(I) is contained in J;
   no flatness of A over R or injectivity of f is used. Every quotient tensor
   element lifts to y tensor 1, and a cycle's lifted differential is a finite
   sum of ideal multiples. Thus the formula hypotheses determine all Tor
   classes, rather than being vacuous assumptions. Repeated searches with
   different words using LeanFinder, Loogle, grep and local library inspection
   found quotient-tensor equivalences and cotangent connecting maps, not either
   full assertion. Inspected TorLongExactFirstVariable, the TorKernelBoundary
   family, and FlatTorIdealCriterion: none supplies the prescribed formula for
   this arbitrary resolution plus cross-ring compatibility. Neither remaining
   homological proof can be closed by a short application of these declarations.
4. Route and pruning: PASS after reporting repair. Read sk-thm-p1's realized
   statement and steps: this item is a tool below its realized nodes, and no
   unit route is bypassed. The parent uses the comparison theorem and two
   strict reductions, then proves kernel preservation from the ranges.
   Listed every old dependency no longer directly used by the parent under
   No longer needed, distinguishing that from closure pruning. Removed the
   unused Ideal.Maps import from the new single-ring module and recompiled it.
5. Nodes: PASS. Only lean/proof/proof_deps/proof_origin are changed on the old
   node. Verified each proof_deps is exactly the union of step uses, both new
   Lean signatures match their node records verbatim, the new nodes are absent
   from the repository, and their source, proof, search, creation, blueprint,
   chapter, unit and Lean records are present. The parent route matches its
   explicit maps, restricted-scalar lift, compatibility application and final
   range argument.

Second-reading changes: removed one unused import from the new connecting
module; completed the direct-dependency accounting above; appended independent
search records to both new nodes and this review. No theorem statement or proof
body was changed. One original hole is decomposed into two lower holes, so this
is not an unconditional proof or a positive net-hole result.
