## What changed

Replaced the earlier sandbox's invalid package projection with a genuine finite-affine-cover
reduction of `AlgebraicGeometry.coherentFormalModule_kernel_stabilized_bound`, preserving its
signature and public imports exactly.

The proof chooses a finite affine cover, takes the finite supremum of its local bounds,
and compares both requested images with the same locally stable image. It then applies
`AlgebraicGeometry.module_subobject_eq_on_cover`, proved in the new module
`Sheaf.AlgebraicGeometry.ModuleSubobjectEqOnCover`. That helper uses sheaf separatedness
for the cokernel and `Abelian.monoLift` to obtain both subobject inclusions. Its proof
needs no coherence or Noetherian assumptions.

The sole remaining step is stated in the new module
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelAffineBound`: stabilization on one
fixed affine open, with equality of section ranges on all its subopens. Its docstring
and node explain the completed-module Artin--Rees calculation, including the index shift.
The main module imports both new modules only for its proof.

All three modules compile together without warnings through the prescribed local compiler.
The generic cover theorem has a complete proof. The original theorem is reduced to one
local theorem; this is a decomposition, not a complete proof independent of sorry.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.coherentFormalModule_kernel_stabilized_bound`
(node `new-kernel-stabilized-bound`).

Added and proved:
`AlgebraicGeometry.module_subobject_eq_on_cover`
(node `new-module-subobject-eq-on-cover`). Its private helper
`comp_cokernel_eq_zero_on_cover` is also proved.

Added hole, the only sorry in the delivered sources:
`AlgebraicGeometry.coherentFormalModule_kernel_affine_bound`
(node `new-formal-kernel-affine-bound`). It is strictly local; the global finite-cover
bound and descent argument are proved in the original module. One delivered-source hole closed and one
added: a decomposition, plus a proved reusable sheaf lemma. These direct hole counts
do not assert the ledger's import-closure net: the local node's planned dependency
imports also enter that closure.

Edge cases were checked mathematically: empty covers use Finset.sup = 0 and the sheaf
axiom on the empty scheme; a larger bound works by comparing both indices to the local
stable value. The affine statement's zero ideal, unit ideal, zero modules, zero morphism,
and identity morphism all admit c = 0. In the general affine argument levels l and m
mean the quotients by powers l+1 and m+1; l >= m+c gives l+1-c >= m+1.

## No longer needed

No original imports, nodes, or modules were pruned: the original module had only its
statement import and its node had no proof dependencies. The finite-cover/Artin--Rees
route is preserved, and no blueprint unit realization is bypassed.

Removed the earlier attempt's sandbox-only
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelStabilizedPackage` and node
`new-kernel-stabilized-package`; neither is imported or delivered. They contained the
entire original conclusion as a conjunct, so their projection was not a reduction.

## Where the brief, the DAG or earlier work was wrong

The earlier package theorem merely restated the whole goal inside a conjunction.
It has been removed, not used as an intermediate statement.

The original DAG supplied a finite-cover proof sketch with no dependency nodes. The
new local affine node records the actual unresolved step; the cover comparison and
finite maximum are now proved in Lean. Existing affine reconstruction, restriction of
formal objects, and Artin--Rees nodes supply its proof plan without depending on the
original bound. No statement or definition was changed and no adaptation is required.

The canonical source file `literature/stacks-project/coherent.tex` is absent in this
read-only checkout. The proof of Stacks Lemma 087X was read directly at
https://stacks.math.columbia.edu/tag/087X ; its displayed preimage calculation is the
source of the new affine statement. The needed existing Lean signatures were read.
LeanSearch returned Internal Server Error on both queries; search records say
unavailable, rather than claiming no match. Loogle found the algebraic Artin--Rees
lemma; LeanFinder and source searches located the sheaf-separatedness and abelian
factorization ingredients used in the proved cover theorem.

The existing node's created.item is a module name rather than a DAG node ID, so
`tools/blueprint_refs.py ancestor new-kernel-stabilized-bound` returns None. New nodes
record that missing nearest blueprint ancestor as null, with the known node chain and
precise source step; the delivery does not change the existing provenance fields.

## New nodes

`new-formal-kernel-affine-bound`, in
`dag/nodes/sec-proper-base-change/new-formal-kernel-affine-bound.json`, states the
single-affine-open stabilization calculation. It is the remaining sorry and supplies
the only local bounds used by the main proof. Its plan cites existing restriction,
affine reconstruction, completion-Noetherian, Artin--Rees, and affine sheaf/module
comparison nodes.

`new-module-subobject-eq-on-cover`, in
`dag/nodes/sec-proper-base-change/new-module-subobject-eq-on-cover.json`, states and
proves the general descent of equality of monic module subsheaves from local section
ranges. There are no new holes in this module. No change record is needed.


## Second reading by B3

1. **Interface comparison — pass.** Read the repository and sandbox modules and
   compared the original module with `diff -u`. The only changes to the existing
   module are two plain proof imports and the theorem body; its signature, docstring,
   visibility, and original public import are byte for byte unchanged. The other two
   modules are new. The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. No definitions or target statements change, and no change record
   or forced adaptation is needed.

2. **Proof and axioms — pass with the declared local hole.** Compiled all three
   modules in import order through `lcompile.py`; no errors or warnings. Read the
   whole cover helper, including its private separatedness proof: naturality restricts
   the cokernel composite to each intersection, local range inclusion kills it,
   and `Abelian.monoLift` gives the correct direction of each subobject inequality.
   A scratch `#print axioms` check gives only `propext`, `Classical.choice`, and
   `Quot.sound` for `module_subobject_eq_on_cover`. The global bound and the local
   affine theorem additionally use `sorryAx`, as expected. The only source `sorry`
   is the named affine theorem. There is no data construction, hollow definition,
   forbidden declaration, or arbitrary witness chosen from an unproved existence
   theorem; the chosen natural-number bounds are logical witnesses within a proof.

3. **New statements — pass.** Read Stacks Tags [087X](https://stacks.math.columbia.edu/tag/087X)
   (claim (a) and its preimage computation) and [087W](https://stacks.math.columbia.edu/tag/087W),
   the formal-module definition, and every dependency statement of the affine node.
   Artin--Rees applied to the image of the completed linear map gives the stated
   preimage identity. With r = l+1, the inequality l >= m+c kills its error term
   modulo I^(m+1). Equality of image subsheaves on U gives equal section ranges
   on every subopen; no affineness of their intersections is assumed. The local
   theorem keeps all original mathematical hypotheses and solves only the affine
   calculation, while the delivered global proof supplies compactness, the maximum,
   and descent. It is strictly part of the argument, not a renamed global goal.
   Checked empty opens/schemes, zero/unit ideals, zero modules, zero and identity
   maps, and the boundary l=m+c. The general cover theorem also covers empty and
   infinite covers and needs no coherence. Fresh LeanFinder, Loogle, Mathlib grep,
   repository grep, and upstream source searches found ingredients but no exact
   existing declaration for either new statement. Loogle's `Abelian.monoLift` query
   reported an unknown identifier, so it supplies no negative evidence.

4. **Route and pruning — pass.** The finite affine cover and Artin--Rees route from
   087X is retained. Read `dag/units/sk-thm-p1.json`, including `realized`; none of
   its statement or step realizations is replaced or bypassed. The original node's
   `proof_deps` is empty, so the report's list of original dependencies no longer
   needed is complete (none). Read the existing
   `quasicoherent_subobject_eq_of_affine_cover`: it requires an already established
   subobject inequality and quasi-coherence and does not replace the more direct
   two-inclusion separatedness proof here. Nearby paired-affine range helpers are
   private and specialized to ideal products. Retained the proved general helper.
   Main proof imports and the cover helper's abelian/separatedness imports have
   their stated uses. The affine node's planned dependency imports were missing;
   added them as plain imports, including Mathlib's Artin--Rees module, as required
   by the standing brief. They are proof dependencies, not public interface imports.
   No further local closure is available in a few minutes: reconstruction,
   restriction transport, and the affine image comparisons are substantial.

5. **DAG agreement — pass.** Checked the finite-cover/supremum and the two local
   comparisons against the main node's three proof steps and exact two
   `proof_deps`. The affine node records restriction, affine reconstruction,
   completion Noetherianity, Artin--Rees, and quasi-coherent kernel/image comparison;
   their recorded Lean signatures support those steps. Artin--Rees is the Mathlib
   leaf `Ideal.exists_pow_inf_eq_pow_smul`, not a missing library declaration.
   The proved cover node has no project proof dependencies and records precisely
   the cokernel separatedness and mono-lift argument. Both new nodes have sources,
   docstring proofs, matching signatures, provenance, search records, and the
   original chapter/unit. No DAG cycle through the original bound is introduced.

Second reading changed only the affine module's missing plain proof-dependency
imports and this report (including clarification that direct one-for-one hole counts
are a decomposition, not the ledger's import-closure net). It changed no statement,
definition, or mathematical proof. Recompiled the full set after the import repair
and checked the three public declarations' axioms. No modules were pruned.
