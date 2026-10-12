## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.isCoherent_homObj` with a compiling proof.
The proof chooses one local kernel model at each point, proves that these opens
cover the scheme, restricts coherence of F, applies finite-sum and kernel closure,
transports coherence through the supplied isomorphism, and applies locality.
The statement and existing declaration docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.CoherentHomLocalKernel`, containing the named local
kernel statement `AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_coherent`.
It packages exactly steps 1--3 of the original plan: coherent G admits local finite
presentations, restriction commutes with Hom, and left exact precomposition gives
the local kernel model. It assumes no coherence of F and concludes no coherence;
the coherence and gluing argument is written in the original module. This is a
strict part of the argument, not the original theorem under another name.

Changed the original module's proof-only import of HomFinitePresentationKernel
to a proof-only import of CoherentHomLocalKernel. The finite-presentation kernel
module remains imported by the new module, whose documented proof needs its
precomposition theorem. Updated the original DAG node's proof, proof_deps and
proof_origin, and added a node for the new statement. No existing signature,
public import, definition, target, or external module was changed.

Both delivery modules compile together through lcompile.py without warnings.
The independently compiled scratch work is outside lean/ and is not delivered.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.isCoherent_homObj`
(node `lem-weil-pbc-coherent-sheaf-hom-coherent`). There is no `sorry` left in
Sheaf.AlgebraicGeometry.CoherentSheafHom.

Added one hole, the whole proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_coherent`
(node `lem-weil-pbc-coherent-hom-local-kernel`). It is in its own module with a
source and complete proof in words. No other holes were added.

This is a decomposition: one upper hole closed, one strictly smaller local-model
hole added, net zero before any pruning. The original proof also uses the existing
coherent_kernel_cokernel_sum and coherent_module_local_on_open_cover theorems,
whose pre-existing holes are unchanged. It does not establish an axiom-free proof
of the full coherence result yet.

The local statement was checked against Modules 01BW and the first assertion of
01CQ in the local Stacks source checkout. Edge cases: the target F is arbitrary;
no Noetherian assumption is used; ranks zero are allowed; the zero source can use
rank n = 0, giving the zero Hom kernel; the zero target gives zero sums and Hom;
on an empty scheme the local assertion is vacuous, and the point-indexed covering
in the main proof still has supremum top. For positive ranks, precomposition and
basis evaluation are exactly the kernel argument of 01CP/01CQ.

## No longer needed

Removed the direct proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel` from the
original module. Its node `lem-weil-pbc-sheaf-hom-finite-presentation-kernel`
remains needed below the new local kernel node and its module remains imported
there. Thus this is not a claim of global pruning.

The original node no longer directly lists def-pur-sheaf-hom,
def-weil-sheaf-of-modules-category, pqf-def-coherent, or
lem-weil-pbc-sheaf-hom-finite-presentation-kernel as proof dependencies; they are
needed within the new local-model node. The original public imports of Coherent
and InternalHom still specify its statement and were preserved. The coherence
closure and locality modules are both used. No module or mathematical dependency
is globally pruned by this delivery; pruned: none.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or unit route was found. The original
plan's elementary local-presentation and restriction steps require nontrivial
Lean glue: coherence is defined on Over sites, while the locality theorem is
stated for open subschemes, and Hom restriction must cross that equivalence.
The existing finite-presentation kernel statement does not itself supply the
local presentations or the scheme restriction identification. The new statement
isolates those steps and the local kernel construction, without a new definition
or arbitrary witness chosen inside a definition.

Search found upstream homObjFreeIso and overHomObjIso, but neither alone supplies
that missing combined interface. The only coherent-to-finite-presentation proof
found locally is private and assumes a locally Noetherian scheme, so it cannot
be applied here. A separate generic scratch proof from finite global generators
and finite-type relations compiled; its attempted instantiation encountered
expensive elaboration and was not delivered. These are unfinished proof attempts,
not reported tool failures or mathematical obstructions.

The LeanSearch service returned Internal Server Error and was recorded as
unavailable, not as a negative mathematical search. Loogle, LeanFinder and grep
searches ran. Blueprint searches for coherent/Hom and 01CQ found no imported
blueprint statement matching the new local kernel assertion. None of this item's
nodes realize a unit's own statement or step; sk-thm-p1 and its route are retained.

## New nodes

`lem-weil-pbc-coherent-hom-local-kernel`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-coherent-hom-local-kernel.json`,
records the local finite-sum kernel model with arbitrary target F, its 01BW/01CQ
source, the original local-presentation/restriction/left-exactness proof steps,
three kinds of actual search, its blueprint ancestry, and the exact Lean
signature in Sheaf.AlgebraicGeometry.CoherentHomLocalKernel. It is the sole new
node and sole remaining new hole. There are no change records because existing
interfaces are unchanged.

## Second reading by H1

Independent second reader; I did not write either delivered module.

1. **Visible interface: PASS.** Read the complete diff of CoherentSheafHom against
   the repository. The only changes are the proof-only import and the theorem body.
   Compared the existing theorem signature byte for byte, including both coherence
   hypotheses, the universe, Hom argument order, and conclusion: identical. The
   existing docstring, public imports, definitions and visibility are unchanged.
   No forced adaptations or change records are needed.
2. **Proof and trust: PASS as a decomposition.** Independently ran lcompile.py
   --all on both delivered modules in import order; both compile without warnings.
   Read the cover proof: each point belongs to its chosen U, hence their supremum
   is top, also on the empty scheme. The locality theorem's first clause gives hFU;
   the closure theorem's finite-sum clause gives hn and hm, its kernel clause
   gives hk, and its isomorphism clause with e.symm transports hk to the restricted
   Hom. Its second locality clause gives precisely the original conclusion.
   The only delivered sorry is the entire named local-kernel theorem. There are
   no definitions or hidden local holes, forbidden declarations, trust overrides,
   or data definitions choosing arbitrary witnesses. Choices of U and e occur
   only inside the proof. Compiled a separate scratch module printing axioms for
   both declarations: exactly propext, Classical.choice, Quot.sound, sorryAx.
   Thus the original theorem remains dependent on open lower statements; this is
   one closed upper hole and one added lower hole, not an axiom-free result.
3. **Split statement and searches: PASS.** Read the new theorem, its whole node,
   Coherent's definition, HomFinitePresentationKernel's two statements, and the
   proved upstream homObjFreeIso and overHomObjIso. Independently read Stacks
   [01BW](https://stacks.math.columbia.edu/tag/01BW),
   [01CQ](https://stacks.math.columbia.edu/tag/01CQ),
   [01CP](https://stacks.math.columbia.edu/tag/01CP), and
   [0E8H](https://stacks.math.columbia.edu/tag/0E8H). Coherent G supplies local
   generators and finite type relations; precomposition with their presentation
   is left exact, and evaluation on the finite bases produces the asserted
   kernel model. Restriction agrees on all smaller opens, including scalar
   actions. The statement permits arbitrary F and concludes only a local model,
   so it is a strict part of the coherence argument, not a renamed coherence
   theorem. Tested zero ranks, G zero (n = 0), F zero, and the empty scheme;
   no Noetherian hypothesis or nonempty-rank assumption is needed. The new
   module's docstring gives all three construction steps and its matching node.
   Repeated independent LeanFinder, Loogle and msearch grep searches using
   finite-product kernel and IsFiniteType queries, and searched lean/ and the
   source checkout for restriction/kernel, finite-presentation and coherence
   terms. No existing statement supplies the combined local model. The upstream
   free-Hom and Over-Hom isomorphisms are only pieces, and finite-presentation
   constructors still require constructing the local relations. There is no
   quick complete proof of this remaining hole from these interfaces.
4. **Shortest route, imports and pruning: PASS.** The delivered upper proof uses
   exactly the local kernel model, restriction/locality, and finite-sum/kernel/
   isomorphism closure. Its two public imports define its interface; the three
   proof imports are used. The new module's public imports supply coherence,
   Hom/restriction and biproduct notation/instances; its plain kernel-sequence
   import retains the documented plan for the open proof without exposing it.
   Checked the old proof_deps against the report's No longer needed list: all
   four removed direct nodes are named; they remain below the local model.
   No module is globally pruned. Read dag/units/sk-thm-p1.json and its realized
   statement and four step lists: neither delivered node realizes a unit step,
   and the unit route and realized record are unchanged.
5. **Node records: PASS.** The existing node changes only proof, proof_deps and
   proof_origin. Its three steps match the Lean argument just checked. For each
   delivered node, proof_deps is exactly the union of step uses. The new node
   has source, self-contained statement/stmt_deps, proof, origin, search records,
   created metadata, blueprint ancestry, chapter/unit and exact Lean declaration
   record, and lives in the original chapter. Its finite-type/presentation and
   restriction steps use the recorded definitions; its non-elementary Hom
   exactness step cites the existing kernel-sequence node. No source assumption
   is silently strengthened or lost.

**Second-reading changes:** added this independent review and additional logged
searches. No Lean or DAG repair was necessary; the existing decomposition is
correct. Reaffirmed holes closed: isCoherent_homObj (1); holes added:
homObj_locally_kernel_of_coherent (1); net zero; pruned none.
