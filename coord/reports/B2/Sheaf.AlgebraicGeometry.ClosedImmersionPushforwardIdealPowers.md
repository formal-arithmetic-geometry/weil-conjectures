## What changed

Replaced the sole proof hole of
`AlgebraicGeometry.Scheme.closedImmersion_pushforward_idealPowers` without changing
its signature, visibility, definitions, or original docstring.

The affine formula uses `modulePullbackIdealQuotient` and `IsAffineOpen.preimage`.
Quasi-coherence of the extended ideal follows from its actual kernel construction,
the source library's closed-pushforward quasi-coherence theorem, and
`Modules.isQuasicoherent_kernel`.

Added two modules, each with one public theorem and one new node:

- `Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerImage`: the remaining geometric
  comparison of image subobjects, with a complete affine-basis proof in its docstring.
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardCokernel`: a complete proof that
  closed pushforward preserves cokernels of arbitrary module morphisms. It forgets
  to abelian sheaves, uses the existing natural closed-pushforward stalk comparisons,
  and detects exactness on stalks. No quasi-coherence assumption is needed here.

The original module constructs the quotient isomorphism using equal image subobjects,
`cokernel.mapIso`, `cokernelImageι`, and preservation of the upstairs cokernel. It proves
its projection identity, then proves naturality and level compatibility by cancelling
cokernel projections. Private helpers for the categorical comparison and the equation
for the canonical quotient maps are completely proved. The existential family of
isomorphisms is determined uniquely by its composite with the epimorphic projection;
it does not choose arbitrary geometric data.

All three modules compiled cleanly together through `lcompile.py --all`. No adaptation
of an existing module, signature change, or change record was needed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.closedImmersion_pushforward_idealPowers`
(node `lem-weil-pbc-closed-immersion-pushforward-ideal-powers`). There is no direct
`sorry` anywhere in its module.

Also proved the new theorem:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_pushforward_preservesCokernel`
(node `lem-weil-pbc-closed-immersion-pushforward-cokernel`). Its proof is complete,
including the empty-source case and points outside the closed image.

Added exactly one hole:
`AlgebraicGeometry.Scheme.closedImmersion_idealPower_image`
(node `lem-weil-pbc-closed-immersion-ideal-power-image`). It asserts only the image
comparison, with no affine ideal formula, quasi-coherence clause, quotient isomorphism,
projection identity, naturality, or level compatibility. These other parts are proved
in the original module. Edge cases checked mathematically: empty schemes and affine
opens, the zero module, zero and unit ideals, and level one. There is no Noetherian or
finite-generation hypothesis in either new statement.

This is a decomposition: one original hole closed and one strictly smaller hole added,
so the textual net is zero. Existing imported holes, in particular
`modulePullbackIdealQuotient`, remain existing frontier items and are not new holes.
The quotient isomorphism and its compatibility laws are implemented rather than
moved into a new assumption.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`;
- `Sheaf.AlgebraicGeometry.Coherent` (already supplied by the public statement imports);
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`;
- `Sheaf.AlgebraicGeometry.TensorPullback`.

The original proof no longer needs node
`lem-weil-pbc-closed-immersion-pushforward-annihilated` or its module: the needed
quasi-coherence is already proved in the source library. The remaining image node's
plan also uses that proved source theorem, not the annihilated-module theorem.
The affine-sections node `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
is still needed by the plan for the new image node, but not by the original module's
completed proof. Its module can still be reached through other imports; no claim of
global unreachability is made.

Second reading also removed the redundant proof import
`Mathlib.CategoryTheory.Abelian.Exact` from the new cokernel module.

The old proof-only citations `def-weil-affine-spectrum`,
`def-sbc-closed-immersion-ideal-sheaf`, `def-pc-module-pullback`, and `pqf-def-coherent`
are no longer direct proof dependencies of the original node. Its statement dependencies
are preserved. No unit statement or realized unit step was removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan's affine-basis construction of the quotient isomorphism is unnecessary
once the product image comparison and preservation of cokernels are available.
The categorical cokernel comparison supplies the isomorphism directly, and both
compatibility laws follow from the projection equation. The old suggestion to obtain
extended-ideal quasi-coherence from `modulePullbackIdealQuotient` also does not match
that theorem's formal signature; the kernel construction gives it instead.

The source library already proves the quasi-coherence of closed pushforward and of
kernels. The general closed-pushforward quasi-coherence declaration appears in the
Lean declaration list of `lem-pc-closed-immersion-coherent-cohomology`, even though that
node's prose emphasizes its coherent, locally Noetherian specialization. The delivery
uses the existing declaration's actual general signature and adds no such hypotheses.

LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder and source
searches found ideal-sheaf functoriality and generic cokernel tools, not the geometric
comparison. The Loogle query `cokernel, image` reported an unknown identifier and was
not treated as evidence of absence. Blueprint searches for closed immersion, cokernel,
and ideal power found no existing node with either new statement; the flat ideal-power
pullback blueprint statement is different and is not used.

WANTED: the locally absent Stacks sources `coherent.tex` (proof of 088A), `modules.tex`
(01AG), `sheaves.tex` (00AE), and `sites-modules.tex` (03DA), for the two new nodes.
Their mathematical arguments are written out in the docstrings and nodes and marked
as agent-written; no unavailable document is claimed to have been read.

## New nodes

`lem-weil-pbc-closed-immersion-ideal-power-image`, in
`dag/nodes/sec-proper-base-change/`, isolates original plan steps 3--6. It retains the
geometric comparison as the one remaining item and states its affine calculation and
gluing proof in full. It is realized by `ClosedImmersionIdealPowerImage.lean`.

`lem-weil-pbc-closed-immersion-pushforward-cokernel`, in the same directory, supplies
the exactness needed in original plan steps 7--8 for all module sheaves. It is fully
proved from the existing closed-pushforward stalk theorem, exact forgetting to abelian
sheaves, and Mathlib's stalkwise exactness criterion. It is realized by
`ClosedImmersionPushforwardCokernel.lean`. Both nodes inherit the original chapter,
unit, and blueprint ancestor. No change records are needed.

## Second reading by B2

1. Compared the delivered original module with the repository using `diff` and the
   declaration-table check. Every existing signature, visibility and docstring is
   unchanged byte for byte. Only its proof, private helpers and proof imports differ.
   Both other modules and their declarations are new. No change record is required.
2. Compiled all three modules in dependency order through `lcompile.py --all`, with
   no errors or unexpected warnings. There is exactly one direct `sorry`, in the
   reported public image-comparison theorem; none in any definition or private helper.
   Checked `#print axioms` for all three public theorems using temporary probe copies:
   the cokernel theorem uses only `propext`, `Classical.choice`, and `Quot.sound`;
   the original theorem and the open image theorem also use `sorryAx`. No forbidden
   declarations, attributes or compiler switches occur. The chosen isomorphisms are
   fixed by their composite with an epimorphic cokernel projection; the proof chooses
   no arbitrary geometric witness from a holed existence statement.
3. The remaining image comparison is true and is only clause (2), strictly smaller
   than the original conjunction. Read its complete affine-basis proof and matching
   node. Checked empty source/opens, zero module, zero ideal, unit ideal, identity
   immersion and level one: both images coincide. Closed pushforward preserves
   cokernels for arbitrary modules, including the empty source; the implemented
   proof reflects exactness through the faithful forgetful functor and tests stalks.
   Repeated searches with different wording using LeanFinder, Loogle (`Ideal.map_pow`),
   and `rg` on Sheaf, upstream modules and Mathlib. `Ideal.map_pow` supplies the ring
   step; ideal-sheaf functoriality does not supply the sheaf-product comparison.
   Read `affine_pushforward_ideal_product`: its pulled-back inclusion differs from
   the power-of-comapped-ideal inclusion here, so it is not a direct replacement.
   Bridging those inclusions still requires the geometric power comparison.
4. Read the proof from the original conjunction downward. Quasi-coherence uses
   the actual ideal kernel and proved upstream results; the affine formula uses
   the existing pullback theorem. The quotient comparison is constructed with
   cokernel universal properties, and naturality and level compatibility cancel
   cokernel projections. No whole-item restatement has been substituted. Checked
   every removed old proof dependency against `No longer needed`; retained the
   extended-ideal, affine-preimage, pullback and formal-quotient dependencies.
   Read `dag/units/sk-thm-p1.json`, including `realized`: this item is below those
   realized steps, and the changes replace no unit statement or unit step.
5. Read all three delivered nodes. Their proof steps describe the implemented
   categorical/stalk arguments and the remaining geometric argument, and each
   `proof_deps` is precisely the union of its steps' `uses`. The new nodes have
   source, proof origin, searches, creation, blueprint ancestry, chapter, unit and
   matching Lean records. Their theorem signatures match the delivered Lean.

Verdict: accepted as a decomposition, one original hole closed and one strictly
smaller hole added (net zero); the separate new cokernel theorem is fully proved.
Second reading removed the redundant proof import
`Mathlib.CategoryTheory.Abelian.Exact` from the new cokernel module after a clean
compile without it, and added this review and independent search/axiom evidence.
Removal trials confirmed that its public module-sheaf import and proof-only
`Mathlib.Algebra.Category.Grp.Zero` import are required. No proof repair was needed.
