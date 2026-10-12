## What changed

Completed `AlgebraicGeometry.Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule`
with its existing signature unchanged. Kernels and cokernels use the general ringed-space
closure theorem; binary sums use its extension clause and Mathlib's canonical split sequence.
For a quasi-coherent submodule, proved affine sections finite using sectionwise injectivity
and Noetherianity, descended finite type over all affine opens, and applied the existing
coherence criterion. The quotient follows from general cokernel closure.

Generalized the proved private `isFiniteType_over` helper from schemes to arbitrary
sites with binary products and pullbacks and arbitrary sheaves of rings. It transports
finite local generators through slice sites; first-level slices require only weak
sheafification, while iterated slices require sheafification. All site, category and universe
binders are explicit. The main proof specializes this helper to the scheme Zariski site.
The helper introduces no hole or public interface.
Only proof imports changed. Updated the existing DAG node's proof, proof dependencies, and
proof origin to describe the Lean argument. Source checked against Stacks Tags
[01Y0](https://stacks.math.columbia.edu/tag/01Y0) and
[01Y1](https://stacks.math.columbia.edu/tag/01Y1); restriction uses
[01B5](https://stacks.math.columbia.edu/tag/01B5).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule`
(node `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`). No sorry remains in this module;
no holes added or split off. The private restriction helper is proved.

The proof still depends on the existing holed general theorem
`AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`
(node `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`); this delivery proves the item
from that existing statement and does not claim its transitive axiom closure is sorry-free.
The coherence criterion and affine finite-type criterion are already proved in their modules.
The repaired module is checked by single-file compilation and the delivery dry run.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
  (node `lem-weil-pbc-quasi-coherent-module-cokernel-image`).
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
  (node `lem-weil-pbc-quasi-coherent-module-kernel`).

These nodes are no longer direct dependencies of this item's proof; no claim is made that
other targets cease to need them. Retained the Noetherian finite-module Mathlib leaf
`lem-weil-pbc-noetherian-finite-module-acc` for its finite-module Noetherian instance.

Deleted the two uncommitted split modules and placeholder nodes from the saved attempt:
`Sheaf.AlgebraicGeometry.CoherentBiprodLocallyNoetherian`
(`lem-weil-pbc-coherent-biprod-locnoeth`) and
`Sheaf.AlgebraicGeometry.CoherentSubmoduleLocallyNoetherian`
(`lem-weil-pbc-coherent-submodule-locnoeth`). Both are unnecessary: their conclusions are
proved within this item using existing declarations. No blueprint unit statement or realized
unit step is bypassed; the item remains within the same unit.

## Where the brief, the DAG or earlier work was wrong

The saved attempt had incomplete new-node metadata and no proof docstrings for its two
new holes. Rather than repair unnecessary statements, removed both and completed their
arguments. Its report also contained a purported second-reading section written by the
first worker; removed it for the independent second reader.

The original DAG's affine route is unnecessary for the kernel/cokernel/sum clause:
Stacks 01Y0 itself cites general coherent-module closure (01BY), exactly the existing
`coherent_kernel_cokernel_sum` statement. The submodule clause keeps the affine Noetherian
argument of 01Y1. Empty schemes, zero modules, and the zero-domain inclusion require no
extra hypotheses: the affine-cover criterion and injection argument retain those cases.


Repair of the returned delivery: the old scheme-only private helper duplicated
`isFiniteType_over` in `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`. That existing
helper is private and cannot be reused by importing its module. The repair takes the
requested generalization route: the local helper now applies to arbitrary sites and ring
sheaves, rather than just scheme structure sheaves. Its signature explicitly states the
site assumptions and distinguishes weak from full sheafification. Searches also found
private restriction lemmas in `FiniteTypeModuleSupportPullback` and
`AnnihilatorAffineBasicOpen`; neither is an accessible public theorem, and the latter
assumes full sheafification even on first-level slices. No other module or visibility
was changed. The previous second reading predates this repair and is retained below as historical
review evidence only; the repaired delivery still requires a fresh independent reading.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, a private helper, and the proof body differ. The DAG node changes only its proof metadata and dependencies. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`; it succeeds without warnings. Searched the file and delivery for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, and `debug.skipKernelTC`; none occur. The private helper is a genuine construction, and no definition contains postponed data. Verdict: pass. The proof relies on the already open general closure theorem as declared in the report.
3. The existing target statement is unchanged. No new public statement or split-off node was added, so there are no new truth or strength concerns. The proof uses the existing coherence criterion, affine finite-type criterion, Noetherian finite-module result, and general coherent kernel/cokernel/sum theorem; searches recorded in the node found no Mathlib duplicate. Verdict: pass.
4. The proof follows the shortest available route: general ringed-space closure for kernels, cokernels, and sums, with the affine Noetherian argument only for quasi-coherent submodules. Removed direct imports of the unused quasi-coherent kernel and cokernel modules, and removed the abandoned split modules and nodes. Verdict: pass.
5. The updated node proof, proof dependencies, and proof origin match the Lean proof, and the unit route remains represented by the original item. Verdict: pass.

Changed after this reading: appended this independent review section only; no Lean or DAG repairs were required.

## Second reading by M3

Fresh independent reading of the repaired delivery, 2026-10-13; the earlier reading above
is superseded.

1. Compared the sole delivered Lean module with the repository using `diff`, and checked
   the existing public theorem signature byte for byte with a script: identical. There
   are no changed definitions or public signatures and no change records are needed.
   The new helper is private, with explicit category, site and universe binders. The
   JSON diff changes only `proof`, `proof_deps` and `proof_origin`. Verdict: pass.
2. Compiled the module with `lcompile.py`: clean, 7.2 seconds. Compiled a scratch copy
   with `#print axioms` for both declarations. The generalized private
   `AlgebraicGeometry.Scheme.Modules.isFiniteType_over` uses only `propext`,
   `Classical.choice`, `Quot.sound`. The public theorem uses those and `sorryAx`, as
   expected from the reported existing general closure theorem. No `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, or kernel-check bypass occurs in
   the delivered source; there is no new data definition or arbitrary witness chosen
   from an unproved existence theorem. Verdict: pass, with the existing transitive
   hole explicitly retained rather than claimed closed.
3. No statement was split off and no node was added. Read the generalized helper from
   its pulled covering through its transported generators. The slice-cover argument
   uses each lifted covering arrow, and `GeneratingSections.map` retains the finite
   generator index; its colimit preservation follows from the explicitly proved
   left-adjoint instance. This proves a restriction property strictly below the item,
   not a restatement. The first-level weak sheafification assumptions are genuinely
   weaker than those of the private helper in `AnnihilatorAffineBasicOpen`; the helper
   in `FinitePushforwardCoherent` is scheme-specific and private. Fresh LeanFinder
   search for finite type under slice restriction and Loogle search for
   `SheafOfModules.IsFiniteType`, together with `rg` over the library and Mathlib's
   generators API, found no accessible existing restriction theorem. Empty schemes,
   zero modules, and zero-domain inclusions require no extra hypotheses. Stacks
   [01B5](https://stacks.math.columbia.edu/tag/01B5) gives the local finite-generator
   definition; the general site version is the explicit proved generalization, not
   a theorem asserted by that tag. Verdict: pass.
4. Read the general closure, coherence criterion and affine criterion modules. The
   proof applies general closure directly for kernels/cokernels, uses the canonical
   split short exact sequence for the biproduct, and uses Noetherian affine sections
   only for the submodule. This matches Stacks
   [01Y0](https://stacks.math.columbia.edu/tag/01Y0) and
   [01Y1](https://stacks.math.columbia.edu/tag/01Y1). All three proof imports are used;
   the two public imports are required by the statement. Every old `proof_deps`
   omitted from the new list is recorded under `No longer needed`: the quasi-coherent
   kernel and cokernel/image nodes. These are direct-dependency prunings only. Read
   `dag/units/sk-thm-p1.json`, including `realized`: neither omitted node carries one
   of its realized steps, and the unit's statement and route are preserved. Verdict:
   pass.
5. Checked each new proof dependency's declaration or Mathlib match and the union
   of the proof steps' `uses`. The node describes the actual general closure,
   finite-generator restriction, affine injection and finite-type descent argument;
   its source and proof origin agree with the checked Stacks proofs. No new nodes
   require metadata. Verdict: pass.

Changed after this reading: appended this fresh independent review and its explicit
axiom/search evidence only. No Lean or DAG repair was necessary.
