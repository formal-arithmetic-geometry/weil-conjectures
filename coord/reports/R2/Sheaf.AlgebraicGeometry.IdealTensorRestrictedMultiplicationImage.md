## What changed

Repaired the returned proof of
`AlgebraicGeometry.Scheme.Modules.ideal_tensor_restricted_multiplication_image`.
The public theorem signature and both public imports are unchanged. No other module
was adapted and no definition was changed.

Removed the nine duplicated private helper declarations identified by the return.
The replacement product theorem `restricted_product_affine` proves quasi-coherence
and computes the range after an arbitrary module morphism, not just the product
inclusion. The main proof uses it with the multiplication morphism itself.
`restricted_powers_affine` handles arbitrary quasi-coherent ideal inclusions,
not just ideal-sheaf-data realizations, and all exponents including zero.
`restricted_image_range_affine` handles any isomorphic presentation of the image.
`restricted_hom_zero_of_basis` and `restricted_subobject_le_of_basis_range`
work on any topological basis, not just affine opens. The ideal realization's
quasi-coherence and the ideal-data specialization of the product formula are
local consequences of kernel closure and these general calculations.

The node's proof and proof origin now describe these stronger helpers and the
composite-range argument. Every helper is proved; no helper is an unproved alias.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.ideal_tensor_restricted_multiplication_image`
(node `lem-pc-ideal-tensor-restricted-multiplication-image`).
No sorry remains in the item and no sorry was added. Zero split off.
Single-file compilation is clean. The delivery dry run checks all added constants'
axioms; the transitive dependencies are not claimed independently sorry-free here.

## No longer needed

Pruned planned dependency `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
and module `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`:
the generalized composite-range and arbitrary-power calculations replace its
needed special cases. Its open-restriction conclusions are unused.

Also avoided `Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerImage` and
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`. The affine comparison
now uses general image presentations and general topological-basis detection.
The original public imports remain. Redundant proof imports
`Mathlib.CategoryTheory.Subobject.Limits` and
`Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` remain removed.
Tensor comparison, affine cokernel/image, affine localization, and
kernel/cokernel closure remain needed. Other importers may still require the
avoided modules; this delivery makes no claim about their whole-library closure.

The returned helpers `ideal_qc`, `product_qc`, `multiplication_range`,
`product_range`, `powers_qc`, `powers_range`, `image_range_affine`,
`hom_zero_of_affine`, and `subobject_le_of_affine_range` no longer occur as
added library declarations in this delivery.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated private special-case theorems. Merely renaming
those declarations would not repair the rejection. This repair removes those
declarations and strengthens the product, power, image, and basis calculations
as described above.

Importing the named existing theorems cannot supply them: they are private in their
modules. Those modules also have source import paths back to this item, through
ClosedImmersion, DirectImage, the proper-cohomology ideal-comparison chain, and
IdealPowerTensorImageLift. A scratch import confirmed that the named private
constants are unknown to an importer. The repair uses lower-level imports and
stronger local helper declarations, without introducing a cycle or changing
another group's module.

The unit `sk-thm-picard-coherence` has no realized statements or steps that this
route bypasses. Exponents zero and one, zero ideals and modules, and empty opens
require no additional hypotheses. No new nodes, interface changes, or forced
adaptations were needed. The previous second-reading text was removed because
it reviewed the returned version, not this repair; the second reader must review
this version afresh.


## Second reading by R2

1. Compared the sole delivered module with the repository using `diff` and checked
   the existing theorem signature byte for byte: identical. Both public imports,
   the existing docstring, and all definitions are unchanged. No change records
   or adapted modules are needed. Verdict: pass.
2. Compiled the module locally through `lcompile.py`: clean. Scanned for `sorry`,
   axioms, unsafe/opaque declarations, extern, implemented_by, and kernel-check
   bypasses: none. A scratch copy printing the main theorem's axioms reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   No data is chosen from an unproved existence result. Verdict: pass.
3. There are no split-off statements or new holes. Read each proved private helper:
   composite ranges follow from tensor induction and linear maps preserving ideal
   multiples; recursive powers explicitly handle zero and one; image presentations
   are transported by isomorphisms; basis detection uses sheaf separatedness and
   cokernel lifting. Zero ideals, zero modules, and empty opens cause no exceptions;
   at n=m=0 the unit ideal acts as the identity. Verdict: pass.
4. Searched local Lean sources by affine pushforward, image ranges, recursive powers,
   and basis containment, and repeated LeanFinder, Loogle, and grep searches with
   composite-range/map-scalar queries. Loogle found `Submodule.map_smul''`, already
   used; the tensor subtype-range result does not directly identify the sheaf tensor
   sections for an arbitrary morphism i. The matching special-case sheaf helpers
   are private and their modules create source import cycles. Removed one remaining
   exact duplicate affine pushforward declaration (see below). Proof imports are
   needed for tensor comparison, affine image sections, basic-open localization,
   and cokernel closure; all are non-public. The old proof dependency no longer used
   is listed under No longer needed. The unit's realized statement and step lists
   are empty, so this local calculation bypasses no realized unit route. Verdict: pass.
5. Compared node JSON: only `proof`, `proof_deps`, and `proof_origin` differ from
   the repository. The dependencies are exactly the union of proof-step uses, and
   their Lean declarations supply the localization criterion, affine localization,
   kernel/cokernel closure, tensor comparison, and image calculation actually used.
   No new nodes are present. Verdict: pass.

Second-reading repair: removed `restrictedImage_pushforward_qc`, whose statement
was an exact duplicate of the upstream affine pushforward theorem. Its required
closed-subscheme localization calculation now sits inside `hIq` in the main proof;
importing the upstream module would introduce a cycle. The other general helpers
and the main range comparison are unchanged. No signature, definition, public
import, DAG route, or hole count changed. Closed one original hole; added zero.
