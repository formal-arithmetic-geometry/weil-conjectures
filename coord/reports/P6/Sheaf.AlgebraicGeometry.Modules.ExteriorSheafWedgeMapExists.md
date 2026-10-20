## What changed

Completed the retirement item recorded in coord/retire-items.tsv, rather than adding
another proof of the already proved duplicate theorem. Withdrew
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists through deleted.txt.
Redirected lem-sc-exterior-sheaf-wedge-map to the existing upstream theorem of the same
name in WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists.
The delivery tool represents withdrawal as an empty module; no module imports it.

Both direct consumers, Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel and
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt, now import the upstream
module privately. Both were unclaimed. Their public signatures, public imports, existing
docstrings and existing determinant proofs remain unchanged except that the wedge-map
application uses a fully proved private transport lemma.

The private comparisons have identity components between the legacy and native exterior
presheaves. Their naturality follows from the legacy unique restriction characterization
and upstream ExteriorPower.map_ιMulti. Sheafifying gives comparison isomorphisms. Unit
naturality proves their hom maps preserve pure wedges; hom_inv_id gives the inverse
formula. Conjugating the upstream wedge map by the tensor of the source comparisons
and the inverse target comparison gives the legacy formula by
tensorHom_app_tmulSection. The LocalAt consumer also transports the upstream map on
the third exterior power for S.g through the same comparison. This constructs real data
and uses no unproved choice theorem.

Updated the two consumers' node proof descriptions to include this comparison step.
Their original dependencies remain, with the exterior-sheaf definition added explicitly
for the transport. The source library and Challenge.lean are untouched. Change record:
coord/changes/retire-exterior-sheaf-wedge-map-P6.md.

LeanFinder and Loogle searches found ordinary exterior-power infrastructure. Repository
rg found the existing upstream theorem, its native exterior presheaf construction, and
exactly two direct consumers. The import-direction checks accepted the two replacement
imports. Initial dependent equality rewrites were unsuitable for the section types;
explicit isomorphisms avoid that problem. Profiling isolated expensive scalar-interface
conversion at the restriction formula; with_unfolding_all at that exact application
reduces elaboration without changing definitions, splitting files, or raising the limit.

Validation: both adapted consumers compile cleanly under the 60-second single-file
limit. The delivery axiom probes and server preflight passed in the required dry run.
The source/interface comparison reports no consumer interface changes or public additions.

## Proved and sorry left

The assigned module already had zero textual sorries: closed 0 of 0, added 0, split off 0.
Its public theorem AlgebraicGeometry.Scheme.Modules.exteriorSheaf_wedgeMap_exists is now
provided by the existing upstream module (node lem-sc-exterior-sheaf-wedge-map).

The LiftWedgeKernel consumer has five completely proved private helpers:
exteriorPresheafComparison, exteriorComparison, exteriorComparison_hom_wedge,
exteriorComparison_inv_wedge and wedgeMap_legacy. The LocalAt consumer has those five
plus the completely proved exteriorSheaf_map_from_upstream helper. No sorry remains in
either adapted consumer. Their public theorems determinant_liftWedge_kernel_exists
(new-determinant-lift-wedge-kernel) and determinant_wedgeMorphism_local_data_at
(new-local-wedge-at) retain complete proofs. No new theorem or node is split off.

The comparison and transport work for arbitrary schemes, modules and natural degrees,
including degree zero in either block, empty schemes and zero rings. They use neither
local freeness nor exactness. The subsequent quotient argument retains precisely its
original hypotheses. No statement or definition has been weakened.

## No longer needed

Removed Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists from the imports of
both direct consumers; the duplicate module has no remaining Lean importer. Replaced
those proof imports with WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists.

The retired module's private restriction_wedge, wedgeMul and wedgeMul_wedge helpers and
its duplicate public wedge theorem are unnecessary: the upstream implementation supplies
the same construction. Its direct imports of Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf,
WeilConjectures.AlgebraicGeometry.Modules.TensorSection,
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal and
WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension are
removed with its implementation. These dependencies still serve the consumers or the
upstream construction; no claim is made that they leave the global target closure.

No DAG node is deleted. The wedge-map node is retained and attached to the upstream
theorem. The two consumer nodes retain their determinant route. The unit
sk-thm-picard-rr has empty realized statement/step arrays; this change preserves its
exterior-power determinant argument.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an item with a proof hole, whereas the current queue marks
this module as a retirement with zero holes. The human's retirement hand-off in
coord/changes/retire-sheaf-twins-20261020.md supplies the concrete required repair.
The API difference is real: exteriorSheaf uses restrictions chosen by uniqueness, while
the upstream exteriorPower uses the native presheaf construction. Replacing imports
alone would not preserve the consumers' types. The explicit, fully proved comparisons
resolve that difference without modifying upstream declarations or legacy definitions.

Repair of return C-991b0: rebased new-local-wedge-at onto the current K8 record.
Preserved K8's first-step comparison argument, its two dependencies, and the K8
proof-origin attribution and place verbatim. Kept the delivered second step,
proof_deps and P6 note, and retained the current independent-review metadata.
No Lean statement or proof was changed by this repair.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
