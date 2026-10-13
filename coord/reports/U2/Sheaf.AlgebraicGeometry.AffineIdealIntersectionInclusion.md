## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_ideal_intersection_inclusion` in
`Sheaf.AlgebraicGeometry.AffineIdealIntersectionInclusion`, without changing its
signature, visibility, or existing docstring. Added private, fully proved helpers
for affine pushforward quasi-coherence, ideal quasi-coherence, recursive
multiplication/power ranges, quasi-coherence and section ranges of
pullbacks, and extension of affine range inclusions to all subopens. Their arguments
adapt the existing private helpers of `ArtinReesAffineComparison`; that module is
not imported and its Artin-Rees theorem is not used.

Added proof-only imports of `Modules.QuasiCoherentCokernelImage`, upstream `Modules.QuasicoherentKernel`,
`Modules.QuasicoherentBinarySum`, `QuasiCoherentTensorProductAffineSections`, upstream
`Mathlib.AlgebraicGeometry.Modules.Tilde`, and `Mathlib.CategoryTheory.Abelian.Basic`.
The original public imports remain necessary for the statement. Updated the item's
DAG proof, proof dependencies, and proof origin to match the implemented argument.

The intersection is a quasi-coherent pullback. The affine hypothesis gives the
range inclusion on U. Compose the pullback inclusion with the cokernel projection
of I^n G -> F; localization and sheaf separatedness extend its vanishing to W.
The kernel/image identity and monicity then give the required section lift.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.Modules.affine_ideal_intersection_inclusion`
(node `lem-pc-affine-ideal-intersection-inclusion`). All private helpers are proved.
No holes remain in the delivered module; no holes or new public statements were added.
This is a proof, not a decomposition. The single-file compile passed without warnings.
The delivery dry run also checks every declaration's axioms.

## No longer needed

Pruned `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` from the original
planned proof dependencies. Its module,
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`, was tried
during proof development and removed; it was not imported in the repository version. Its needed power calculations are proved here by recursion from tensor
and image calculations. This module cannot be imported: its CoherentFormalModule
import leads back to the assigned theorem. The original public imports remain.
Kernel and cokernel/image nodes are still needed. No new modules are created.
`Sheaf.AlgebraicGeometry.ArtinReesAffineComparison` is not a dependency of this proof;
only its already proved helper arguments were adapted locally. No Artin-Rees bound,
coherence, Noetherian hypothesis, or completed-module theory is needed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned ideal-times-sections dependency would
close an import cycle through CoherentFormalModule, the direct-image finite-free
complex, and CoherentKernelIdealIntersectionBound. The dry-run guard detected it.
The replacement proves ideal quasi-coherence from the principal-open criterion and
basic-open localization; the affine-pushforward proof is adapted from upstream
DirectImage.AffineMorphism without importing that module (also cyclic). No existing
module or interface needed adaptation. The original DAG omitted the explicit tensor-sections,
binary-sum, principal-open-criterion, and basic-open-localization dependencies needed for this implementation;
they are now recorded. The affine equivalence need not be applied as a categorical
factorization: vanishing of the composite with a cokernel gives the same inclusion.
The unit has no realized nodes, and its higher-level route is unchanged.
The argument includes m=0 and n=0 through the unit-ideal calculation. Empty U or W,
zero modules, and zero or unit ideals need no additional hypotheses: the local cover
argument and sheaf separatedness also apply to the empty open.

The principal-open criterion node is an existing, fully proved upstream tool from
another unit; it is used only to prove quasi-coherence of the affine pushforward.
It does not replace any step of this unit.


## Second reading by U2

1. Compared the complete module against the repository version. The existing
   theorem signature, visibility, and docstring are byte for byte unchanged.
   The new helper declarations are private proved theorems; there are no new
   definitions or changes to any target. Verdict: pass.
2. Compiled the delivered module locally with lcompile.py (20 seconds, no warnings).
   Independently compiled a scratch copy with an explicit `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.affine_ideal_intersection_inclusion`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Read every helper and the final
   argument; there are no sorries, forbidden declarations, or witness constructions
   from unproved existence. Verdict: pass.
3. No statements were split off and no holes were added. Checked the recursive
   power calculations at zero and one, the mono requirement in the cokernel lift,
   and the empty-open coverage case. No extra finiteness or affine hypothesis on W
   is used. Verdict: pass; no split-off node review is needed.
4. Read from the final pullback argument down through the multiplication and
   localization helpers. Searched the library for affine vanishing, range inclusion,
   and multiplication range, and used LeanFinder with the alternative query about
   morphisms determined by affine global sections. No usable shorter public result
   was found; matching library arguments are private or in cyclic dependencies.
   Each added proof import supplies a used theorem or categorical construction;
   both public imports supply the unchanged signature. The only old proof dependency
   removed is the ideal-times-sections node, now explicitly listed above. Checked
   `dag/units/sk-thm-picard-coherence.json`: its realized statement and step lists
   are empty, and this argument changes no unit route. Verdict: pass.
5. Compared the original and delivered node records. Only proof, proof_deps, and
   proof_origin differ. All six recorded dependencies are used in the helpers,
   and their Lean declarations agree with the calls. The five proof steps describe
   the tensor/image calculation, pullback, affine lifting, localization vanishing,
   and mono-image lift actually implemented. No new node is needed. Verdict: pass.

Second reading changed only this report: clarified that the pruned import was a
trial import rather than an import of the repository version, distinguished private
helpers from new public statements, and recorded the independent checks. The Lean
proof and DAG needed no repair.
