## What changed

Completed the duplicate repair using the source-library relative Proj. The obsolete item is
withdrawn under brief step 8d, with its Lean path listed in `deleted.txt`. The source
Basic module is publicly imported by the actual bridge and remains available there.
Removed `AlgebraicGeometry.exists_relativeProjData` and its private independent gluing.

In `RelativeProjAffineRestriction`, `RelativeProjAlgebra.affineData` explicitly packages
the actual section rings, homogeneous image submodules, and restriction maps as source
`Scheme.GradedAlgebraData`. Degreewise quasi-coherent base change is proved from total
section base change using direct sums. The documented grading comparisons give an
identity-on-sections local Proj isomorphism and its base and transition equations.
`RelativeProjAlgebra.realization` uses exactly the source `relProjGluingData`, with
restriction charts derived from `relProjHom_preimage`. Its scheme and structural map
are the source `relProj` and `relProjHom`; there is no new colimit construction.

Adapted the sole user, `RelativeProjectiveSpace.construction`, to use this explicit
realization instead of choosing a witness of the removed theorem. Its type and every
other existing consumer signature remain unchanged. The source library is untouched.
The change record is `coord/changes/U2-relative-proj-source-api.md`, with the full
consumer audit. Updated the existing definition, affine-restriction and existence
nodes to describe the bridge and preserve the source-library uniqueness attachment.

Validation: the three edited modules compile without errors or warnings (20.2 s,
2.1 s, and 26.3 s). Two separate `rfl` probes verify that `A.realization.proj` and
`A.realization.π` are definitionally the source `A.affineData.relProj` and
`A.affineData.relProjHom`. The axiom probe reports only the standard axioms and
`sorryAx` inherited from the existing named prerequisites in `RelativeProjData`;
this repair does not claim those prerequisite proofs are closed.


Direct importer verification: `ProjectiveBundleFrameModels`,
`ProjectiveBundleTautologicalData`, `ProjectiveBundleTautologicalGeometry` and
`VectorProjectiveCompletionData` compile against the changed modules (1.7, 11.0,
9.7 and 2.6 s). Checks of `GloballyGeneratedProjectiveBundle`,
`ProjectiveBundleQuotientGeometry` and `Targets.AffineSpaceRationalLine` stop before
checking those modules: the service cannot compile the dependency
`Sheaf.SixFunctorsBasics.BrownHypotheses` from `c453867b785f` (`IsCompactObject`
is unknown at lines 65 and 178; a subtype-membership mismatch follows at line 190).
`ProjectiveConstructibilityFromLine` stops at its missing root `Mathlib.olean`.
These dependency files are not part of this packet. No adaptation to them is claimed.
The only direct user of the removed theorem is the edited `RelativeProjectiveSpace`,
which does compile cleanly.

## Proved and sorry left

The assigned item already had zero holes. This is a definition/interface repair,
not a newly closed proof hole: zero holes closed, zero holes added, zero split off.
There are no `sorry`s in any of the three delivered Lean modules.

The existing local-transition theorems remain proved. The new
`gradeRestriction_baseChange`, `gradeIso_naturality`, and
`affineRestrictionIso_hom_ι` have complete proofs, as do all fields of `affineData`,
`affineRestrictionIso`, and `realization`. Existing prerequisite holes remain in their
existing modules and are not copied or added here.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.RelativeProjExists` from the consumer's import closure:
it has no remaining Lean importers or declarations. Its path is in `deleted.txt`;
the delivery tool lands the expected empty module. The replacement argument and
parent dependency updates are included in this same packet, as step 8d requires.
Removed its duplicate `exists_relativeProjData`, `chartFunctor`, `chartGluing`,
`chartIso`, `construction`, helper lemmas and helper instances.

The consumer replaces its public import of that module with
`Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction`. The retired item removes
its public import of `RelativeProjData` and private import of
`RelativeProjAffineRestriction`. Source Basic is publicly imported by the bridge.
The bridge now publicly imports source Basic because its explicit data definitions
use that API; the existing GradedTensor and affine-section base-change proof imports
remain necessary. Removed its now-redundant private import of
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme`: source Basic already imports
it, and the bridge no longer assembles the spectrum inclusion square itself.
No other declared mathematical dependency or module is withdrawn.

The DAG node `lemma-nagata-relative-proj-exists` remains: its full existence,
affine compatibility, cover independence and chart-preserving uniqueness are the
unchanged source-library results. Its attachment to the removed duplicate theorem
has been replaced by the explicit sheaf-input adapter. The unit has no proof steps
to bypass, and its statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The F3 delivery proved the former hole, but did not complete the assigned duplicate
migration: it implemented a second gluing rather than using source relative Proj.
The source input differs in representation (submodule-graded affine sections versus
an algebra sheaf), so the necessary repair is the explicit affine-data bridge.
Relocating the old theorem or rebasing its already complete proof would not repair it.

The bridge imposes no extra assumptions: degree zero need not equal the base,
intersections need not be affine, and zero rings, empty schemes and degree-zero-only
algebras are handled by the same source construction. The scalar extension checks
use actual restriction maps, not arbitrary isomorphic affine models. The replacement
of the chosen realization preserves every specified chart and its equations.

The original `GloballyGeneratedProjectiveBundle` compiles against the published
baseline in 4.0 s. Its overlay check above fails while the service rebuilds the
unrelated Brown dependency: the current source of `Sheaf.CategoryTheory.CompactObject`
is an empty withdrawn module, whereas `BrownHypotheses` still names `IsCompactObject`.
This source/cache inconsistency is outside the changed relative-Proj interface.

Delivery bookkeeping: the first delivery attempt refused this zero-hole repair with
`FAILED: nothing is proved` (the original-sorry list is empty). The queue still labels
the item a repair, but its row is absent from `coord/repairs.txt`. No tool or metadata
is patched. The final packet follows the supported withdrawal path of steps 8b/8d:
the obsolete module is explicitly withdrawn, its sole consumer is migrated, and the
source-library node and all mathematical dependencies are preserved.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
