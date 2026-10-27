## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.podGeneralCtfAdjunctions in
Sheaf.Paper.PodCtfAdjunctions, preserving its exact statement. Two proved private
helpers construct the fully faithful restriction and establish precisely the
ambient Hom-bijection compatibility equation. The first clause restricts the
ordinary derived adjunction using the preservation theorem. The second uses
the signed tensor interchange and actual tensor/internal-Hom preservation.
The third constructs the small functors at the specified compactification,
transports its ambient adjunction to each boundary compactification by the
canonical coherence comparison, and proves compatibility by the same helper.

Restored the absent existing proof dependency
Sheaf.Paper.DetThmSfCtfStabilityInternalHom, retaining its complete recorded
statement, all auxiliary definitions, and original node. Its theorem is a named
whole-proof sorry, with the twelve-step proof from its existing DAG in the
docstring. This reuses an already stated node rather than adding a new statement.
The restored explicit constructions choose no data from existence proofs.

Added private proof imports for CtfStabilityDirectImages, the restored Hom
module, CompactificationCoherenceCocycle, and QuasiSeparated. Updated the item
node's proof text to match the implemented proof, retaining its dependencies.
The restored node's Lean statement records the formatted full signature.
Change record: coord/changes/H1-restore-ctf-internal-hom-dependency.md.

Validation: lcompile --all accepted both modules. The initial all-module run
reported 55.8 s and 75.7 s; a diagnostic profile of the item then compiled in
20.7 s, with about 4.55 s tactics, 2.41 s kernel checking, and 2.93 s linting.
No slow declaration was identified; the diagnostic option is removed. The
final all-module run after removing the unused dependency import accepted both
modules (54.0 s and 78.9 s). The standalone final source/compiled-signature
compatibility check and delivery checks are recorded by the delivery tool.

## Proved and sorry left

Closed one of the two original holes:
AlgebraicGeometry.ProEtale.CondensedRing.podGeneralCtfAdjunctions
(node det-thm-sf-ctf-stability-adjunctions).

One original hole remains unchanged:
WeilConjectures.podCtfAdjunctions_exists
(node det-thm-sf-ctf-stability-adjunctions, secondary declaration).
Its four-stage closed-presentation existence assertion is distinct from the
original general admissible-coefficient theorem proved here.

Restored one hole outside the item, on its already existing node:
AlgebraicGeometry.ProEtale.CondensedRing.internalHom_stability
(node det-thm-sf-ctf-stability-internal-hom). No new nodes or new mathematical
statements were added. The general theorem is completely proved from its
recorded named dependencies; restoring the needed dependency adds one textual
hole. Thus this delivery closes one upper hole and restores one lower hole,
for net zero textual holes, and is a dependency reduction, not a claim of a
sorry-free target proof. There are two textual holes in the delivered modules
in all, and none inside definitions or partial proofs.

## No longer needed

No existing public import is removed: they form the existing public interface.
No planned proof dependency is pruned. All six recorded proof dependencies are
used: direct-image preservation, ambient push-pull adjunction, ambient tensor-Hom,
internal-Hom stability, localizing exceptional existence, and compactification
coherence. No module is withdrawn. The restored Hom module imports the lower
shriek definitions directly, without the unused tensor-projection theorem module.

## Where the brief, the DAG or earlier work was wrong

The DAG's internal-Hom attachment refers to a module absent from lean/. Its note
says it was deleted as dead on 2026-10-20. The unfinished parent still lists that
node as a proof dependency. Restoring it is necessary for the supplied proof
plan; its absence is not evidence that the mathematics is unnecessary. There
is no quarantine/rework row for either item or restored module.

The compiled compactification_coherence_cocycle currently accepts the arguments
Λ, ℓ, admissibility, f; the source version additionally shows an explicit ground
field argument. The proof's `first` tries the current source signature, then the
published compiled signature; either branch uses exactly this same coherence
theorem. This keeps the delivery compatible with both the current compiled
snapshot and the next source build under the item's original hypotheses. No source-library declaration is changed.

Edge checks: the categorical helpers require no objects and hence include empty
categories; tensor restriction allows K=0; identity and proper morphisms use the
same adjunction formulas. The compactification comparison does not assume a
dense chosen compactification. The restored internal-Hom statement retains
arbitrary characteristic-p ground fields and all admissible coefficients,
allows empty schemes and zero objects, and does not add site-perfectness to
K or L. Its perfectness condition applies only to the displayed generators.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
