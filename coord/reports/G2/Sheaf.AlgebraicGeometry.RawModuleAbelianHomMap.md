## What changed

Completed the listed duplicate retirement of
Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap together with its four otherwise
unused duplicate formula consumers: RawModuleScalarHomEvaluation,
RawModuleScalarHomCompositeFormula, RawModuleAbelianHomSourceFormula and
RawModuleAbelianHomTargetFormula, all under Sheaf.AlgebraicGeometry.
All five paths are withdrawn through deleted.txt.

The item is already a reexport shim. Its definition node already points to the
canonical upstream construction and is preserved. The four formula nodes now
point to the existing fully proved declarations in their corresponding
WeilConjectures.AlgebraicGeometry modules, keeping the same declaration names.
Their proof records follow those canonical proofs; no statement, hypothesis,
mathematical node, incoming dependency, unit or chapter changes.

The old raw-class views return their inputs. The historical forget name and
native coefficient factor are abbreviations of the canonical data. The inverse
of the historical derived comparison is definitionally the canonical forward
comparison. Consequently the canonical equations have exactly the same meaning
as the retired presentations. No adopted source file changes.

Change record: coord/changes/G2-retire-raw-module-abelian-hom-map-shim.md.

## Proved and sorry left

The assigned retirement starts with 0 holes. Holes closed: 0 of 0. Holes added: 0.
Split off: 0. Sorries left in the five withdrawn modules: none. This is duplicate
retirement and canonical-proof reuse, not a proof-count gain.

The existing fully proved construction rawModuleAbelianHomMap and theorems
rawModuleScalarHom_evaluate, rawModuleScalar_hom_composite_formula,
rawModuleAbelianHomMap_source_formula and rawModuleAbelianHomMap_target_formula
remain in their canonical upstream modules. None of their proof bodies changes.

## No longer needed

Pruned modules (all Sheaf.AlgebraicGeometry): RawModuleAbelianHomMap,
RawModuleScalarHomEvaluation, RawModuleScalarHomCompositeFormula,
RawModuleAbelianHomSourceFormula and RawModuleAbelianHomTargetFormula.
All their imports disappear with the redundant copies. Their canonical
WeilConjectures implementations remain. No mathematical node is removed.

The native-view identity node def-sbc-raw-class-native-morphisms is no longer a
proof dependency of the four canonical formulas. It remains elsewhere as needed
and its existing statement citations are preserved. The composite proof no
longer uses the two-part lem-sbc-raw-scalar-pullback-formulas: it directly uses
lem-sbc-raw-scalar-pullback-module-formula, the same module equation from that
conjunction, as the existing canonical proof does. No global withdrawal of
these two dependencies is claimed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a repeatedly split proof obligation. The current
assignment is a listed duplicate retirement with zero holes. P2's reviewed
migration has already moved the construction upstream. All four remaining
Sheaf importers are duplicate formula modules with their own listed upstream
twins and no external live or quarantined importer. All four are unclaimed.

The direct-import-only packet compiled its header in 9.7 seconds but exposed
slow concrete raw-class equation checks. A low-heartbeat profiler localized the
failure to kernel checking rawModuleScalarHom_evaluate (6.95 seconds before the
intentional diagnostic heartbeat bound); proof elaboration took 299 ms. The
actual issue is repeated definitional comparison of native-view endpoints and
derived scalar forgetting. The existing upstream proof has the same mathematical
formula without those duplicate presentation wrappers. Reusing the canonical
chain removes those equation checks without splitting a proof or file for speed.

The library, quarantine and rework audits found no external import of the
five-module chain. All 56 present quarantine archives were checked. All ten
mathematical parents of the definition node retain that construction. Four node
attachments are migrated rather than detached, and their incoming dependencies
are preserved. This is actual replacement by the existing canonical argument,
not a withdrawal inferred only from zero Lean importers.

Searches were run through msearch.py using LeanFinder, Loogle and grep, with
additional direct rg searches of both library roots. LeanFinder returned generic
sheaf-module and free-sheaf constructions; Loogle found AddCommGrpCat.ofHom and
its evaluation/composition API. Direct source search found the exact canonical
construction and all four existing formula proofs. No new lemma is needed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
