## What changed

Repair of returned head `178863bcf98` (reviewer C-17886): the mathematical review
passed, but landing rejected a reviewer override named
`H1-lattice-cubical-local-instances.md`. The stage-3 landing tool indexes this
change record as `H1-lattice-cubical-local-instances.change.md` in its flat
`--apply-fixes` directory (`tools/batch_land.py`, function `fixes`). The repository
path remains `coord/changes/H1-lattice-cubical-local-instances.md`; it must not
be renamed to the flat override key. This packet includes the complete record,
so no override is needed for these repair notes. If the reviewer edits it, use
the `.change.md` override filename. No landing-tool change is proposed.

Compared the retained returned packet with current shared sources: the two new
Lean modules and two new nodes remain absent from main; the original item node
differs only in `lean` and `stmt_deps`. The source extraction and proof are
retained. Delivery regenerates the commit on freshly fetched `sheaf-dag`, keeping
current maintainer-owned node fields. The server compiler accepted the identical source set and its unchanged direct
importer from its cached successful compile: 32.6, 29.6, 29.8 and 46.4 seconds
respectively. The temporary unchanged importer copy was removed again.

Repair validation: `deliver3.py --no-push` passed server preflight on rebased
commit `93151f438d1`; no files were pushed by that dry run. The CODEX review
classification is retained for the existing module extraction and change record.

Proved `Profinite.DiscreteLattice.CubicalEvaluation.koszulZero` by chain-map and
finite-biproduct extensionality, using the prescribed entries in `KoszulModel.maps`.
Cancel both coordinate isomorphisms; every matrix entry of the zero map is zero.
This also handles empty coordinate sets outside the Koszul degree range.

The original combined file exceeded the 60-second limit. Profiling showed that
kernel conversion in the existing definitions dominated the new proof. Used the
canonical imported instances within sections, restored respectTransparency, made
two existing endomorphism function coercions explicit, and made three complex
functors ordinary definitions with identical bodies. One compile then passed in
59.3 seconds, but the required importer check recompiled it in 81 seconds. After
these improvements, extracted the existing declarations into two smaller modules:

- `Sheaf.CategoryTheory.LatticeCubicalEvaluationCore`: normalized discrete comparison,
  Koszul zero-map proof, totalization, cells, signs, and tensor augmentation.
- `Sheaf.CategoryTheory.LatticeCubicalEvaluationModel`: the existing CubicalModel,
  invariant complex and inclusion, and coordinate/evaluation maps.
- The item publicly reexports the model module and retains Evaluation, RankZero,
  and the main theorem. All existing public names and mathematical statements remain.

The change record is `coord/changes/H1-lattice-cubical-local-instances.md`.
The core, model and item compiled in 32.6, 29.6 and 29.8 seconds respectively.
The unchanged direct importer LatticeCubicalMultiplicationRoof compiled against
the delivery in 46.4 seconds. Its unchanged temporary copy was removed.

## Proved and sorry left

Closed one of the two original holes:
`Profinite.DiscreteLattice.CubicalEvaluation.koszulZero`, now in the core module
(node `lem-sfb-koszul-functor-preserves-zero`). This is a complete proof from the
coordinate characterization, without a postponed existence assertion.

One original hole remains unchanged:
`Profinite.DiscreteLattice.CubicalEvaluation.lattice_cubical_augmentation_evaluation`
(node `lem-sfb-lattice-cubical-augmentation-evaluation`). Its complete seven-step
natural-language proof and source remain in the docstring and DAG node.

Added zero holes and split off zero unproved statements. The two extracted modules
have no sorry. This is a partial proof delivery, not a proof of the main existence
assertion. No declaration is duplicated or withdrawn.

## No longer needed

None. No mathematical dependencies or imports were pruned. The original main
proof plan and unit route remain intact, including the cubical-resolution,
integral-contraction, tensor-comparison and restriction-calculus dependencies.
The added node edges record the ownership of extracted definitions, not a new
mathematical route. No module is proposed for withdrawal.

## Where the brief, the DAG or earlier work was wrong

The returned landing failure was a reviewer override filename mismatch, not a
Lean error or a missing sandbox change record. The flat landing fix key is given
above; the repository record path is unchanged.

No mathematical error found in the completed zero-map argument. Its coordinate
formula already gives every entry, so no additional exactness or tensor theorem
is needed for this hole. The original file required conversion improvements and
then a source split to compile reliably within the unchanged per-file limit.
The main theorem remains its original named statement.

## New nodes

`lem-sfb-koszul-functor-preserves-zero` records the existing auxiliary theorem,
now proved and moved to LatticeCubicalEvaluationCore, and the supporting existing
core declarations. Its matrix-entry proof is complete in Lean; no new obligation.

`def-sfb-lattice-cubical-model` records the existing CubicalModel data and coordinate
maps moved to LatticeCubicalEvaluationModel. It defines the same structure and
asserts no inhabitance. All fields retain their mathematical content.

The original node keeps its statement and seven proof steps. Its Lean declaration
list retains the declarations physically in the item; moved declarations are all
attached to the two new nodes. Its statement dependencies gain those two nodes.
The associated record is `coord/changes/H1-lattice-cubical-local-instances.md`.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
