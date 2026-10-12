## What changed

Replaced the proposed clause split with an actual proof of
`AlgebraicGeometry.limit_fibre_products_of_affine_transition` in its original module.
The existing signature is byte-for-byte unchanged. A local, fully proved pullback
construction is applied first to X, S, T and then to the residue-field spectra.
The cone point is the exact chosen pullback; the stage objects and projections
have the exact equalities/HEq required by the original theorem.

The categorical part uses Mathlib's `PullbackCone.combine` and the universal
properties of the three supplied limiting cones and the pullback, rather than the
unproved categorical comparison. Affineness uses the existing
`AlgebraicGeometry.isAffineHom_pullback_map`. The fibre specialization uses the
existing `AlgebraicGeometry.exists_isColimit_residueField_of_isLimit`, including
its canonical transition and cone-map identities. `Functor.copyObj` and cone
transport put those spectra on the exact specified objects.

Removed the proposed Part1/Part2 modules and nodes. Added one plain proof import
of `Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks`, made
LimitResidueField a plain proof import, and removed the unused direct
LimitAffineTransition and FibreProductLimit imports. Updated the original
proof docstring and the item's `proof`/`proof_deps` to describe the actual route.
The import-visibility change is recorded in
`coord/changes/LimitFibreProducts-imports.md`.

## Proved and sorry left

Hole closed (one): `AlgebraicGeometry.limit_fibre_products_of_affine_transition`
(node `lem-weil-pbc-limit-fibre-products`). No `sorry` remains in the delivered
module. Holes added: none. New split-off statements: none. This is a genuine
reduction to existing dependencies, not the initially proposed decomposition
of one hole into two new holes.

The proof still depends on the pre-existing open declarations
`AlgebraicGeometry.isAffineHom_pullback_map`
(node `lem-weil-pbc-fibre-product-affine-transition`) and
`AlgebraicGeometry.exists_isColimit_residueField_of_isLimit`
(node `lem-weil-pbc-limit-residue-field`). They are not altered or delivered here.
`#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`; the delivery is not claimed to be transitively axiom-free.
The ledger, not these local hole counts, determines target-closure progress.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.FibreProductLimit`: its only public declaration
`AlgebraicGeometry.Scheme.isIso_limit_pullback_comparison` and its DAG node
`lem-kun-fibre-product-limits` are not used. The explicit universal-property
argument replaces this dependency. The repository's only import of that module
was in this item, so removing it prunes that branch of the import graph.

Removed the direct `Sheaf.AlgebraicGeometry.LimitAffineTransition` import:
`exists_limit_affine_transition` is not needed because limiting cones are
supplied as hypotheses. This module remains transitively imported by
LimitResidueField and is not claimed globally pruned.

LimitResidueField remains necessary, but only as a plain proof import.
The affine-transition dependency remains necessary. Of the old `proof_deps`,
only `lem-kun-fibre-product-limits` is removed; the residue-field and affine-map
nodes remain. `def-pc-fibre-product` now records the elementary universal-property
argument. No node in any `dag/units/*.json` realization is bypassed.

The proposed, never-landed Part1 and Part2 modules and nodes are removed from the
sandbox delivery entirely; no new module or node remains.

## Where the brief, the DAG or earlier work was wrong

The first worker merely extracted the theorem's two conclusion clauses into
new theorems with `sorry`. Their node proof dependencies cited their parent,
creating a cycle if the parent were updated to match the proposed proof.
Their node statements were titles instead of self-contained statements,
`lean.statement` was not the Lean signature, search records were absent, and
the docstrings did not give complete proofs. Part1 also emitted a long-line
warning. The original report described this as a real decomposition while
leaving the parent's DAG route unchanged.

The original parent's general categorical comparison was unnecessary: a direct
universal-property proof works for the supplied cones and gives the exact
chosen representative, avoiding comparison-isomorphism transport. The supplied
residue-field theorem already gives every canonical map needed for the fibre
specialization, so no new helper statement is needed.

## Second reading by S1

1. **Visible statements and definitions.** Compared the delivered module with
   the repository using `diff` and an exact signature extraction. The complete
   existing theorem signature is byte-for-byte unchanged, including all three
   affine-transition instances, all cones and limiting proofs, F/G and their
   compatibility hypotheses, and both conclusion clauses. There are no new
   public declarations or definitions. The only visible change is import
   pruning/visibility, with `coord/changes/LimitFibreProducts-imports.md`.
   The sole direct importer, ProperFibreIdempotentImage (held by P3), compiles
   from an unchanged scratch copy against the newly compiled item; no forced
   adaptation is required. Verdict: pass after the recorded import repair.

2. **Actual proof and axioms.** Initially all three proposed modules compiled,
   but Part1 emitted a long-line warning and both component theorems had sorry.
   The final item compiles cleanly through lcompile.py (about five seconds),
   contains no sorry or forbidden declaration mechanism, and its scratch
   `#print axioms` gives exactly the allowed three axioms plus existing sorryAx.
   The pointwise pullback data and cone are constructed explicitly. Data from
   the residue-field theorem is determined by its object equalities and HEq
   identities for every transition and projection; no arbitrary existence
   witness is used as new definition data. Verdict: pass; existing upstream
   proof holes remain explicitly reported.

3. **Split-off statements and searches.** Rejected and removed both proposed
   split-off nodes; none remains to certify. Independently searched the library
   and upstream sources for limit/pullback and fibre/limit declarations, and
   used msearch.py LeanFinder with the query about limiting cones of pointwise
   pullbacks, plus grep for PullbackCone.combine/copyObj/isoCopyObj. This found
   the exact Mathlib constructions used by the repair. The local hpb is proved,
   not a hidden new hole. For edge cases, the cone argument works for a singleton
   index with identity maps and for empty schemes; the point specialization is
   vacuous when the limiting base has no points. No hypothesis is added to
   exclude these cases. Verdict: original split refused; repaired proof passes.

4. **Top-down proof, pruning and unit route.** Read the original planned
   categorical, affine-transition and residue-field steps and the declarations
   they name. The categorical universal property is proved directly; the two
   geometric dependencies are applied with precisely their stated hypotheses.
   The source's fibre specialization is retained: residue spectra first,
   pullbacks second. Read the unit sk-thm-p1 realized record and searched every
   unit record for this item and lem-kun-fibre-product-limits; neither is a unit
   realization. Therefore the removed comparison helper is below the unit
   level. No longer needed lists every old proof dependency dropped, and
   distinguishes removing a direct import from globally pruning a module.
   Read the source's limit argument in [Stacks 0G7X](https://stacks.math.columbia.edu/tag/0G7X),
   the general commutation principle in [002M](https://stacks.math.columbia.edu/tag/002M),
   and the residue-field clause in [0CUG](https://stacks.math.columbia.edu/tag/0CUG).
   The source files are absent locally, so their official tag pages were used.
   Verdict: pass.

5. **Nodes against Lean.** The only delivered node is the existing item.
   Its statement, stmt_deps, lean record, chapter, unit and realization data
   remain unchanged. Changed only proof and proof_deps: the first step spells
   out the lift/factorization/uniqueness argument using def-pc-fibre-product;
   the second uses isAffineHom_pullback_map; the third transports the exact
   residue-field spectra and applies the proved local pullback construction.
   Checked that proof_deps is exactly the union of step uses. No cyclic new
   node survives. Verdict: pass.

Second-reading changes: removed the invalid clause split and both new nodes;
wrote the actual pullback and fibre reduction; pruned the categorical comparison;
repaired proof-only import visibility; updated the DAG route, proof explanation,
report and import-change record. No theorem statement was changed.
