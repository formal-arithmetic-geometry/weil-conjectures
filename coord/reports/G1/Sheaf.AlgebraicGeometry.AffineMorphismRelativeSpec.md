## What changed

Proved the canonical quasi-coherence clause and constructed the affine structure-algebra
functor. Added proof modules for full faithfulness, affine realization of quasi-coherent
algebras, and the remaining chart compatibility clause. The main theorem now combines these
results with the affine-open, restriction, and pullback APIs.

## Proved and sorry left

`affine_morphism_relative_spec` is proved. The remaining named intermediate theorems are:

- `affine_structure_algebra_full_faithful` (`lem-weil-pbc-affine-structure-algebra-fully-faithful`);
- `exists_affine_structure_algebra` (`lem-weil-pbc-relative-spectrum-affine-realization`);
- `relative_spec_morphism_chart` (`lem-weil-pbc-relative-spec-morphism-chart`).

Each is a strict part of the construction or its local chart argument and is left as a
named theorem for the next worker.

## No longer needed

The proof does not import `Sheaf.AlgebraicGeometry.Coherent`; the direct pushforward result
and the module-theoretic quasi-coherence API suffice. The original direct imports of the
quasi-coherent affine-inclusion and qcqs pushforward modules are replaced by the intermediate
proof modules, which expose only the needed interfaces.

## Where the brief, the DAG or earlier work was wrong

The blueprint describes a complete relative-spectrum construction but Mathlib provides only
relative gluing and the absolute affine Spec equivalence. The missing gluing and counit
arguments therefore remain explicit intermediate theorem nodes.

## New nodes

`lem-weil-pbc-affine-structure-algebra-fully-faithful`,
`lem-weil-pbc-relative-spectrum-affine-realization`, and
`lem-weil-pbc-relative-spec-morphism-chart` are new strict subarguments. Their modules and
DAG records are included in this delivery.

## Earlier second reading (a previous round; superseded)

The second reader should verify the three strict intermediate statements and the unchanged target signature.

## Second reading by G1

1. Compared the delivered main module with the repository version. The target theorem and all
existing declaration signatures are unchanged; only proof code and proof-only imports changed.
Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds. The only
remaining `sorry`s are the three named split-off theorems, each with a matching DAG node and
source/docstring. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. Read the three split-off statements and checked their edge cases and dependencies. Full
faithfulness, affine realization, and chart compatibility are strict subarguments of the target,
with no weakened hypotheses or conclusions and no duplicate existing declarations found. Verdict:
pass.
4. Checked the proof route against the DAG and unit route. The main proof uses the three
intermediate declarations, and the DAG `proof`/`proof_deps` records match those uses. Removed
imports are recorded above; the unit realization remains intact. Verdict: pass.
5. Checked the delivered files and node records for agreement, including module/declaration names,
proof origins, and split status. Verdict: pass.

Changed nothing during this second reading; the delivery is ready for the stage-3 dry run.
