## What changed

Proved the target without changing its signature. For each point, construct an integral
pushforward detector, factor its map through a finite pushforward, and transport stalk
injectivity through the factorization. Classical choice assembles the indexed families.

Two new, fully proved supporting modules supply the general-ring integral detector and
finite-stage factorization. The integral proof adapts the existing finite-coefficient argument:
constructibility over a field gives a locally constant trivialization; an etale residue field
provides a finite separable extension; finite generation of the constant value follows from
its geometric stalk. Normalization, the normal generic-point unit, adjunction and the stalk
comparison then construct the detector. The factorization proof reuses the affine-presentation
argument from the source library. Importing that source module directly would create a cycle,
since it now imports this target, so the necessary private helpers are reproduced here.

## Proved and sorry left

Closed the original hole:

- `AlgebraicGeometry.Etale.exists_noetherian_stalk_detector`.

Also proved both new supporting theorems:

- `AlgebraicGeometry.Etale.exists_integral_lowerStar_stalk_injective_noetherian`.
- `AlgebraicGeometry.Etale.exists_finite_lowerStar_factorization_noetherian`.

No `sorry` remains in any delivery module; no new hole is added. Existing imported project
lemmas remain dependencies of the argument. All three modules compile together through
`lcompile.py --all`.

## No longer needed

No existing DAG node or module is pruned. Removed the redundant target proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; its API is already supplied by the
public constructibility import.
The general-ring proof does not import the finite-coefficient detector or its generic-data
modules. Redundant proof imports removed from the new supporting modules are:

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`.
- `Mathlib.CategoryTheory.Presentable.Finite`.

## Second reading by Q1

1. I compared the delivered target module with the repository version. The target theorem
   signature is byte-for-byte unchanged; the only target change is its proof and its proof-only
   imports. The two new supporting modules and their declarations are recorded by the two new
   DAG nodes, and the node proof and dependency lists follow the imports and theorem applications.
   Verdict: pass.

2. I compiled all three delivery modules with `lcompile.py --all` and compiled the target alone.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or
   `debug.skipKernelTC` declarations. The supporting declarations are constructive proofs using
   only the permitted classical categorical infrastructure. Verdict: pass.

3. The two split-off statements are strict reductions of the target: the first supplies one
   integral detector at a fixed point, and the second factors that detector through one finite
   stage while retaining the transition map. Neither restates the target, and both are stronger
   intermediate data needed by the final choice argument. Their statements match their Lean
   declarations and their docstrings give the source and proof route. Verdict: pass.

4. I checked the proof from the target downward. It uses the integral detector, finite-stage
   factorization, and the stalk composition argument; the unit route and its realized nodes are
   retained. The finite-coefficient detector and generic-data modules are not needed. The
   removed imports listed above are proof-only redundancies. Verdict: pass.

5. I checked the DAG records for the target and both new nodes. Their Lean module paths,
   declarations, statements, source, proof steps, proof dependencies, origin, unit, and chapter
   agree with the delivered files. No definition or existing interface was changed. Verdict:
   pass.

I changed only this report section after the first delivery dry run, adding the required second
reading record; no Lean proof or node content was changed.

## Where the brief, the DAG or earlier work was wrong

The existing finite-coefficient detector requires `Finite Λ`, which does not follow from
`IsNoetherianRing Λ`. Its argument nevertheless generalizes: replace finite cardinality of
its constant value by finite generation, obtained using the general constructibility API and
constant geometric-stalk comparison. No definition or existing statement was changed.

## New nodes

`new-lem-weil-pbc-noetherian-integral-stalk-embedding` records the fully proved general-ring
integral detector. Its dependencies are immersion independence, normalization in a finite
residue-field extension, and the normal generic-point constant-sheaf unit.

`new-lem-weil-pbc-noetherian-integral-map-factorization` records the fully proved finite-stage
factorization. Its dependencies are general affine presentations, affine etale sections and
filtered colimits, integral finite approximation, and the constant-module pushforward colimit.
