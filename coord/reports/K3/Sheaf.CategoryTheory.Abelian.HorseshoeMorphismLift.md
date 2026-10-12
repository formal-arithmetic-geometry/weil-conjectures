## What changed

Closed `CategoryTheory.InjectiveResolution.horseshoe_preliminary_data`, the module's
only remaining hole. All original declaration signatures are unchanged.

Added three proved intermediate modules:

- `Sheaf.CategoryTheory.Abelian.HorseshoeDegreewiseMap`: constructs the degreewise
  middle family by Mathlib's injective splittings and proves its two outer squares.
- `Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization`: factors the differential
  and augmentation defects through the outer rows, then proves their signed cocycle
  and augmentation compatibility identities by cancellation.
- `Sheaf.CategoryTheory.Abelian.HorseshoeHomotopyCorrection`: implements the inductive
  injective-extension proof of the signed primitive and checks that the correction
  kills both defects.

The original module imports the degreewise and homotopy-correction modules privately,
constructs the corrected chain map via `CochainComplex.ofHom`, checks both outer squares
using the zero composites, and uses that map as chi and zero as q. The factorization
module is imported privately by the correction module. `Mathlib.Tactic.Abel` is a private
proof import of that module and is used in the final additive cancellation.

All four files compile without warnings through `lcompile.py --all`. The dependent
recurrence retains both consecutive primitive components, so its consistency and
successor equations are checked by Lean, including the degree-zero augmentation case.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.InjectiveResolution.horseshoe_preliminary_data`
(node `lem-weil-pbc-horseshoe-preliminary-data`).

The three new public theorems are fully proved:
`CategoryTheory.InjectiveResolution.horseshoe_degreewise_map`,
`CategoryTheory.InjectiveResolution.horseshoe_defect_factorization`, and
`CategoryTheory.InjectiveResolution.horseshoe_homotopy_correction`.
The private helpers `factor_through_rows` and `signed_primitive` are fully proved.
The already-proved `corrected_middle_map` and `exists_horseshoe_morphism_lift` remain proved.

No sorry remains in the item or any added module. No holes were added: this is a proof,
not a decomposition into unproved statements.

## No longer needed

No existing import was removed. Every delivered proof import is used.

`lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` is no longer needed as a proof
dependency of this item's branch: the specialized signed primitive is proved directly
by injective extension, using Mathlib's `exact₀`, `exact_succ`, and `descToInjective`.
No integer-indexed extension, shift, mapping cone, or K-injective module is imported.
This does not claim that other branches using that node can be pruned.

The injective-kernel splitting leaf stays needed through the degreewise-map node.
The unit's own statement and realized steps are preserved; this change is below them.

## Where the brief, the DAG or earlier work was wrong

The earlier preliminary-data statement already asks chi and q to be chain maps; the
raw map in the original planned first step is only a degreewise family. The proof now
keeps that family unbundled until its defects have been corrected. No statement change
is needed: the corrected map together with q = 0 supplies the existing conclusion.

The original morphism-lift DAG Step 2 wrote a minus-sign differential identity for D
where the signed cocycle calculation requires the plus-sign identity. The delivered
factorization proof computes the signs explicitly and proves the correct cocycle
identity. The existing parent node now records the actual preliminary-data/correction
combination rather than that erroneous prose calculation.

The repository's referenced Stacks TeX files are absent on this machine. The cited
ingredients were read at the official pages for Tags
[0136](https://stacks.math.columbia.edu/tag/0136),
[013R](https://stacks.math.columbia.edu/tag/013R), and
[013T](https://stacks.math.columbia.edu/tag/013T).
Weibel remains listed as wanted in `literature/LIST.md`. The diagram chase is marked
as agent-written, following the existing node's explicit argument; the primitive
recurrence follows the injective-extension induction of Tag 013R.
LeanSearch returned Internal Server Error; this is recorded as unavailable, with no
fabricated verdict. LeanFinder, Loogle, and source grep supplied the checked APIs.

## New nodes

`lem-weil-pbc-horseshoe-degreewise-map` records the fully proved splitting construction
in `HorseshoeDegreewiseMap.lean`; its sole substantive dependency is the existing
injective-kernel splitting leaf.

`lem-weil-pbc-horseshoe-defect-factorization` records the fully proved row factorizations
and their two compatibility identities in `HorseshoeDefectFactorization.lean`.
It uses abelian exactness and elementary cancellation; it has no unresolved dependency.

`lem-weil-pbc-horseshoe-homotopy-correction` records the fully proved signed primitive
recurrence and cancellation in `HorseshoeHomotopyCorrection.lean`. Its proof depends
on the defect-factorization node and the Mathlib injective-resolution primitives.

Updated the proof, proof_deps, and proof_origin of the existing preliminary-data and
morphism-lift nodes to match the compiled argument. No change record is needed because
no existing statement or definition was changed.

## Second reading by K3

1. I compared the delivered `HorseshoeMorphismLift.lean` with the repository version.
All existing declaration signatures, including `corrected_middle_map` and
`exists_horseshoe_morphism_lift`, are byte-for-byte unchanged; the only changed body is
the proof of `horseshoe_preliminary_data`, with the stated private imports added for it.
Verdict: pass.

2. I compiled all four delivered modules with `lcompile.py --all`. The compilation is
clean and the files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`. The new declarations are proved by ordinary category-theoretic
calculations and injective-extension induction; the original target hole is closed.
Verdict: pass.

3. I checked each new theorem against its node and its docstring. The degreewise map,
defect factorization, and homotopy correction statements are true intermediate results,
strictly simpler than the target, and are needed by the target proof. They do not repeat
the target statement, and no existing library declaration duplicates them. Verdict: pass.

4. The proof follows the shortest available route below the unit: Mathlib splittings,
explicit factorization, and direct injective extension. The old acyclic-nullhomotopy
dependency is no longer used. Public imports are limited to the resolution API; the
additional factorization and `Mathlib.Tactic.Abel` imports are private proof imports.
Verdict: pass.

5. The DAG proof steps, dependencies, origins, and new node records match the Lean
proofs. The preliminary-data and morphism-lift nodes retain the unit route through the
same final correction construction, while recording the actual lower-level steps.
Verdict: pass.

I changed only the proof bodies, added the three required intermediate modules and node
records, updated the corresponding proof metadata, and added this second-reading report.
