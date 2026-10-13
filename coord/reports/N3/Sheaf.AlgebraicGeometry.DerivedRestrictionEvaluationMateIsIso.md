## What changed

The target theorem now reduces its `IsIso` conclusion to the Yoneda criterion and the
postcomposition bijectivity theorem. A new helper module states that strictly smaller
bijection claim; its proof is left for the next worker.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.derivedRestriction_evaluationMate_isIso` by
`isIso_of_yoneda_map_bijective`. The new declaration
`derivedRestriction_evaluationMate_postcomp_bijective` remains `sorry` and is recorded
by node `lem-sc-derived-restriction-evaluation-mate-postcomp-bijective`.

## No longer needed

The original module imports only `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom`
and the new helper. The K-flat and stalk modules listed in the original proof plan are
needed by the helper's intended proof but are not imported by this reduction.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated the full categorical calculation as one proof step. The
Yoneda reduction isolates the actual remaining mathematical content as a bijectivity
statement, which is strictly below the target and can be proved independently.

## New nodes

`lem-sc-derived-restriction-evaluation-mate-postcomp-bijective` records the helper
statement and its Stacks sources.

## Earlier second reading (a previous round; superseded)

The target proof is a direct Yoneda reduction; the helper is strictly a Hom-set bijectivity claim and is the only remaining hole.

## Second reading by N3

1. Compared the delivered target module with the repository version: the theorem signature is byte-for-byte unchanged; only its proof and a private import were added. The helper is a genuinely smaller Hom-set bijectivity statement. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds with no warnings. The target has no `sorry`; the helper has the single named `sorry` listed above, with no hollow definition, axiom, unsafe, opaque, extern, or implemented_by. Verdict: pass.
3. Checked the helper statement against its node and docstring: it preserves the exact objects, hypotheses, and displayed mate, and is strictly stronger in the useful intermediate direction without restating the target. Its Stacks source and proof plan are recorded. Verdict: pass.
4. The target uses the Yoneda reduction and the helper; the canonical tensor-Hom import remains public for the signature, while the helper import is private to the proof. The K-flat and stalk modules are not needed by this target proof and are named above. Verdict: pass.
5. The target node proof and `proof_deps` match the implemented Yoneda application, and the helper node records the remaining open proof. The Picard-duality unit route remains represented by the target and helper nodes. Verdict: pass.

Changed during second reading: no theorem statements or definitions; added this review record only.
