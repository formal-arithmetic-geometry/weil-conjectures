## What changed

Completed `AlgebraicGeometry.quasi_coherent_algebra_affine_inclusion` in its original module
with its entire signature unchanged. The ring pushout is derived from the existing
`Scheme.Modules.quasiCoherent_affine_section_baseChange` theorem: the tensor-product ring
comparison agrees with its bijective linear comparison by tensor induction. Transporting
the ring pushout through Spec and the canonical affine charts gives the cartesian square;
base change gives the open immersion and Mathlib gives the range/preimage equality.
Functoriality and identity follow directly from functor laws.

Added only the proof import `Mathlib.AlgebraicGeometry.PullbackCarrier`. All original public
imports and the existing affine section base-change proof import are retained. Updated the
original DAG node's proof and proof origin to record the actual Lean argument.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.quasi_coherent_algebra_affine_inclusion`
(`lem-weil-pbc-quasi-coherent-algebra-affine-inclusion`).

No sorry remains in the delivered module. No new sorry, statement, definition or axiom
is added. The proof still depends on the existing sorry-bearing theorem
`AlgebraicGeometry.Scheme.Modules.quasiCoherent_affine_section_baseChange`
(`lem-weil-pbc-quasi-coherent-affine-section-base-change`); proving that theorem is a
separate stage-3 item, as intended by the brief.

## No longer needed

Removed all three intermediate modules and corresponding new nodes from the earlier
sandbox attempt, together with their imports:

- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusionPushout`,
  `new-qc-algebra-affine-inclusion-pushout`;
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusionGeometry`,
  `new-qc-algebra-affine-inclusion-geometry`;
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusionFunctoriality`,
  `new-qc-algebra-affine-inclusion-functoriality`.

Their arguments are fully proved inline, so none of those proposed new items needs landing
or further work. No original DAG dependency is pruned: the affine module base-change
statement and both Mathlib geometry leaves retain their roles. The unit's realized
statement and steps are preserved; this node is below that level.

## Where the brief, the DAG or earlier work was wrong

The earlier report incorrectly listed the already compiled geometry and functoriality
proofs as remaining sorries and had duplicated and superseded report sections. Its
three-way split is now unnecessary: the ring pushout also follows from the stated
module base-change theorem without introducing any new obligation. The brief and the
original DAG's mathematical route needed no correction. No statement was changed.

## Second reading by V1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and a proof-only import were added. Verdict: pass.
2. Compiled the module locally with `lcompile.py`; it succeeds with no errors, and the module contains no `sorry`, axiom, unsafe, opaque, implemented_by, or extern declarations. Verdict: pass.
3. Checked the proof against the existing DAG dependencies and searched the library/Mathlib for duplicate declarations. No new statements or split-off nodes were added, and the proof uses the existing affine section base-change theorem plus the two stated geometry dependencies. Verdict: pass.
4. Read the proof top-down. The tensor comparison is proved by TensorProduct induction, then transported through `CommRingCat.isPushout_tensorProduct`; the pullback, open immersion, range equality, functoriality, and identity are discharged directly. The added `Mathlib.AlgebraicGeometry.PullbackCarrier` import is used by the proof. No original dependency is pruned and the unit route remains intact. Verdict: pass.
5. Compared the sandbox DAG node with the proof. Its statement, proof steps, proof dependencies, and proof origin match the Lean argument; no statement change is present. Verdict: pass.

Changed only this report by recording the second reading. No code repair was needed.
