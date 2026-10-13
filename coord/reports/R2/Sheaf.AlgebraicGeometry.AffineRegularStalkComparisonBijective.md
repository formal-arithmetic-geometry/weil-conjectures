## What changed

Proved `AlgebraicGeometry.Scheme.affineRegularStalkComparison_bijective` with its
signature and existing docstring unchanged. Added the proof-only import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` for the canonical map
from the unit module to the direct image of the restricted unit module.

The proof follows the existing node's route. On opens V contained in U, the
second projection from U times V is an isomorphism. Its section maps are
bijective. A proved private germ calculation passes this bijectivity to the
stalk at x, using representatives and equality witnesses inside U. A second
private helper identifies the unit module's stalk linearly with the stalk
ring; its proof is reused from the proved private helper of the same name in
`Sheaf.AlgebraicGeometry.IdealModuleProductStalk`. Finally, transport through
the stalk of `affineRegularSheafIso` identifies the given comparison with
the composite of these bijections. No additional affine localization theorem
or unit-preservation claim about the individual factors of that iso is needed.

Single-file compilation passed. The proof uses the explicit construction of
`affineRegularStalkGerm`; it does not select data from an unproved existence
statement. Empty U is excluded by hxU, and the argument also applies when U
is the whole space. The unit's route and the existing DAG dependencies are kept.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affineRegularStalkComparison_bijective`
(node `lem-sc-affine-regular-stalk-comparison-bijective`).

There are no sorries left in the delivered module, no new holes, and no split-off
theorems. Both private helpers have complete proofs. This is a proof, not a
decomposition.

## No longer needed

No existing imports or DAG dependencies were removed. The proof does not import
`Sheaf.AlgebraicGeometry.IdealModuleProductStalk`; only its proved private unit
stalk calculation is reused locally. No existing nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was wrong. The existing plan's assertion that each
factor of the regular sheaf isomorphism preserves the unit is unnecessary:
the unit germ is defined using the inverse of the whole isomorphism, so the
inverse-hom identity proves its needed transport formula directly. This
simplification keeps the stated proof route and dependencies unchanged.

## Second reading by R2

1. Compared the delivered module with the repository version. The theorem
   signature, declaration visibility, and docstring are byte-for-byte
   unchanged; the only module change is the proof-only Mathlib import and the
   proof body. Verdict: pass.
2. Compiled the module with `lcompile.py`; it has no `sorry`, `axiom`, `unsafe`,
   `opaque`, `implemented_by`, or `extern`. A scratch `#print axioms` reports
   only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the existing node and its proof dependencies against the proof.
   No split-off statements or new nodes were added, and the unit route is
   preserved. Verdict: pass.
4. Reviewed the proof for a shorter available route and import scope. The
   direct-image stalk bijection and explicit unit-stalk linear isomorphism are
   proved constructively; the added import is proof-only and no existing import
   or dependency can be pruned. Verdict: pass.
5. Checked edge cases and statement strength: `hxU` rules out empty `U`, and
   the argument includes `U = univ`; no hypotheses or conclusions changed.
   Verdict: pass.

Changed only the report by recording this review; no Lean or DAG repairs were
needed.
