## What changed

Restore Sheaf.Paper.PurityConventions from its rework archive. Replace the three broad
imports that reach SfP1ProjectionTraceFalseTail with existing finite coefficient modules;
retain the other existing convention reexports. Migrate the retired torsor theorem import to its
identical source-library provider, used privately in the torsor proof. Explicitly import
the finite coefficient instance required by public data.
All existing signatures and definition formulas are preserved.

Fill roots restriction by kernel preservation, the arithmetic annihilator and invertibility
proofs, and the torsor class proof from existing declarations. The DAG attachment and the unit route are retained.

Validation: the revised module compiled cleanly with lcompile.py in 48.5 seconds.
The direct-consumer checks found no type errors. Fifteen completed below 60 seconds; three
large unclaimed consumers exceeded the server timing limit (68.1, 67.0, and 64.4 seconds in
the initial runs). Their temporary copies and debug settings are not part of this delivery; no
consumer signature or body was changed.

Change record: coord/changes/E7-purity-conventions-finite-dependencies.md.

## Proved and sorry left

Original holes: 11. Closed: 4. Added: 0. No split-off statements.

Closed declarations, in namespace WeilConjectures.PurityConventions:

- rootRestriction_existsUnique: the right-adjoint comparison functor preserves the root kernel.
- coefficientPower_isUnit: extract the unit ell from the unit ell^n (n>0), then take its power.
- defaultAnnihilator: the existing diagonal annihilator at level n, using (n-1)+1=n.
- kummer_torsor: coefficient functoriality of classH1 and the lifting-torsor boundary identity.

Remaining existing named holes, all attached to sk-def-purity-conv:

- coefficientComparison_existsUnique
- finiteLinePullback_existsUnique
- kummer_baseChange
- finiteLineTransition_existsUnique
- kummer_exponent_independent
- rootTorsor_represented
- regularNormalBundle

## No longer needed

Removed archived imports:

- Sheaf.Paper.ProEtaleTateTwists
- Sheaf.Paper.PurityFiniteKummerLevel
- Sheaf.Paper.PbcCoefficientTwists
- Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality

The finite-line data come from TateTwistFiniteLocallyFree; PurityNormalBundle still supplies
the normal-cone convention. FixedFinitePositiveCoefficientTwist supplies the annihilator.
The torsor theorem is retained through the identical source-library provider. No mathematical
DAG dependency is withdrawn, no parent proof is bypassed and no module is deleted. In particular,
this restoration preserves the quarantined node's attachment and all statement dependencies.
The aggregate integral/rational twists, finite Kummer comparison proof and PbcCoefficientTwists
are not used by this module's definitions or completed proofs. They may remain needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

The archived import of the retired Sheaf torsor duplicate was stale; the J5 change record
specifies its identical source-library replacement. The quarantine reason was a transitive
import of SfP1ProjectionTraceFalseTail through the three aggregate imports, not a missing or
withdrawn purity convention. No false theorem is applied. No target statement changes.
The existing regularNormalBundle theorem is more general than PurityNormalBundle.regular_spec
(which requires finite-type field hypotheses), so that theorem is not a direct solution.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
