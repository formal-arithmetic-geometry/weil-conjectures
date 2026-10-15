# Target migration, 2026-10-14

The human decided on 2026-10-12 to follow the corrected upstream statements. This sync
adopts `slopmaster2` commit `2104a988ee9fbee4de847237b493e3bd361d4ebb`, including PR 1413
(`46dc75fcf`) and its reviewer fix (`84babb37e`). `isIso_baseChange_of_isProper` is the
bounded-below abelian-sheaf statement with torsion cohomology, Stacks 0DDE;
`isIso_baseChange_of_isProper_of_isAddTorsion_ring` is the torsion-ring form, and
`isIso_baseChange_of_isProper_of_torsionHomology` retains the former module statement.

## Targets selected from the upstream structure

1. `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` — `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`; node `lemma-weil-pbc-p1-exchange-geometric-stalk`.
2. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`; node `prop-weil-pbc-algebraically-closed-extension`.
3. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`; node `lemma-weil-pbc-curve-separably-closed-passage`.

4. `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject` — `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`; node `lem-weil-pbc-cohomology-filtered-colimit`.
5. `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit` — `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity`; node `lem-weil-pbc-etale-section-continuity`.
6. `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing` — `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`; node `thm-weil-pbc-henselian-idempotent-lifting`.

These keep the upstream geometric-stalk and field-extension proof boundaries. The reduction
is now proved in `BaseChangeTheorems.Reduction`; injective acyclicity for arbitrary module
coefficients is now deduced from prime quotient coefficients in `BaseChangeTheorems.Coefficients`.
Both former targets leave Challenge. The two duplicated property definitions also leave
Challenge; only upstream defines each notion. All module torsion hypotheses use upstream's
`Scheme.IsTorsionModuleSheaf`, while `Scheme.IsTorsionSheaf` is for abelian sheaves.

## Current compiled closure audit

The user authorized following corrected upstream statements on 2026-10-14, including
substantive changes with adaptations of local users. The six target contracts listed above
are the current upstream boundaries; no local target statement was weakened to obtain a proof.

The completed pure-upstream server build at
`sidebuild-base/2104a988ee9fbee4de847237b493e3bd361d4ebb` reports success for 11,623 jobs.
The exact-tip audit imports that compiled library, with the unchanged shared packages, and
runs within the existing 60-second single-file limit. Both main theorems have precisely
`[propext, sorryAx, Classical.choice, Quot.sound]`. A complete export contains 65,932
project declarations. Traversing project references in declaration types and values reaches
5,699 declarations from the abelian main theorem and 5,594 from its torsion-ring form.
Each closure contains exactly the same six own-sorry owners, namely the six targets listed
above. The full source map and closure traversals are retained in `~/cc1/upsync-audit/`.

Upstream has proved `hasTorsionBaseChange_of_projectiveLine_of_isProper` and
`hasTorsionBaseChange_of_hasInjectiveAcyclicity`, both own-sorry owners in the old main
closure. The modules `BaseChangeTheorems.ProjectiveLine` and
`BaseChangeTheorems.BaseChangeProperty` now have zero own-sorry records. Their proofs
still depend transitively on the six remaining upstream gaps; this audit does not claim
the proper-base-change main theorem is sorry-free.

This source audit uses pure upstream so that a landed local proof resting on unfinished
helpers cannot hide an upstream target. The routine separately requires the combined
side copy's complete default-target build, independent compilation of every local or
retained source file within 60 seconds, name-clash checks, and all current target/definition
hash checks before changing the live base.

## Historical compiled closure audit at ffb7b9060

At 2026-10-13 03:25 +08, the completed pure-upstream server side build
`base-46dc75fcf` was audited again through `sidebuild-base/current`. This supplies exact evidence for the synced
tip: `git diff 46dc75fcf ffb7b9060` changes only `EtaleCohomology/Purity/Smooth/Deformation.lean`,
and that module is absent from the Proper source import closure (1,931 modules).
A single-file `lake env lean` invocation with a 60-second timeout printed both main axioms,
then traversed every declaration referenced by their types or values (opaque values included).
Both main statements have precisely `[propext, sorryAx, Classical.choice, Quot.sound]`.
The abelian statement reaches 88,867 declarations; the torsion-ring form reaches 88,747.
Each closure contains exactly the same six declarations with their own `sorryAx`:

1. `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` — `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`.
2. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`.
3. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`.
4. `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject` — `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`.
5. `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit` — `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity`.
6. `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing` — `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`.

The three additional declarations are exposed by the now-proved reduction and its filtered
colimit/locality ingredients. They are selected as targets alongside the retained three,
using upstream's existing lemma boundaries. `Challenge` contains exactly six named theorem
sorries. The audit was run on pure upstream, because our landed proofs can replace a target
sorry by a proof that still rests on unfinished local helper lemmas.

`shiftedHomFunctor`, `finalObject`, and `unitComparison` must be restated verbatim only in
Challenge: each is defined in a module that also declares one of its targets, so importing
that module there would clash. These are comparator specifications; the compiled library
uses only upstream's definitions. The target checker also compares their types and bodies, ignoring only names of theorem-proof
constants (Lean caches such proof terms under whichever declaration it elaborates first).
A standalone single-file check against the completed upstream build confirmed all six target
type/universe hashes and all three definition type/body hashes agree; both specification
modules compile separately within the 60-second limit.
