## What changed

Closed `hasProjectionFormulaOfCompactification_iff` by proving both directions from the
finite coefficient projection formula. The forward direction applies
`hasProjectionFormula_of_finite`; the reverse direction unfolds the compactification
projection map, applies the finite proper projection theorem to `c.g`, and uses instance
inference for the remaining isomorphisms. The module and all existing signatures are
unchanged.

## Proved and sorry left

Closed one original proof hole:

- `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_iff`.

The following original holes remain unchanged:

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`.
- `AlgebraicGeometry.Etale.hasProjectionFormula_id`.

No new statements or holes were added.

## No longer needed

The public imports `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` and
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`, and the plain import
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`, were removed because they are unused.
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable` was made private because it
is proof-only. The proof uses the existing finite projection theorem,
`HasProjectionFormulaOfCompactification`, and `projectionMapOfCompactification_app_app`.

## Where the brief, the DAG or earlier work was wrong

No statement or route was found to be wrong. The finite proper projection theorem remains the
substantive unproved input; the compactification independence statement is a direct consequence
once that theorem is available.

## New nodes

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** Compared the delivered module with the repository version.
   The only declaration body changed is `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_iff`;
   all existing declaration signatures and definitions are byte-for-byte unchanged. The finite proper
   projection statement and its node `lem-etale-proper-projection-formula-finite` remain unchanged.
   Verdict: pass.

2. **Proof and trust basis.** Compiled the module with `python3 /home/ubuntu/weil-launcher/lcompile.py`.
   It compiles without errors or warnings. The proof closes the compactification-independence hole by
   reducing each direction to `hasProjectionFormula_of_finite` and
   `isIso_rightDerivedLowerStarProjectionMap_of_finite`; no new `sorry`, axiom, unsafe, opaque,
   extern, or hollow definition was introduced. Verdict: pass.

3. **Statements and searches.** Checked the finite proper projection statement against the existing
   node and searched the local library and Mathlib for duplicate projection-map results. The statement
   is true for finite rings (including the zero ring) and is exactly the existing unbounded proper
   projection theorem used by the proof. No new statement was split off. Verdict: pass.

4. **Route and pruning.** The proof keeps the coherence route through the finite projection theorem
   and the compactification projection-map decomposition. I verified imports individually: the
   `ProjectionMapDualizable` import is proof-only, while `ModuleCat.AB` and
   `Etale.Derived.UpperLowerStar` are redundant because the remaining imports already provide the
   declarations used by the module. Removed all three from the public import list. No DAG proof
   dependency is made unused by the changed proof. Verdict: pass.

5. **DAG agreement and unit route.** The module's remaining holes and the finite-projection node agree
   with the Lean declarations; the coherence unit's route is retained. No node files or change
   records were needed. Verdict: pass.

Changed in this second reading: pruned the two redundant public imports, made the projection-map
adjunction import private because it is needed only by a proof, added change record
`coord/changes/projection-formula-imports.md`, and updated this report.

## Second reading by Q1

1. **Signatures and accidental changes.** I compared the delivered module with the repository
   version. Existing declaration signatures and definitions are unchanged byte-for-byte; the only
   theorem body added is the proof of `AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_iff`.
   The import edits are recorded in `coord/changes/projection-formula-imports.md`. Verdict: pass.

2. **Proof and trust basis.** I compiled the module with
   `python3 /home/ubuntu/weil-launcher/lcompile.py`. It compiles without errors or warnings. The
   proof closes the compactification-independence theorem by applying the finite projection formula
   in each direction and the compactification projection-map decomposition in the reverse direction.
   The only remaining `sorry`s are the two declarations named above in the report; no forbidden
   declarations or hollow definitions were introduced. Verdict: pass.

3. **Statements and searches.** I checked the theorem statement against the existing finite
   coefficient and compactification definitions, including the zero-ring edge case, and checked the
   local declarations and recorded search for duplicate projection-map results. No new statement was
   split off, and the existing statement is unchanged. Verdict: pass.

4. **Route and pruning.** The proof uses the finite projection theorem and the compactification
   projection-map decomposition. I verified that `ProjectionMapDualizable` is proof-only and that
   `ModuleCat.AB`, `Etale.Derived.UpperLowerStar`, and
   `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` are unnecessary after the proof; all
   three removals are listed under `## No longer needed` and in the change record. Verdict: pass.

5. **DAG agreement and unit route.** The remaining holes and the finite-projection node agree with
   the Lean declarations, and the coherence unit still realizes its compactification-independence
   step. No node or statement change is needed. Verdict: pass.

I changed only the report and import change record during this second reading, adding the omitted
removed import and documenting the five checks above.
