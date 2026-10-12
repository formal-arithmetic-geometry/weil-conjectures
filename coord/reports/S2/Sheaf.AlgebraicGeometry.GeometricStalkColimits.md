## What changed

Proved `AlgebraicGeometry.Scheme.geometricStalk_preservesColimits` in
`Sheaf.AlgebraicGeometry.GeometricStalkColimits` without changing its signature.
The first conjunct follows from Mathlib's skyscraper adjunction. The second
uses Mathlib's degreewise preservation instance, after supplying filtered-colimit
preservation of the integer-module forgetful functor by factoring it through
abelian groups. Updated the theorem docstring and the existing node's proof,
proof_deps and proof_origin to match this route. No definitions or statements changed. The second reading narrowed public imports: `Additive` supplies the complex-functor definition; `Skyscraper` and `HomologicalComplexAbelian` are private proof imports.
The unit record has no realized steps or statement nodes to bypass.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.geometricStalk_preservesColimits`
(node `lem-kun-stalks-commute-colimits`): 1 of 1 original sorries closed.
No sorry remains and none was split off. Local compilation succeeds without warnings.
The delivery dry run checks compilation on the server and the declaration's axioms.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.EtaleSheaves` and the corresponding
proof dependency `def-weil-pbc-etale-sheaves`.
The new proof does not directly use the planned nodes
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact` or
`lem-weil-pbc-sheafification-geometric-stalk`; both have Mathlib matches rather
than separate Sheaf modules. Their explicit sheafification-and-stalk-interchange
route is replaced by the skyscraper adjunction and Mathlib complex-colimit theorem.
Retained `def-weil-pbc-geometric-stalks` because its Mathlib definitions are used.
The second reading also reduced the public export of Skyscraper and
HomologicalComplexAbelian to private proof imports, retaining Additive publicly
for the signature. No other existing imports were removed. These pruning claims concern this item's
proof; other items may still need the nodes and EtaleSheaves module.

## Where the brief, the DAG or earlier work was wrong

The earlier searches missed the direct Mathlib adjunction route for the stalk
clause and the preservation instance for `mapHomologicalComplex`. Loogle with
`Functor.mapHomologicalComplex, PreservesColimits` returned unknown identifier;
LeanFinder found the stalk preservation and degreewise evaluation results;
local rg found the exact complex preservation instance in
`Mathlib/Algebra/Homology/HomologicalComplexAbelian.lean`.
The generic `ModuleCat.FilteredColimits.forget_preservesFilteredColimits` instance
ties the ring universe to the module universe, so it does not synthesize for
`ModuleCat.{u} ℤ`. The proof supplies the true instance by composing the two
forgetful functors using the general module-colimit theorem, without changing
universes, assuming new hypotheses, or introducing a new sorry.

## Second reading by S2

1. Compared the complete module and node against the repository versions. The
   existing theorem signature is byte for byte unchanged; there are no definitions
   or other declarations to alter. Verdict: pass.
2. Compiled the original and repaired module locally without warnings. There is
   no sorry or forbidden declaration. A scratch copy prints the theorem's axioms;
   the delivery probe checks the same declaration locally and on delivery.
   Axioms: propext, Classical.choice, Quot.sound. Verdict: pass.
3. No statements were split off and no nodes were added. Thus there are no new
   hypotheses, small-case failures, duplicate lemmas, or restatements to review.
   Verdict: pass.
4. Read Mathlib's skyscraper adjunction, the complex preservation instance, and
   the module-to-abelian-group colimit instances. Searched the existing library
   for the stalk/complex conclusion. The direct adjunction and degreewise route
   is appropriate; the forgetful composition resolves the universe mismatch.
   All three removed old proof dependencies are listed above. The unit's
   `realized.statement` and `realized.steps` are empty, so no unit route is
   bypassed. Verdict: pass after repairing import visibility.
5. Compared the old and delivered node. Only proof, proof_deps and proof_origin
   change; their steps match the Lean proof. The retained dependency names the
   geometric stalk definitions, and the three pruned dependencies are unused.
   Verdict: pass.

Changed the public HomologicalComplexAbelian import to the narrower public
Additive import needed by the theorem signature, and made Skyscraper and
HomologicalComplexAbelian private proof imports. The mathematical proof is
unchanged. No split-off statement needed repair.

Change record: `coord/changes/geometricStalkColimits-imports.md`. The dry run
requires this record for reduced public exports. All 135 downstream modules are
listed; the sole direct importer imports this item privately, so no exported
statements or definitions in those modules change. No module needs adaptation.

Additional validation: compiled a scratch copy of the sole direct importer,
`Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations`, against the repaired
module in import order. Both files compile without warnings, confirming that the
public-import repair requires no downstream adaptation.
