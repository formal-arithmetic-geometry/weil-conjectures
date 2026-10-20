# CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality

## Reason

Retire the duplicate Sheaf module under the human's 2026-10-20 hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The item's row in
coord/retire-items.tsv names the official twin, has depth zero and no prerequisite
retirements. The original module has zero direct holes. The official theorem has
exactly the same signature after whitespace normalization and a complete proof.
A server-compiled example with the original statement applies the official theorem;
its axiom probe reports only propext, Classical.choice and Quot.sound.
No source-library file or target statement changes.

## Old

The redundant module Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality declares:

```lean
theorem etale_torsor_h1_functoriality :
    (∀ (X Y : Scheme.{u}) (f : Y ⟶ X)
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (T : Torsor G),
      ∃ (T' : Torsor ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G))
        (eT : (Scheme.etaleSetPullback f).obj T.sheaf ≅ T'.sheaf),
        (∀ (W : X.Etale) (g : G.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
          eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (Y.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
                (T.vadd (op W) g t)) =
          T'.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
              (op W) g)
            (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
                (X.smallGrothendieckTopology @Etale)
                (Y.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))) ∧
        Etale.cohomologyMap f G 1 (classH1 G terminalIsTerminal ⟦T⟧) =
          classH1 ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G) terminalIsTerminal ⟦T'⟧) ∧
    (∀ (S : Scheme.{u}) (G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (φ : G ⟶ G') (T : Torsor G),
      ∃ T' : Torsor G', Nonempty (ContractedProductPresentation.{u, u} S φ T T') ∧
        H.map φ 1 (classH1 G terminalIsTerminal ⟦T⟧) =
          classH1 G' terminalIsTerminal ⟦T'⟧)
```

Both active consumers have the private proof import:

```lean
import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
```

The DAG node lem-sc-etale-torsor-h1-functoriality is attached to that Sheaf module.

## New

The declaration name, universe and entire signature above remain identical in
WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality. Both active consumers instead use:

```lean
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
```

Withdraw the Sheaf file through deleted.txt and attach the same DAG node to the
official module/file, with existing=true and an explanatory note. All mathematical
node statements, dependencies and unit steps remain. No proof body in either
consumer changes. The source theorem's proof and imports are untouched.

## Users

Refreshed tools/downstream.py inventory: 18 downstream modules, two declaration
name matches (the item declaration and GmPicardPullback's existing application).
There are two active direct importers. Both are unclaimed in the current local claim
records. The withdrawal forces their private import migrations. The first server
preflight additionally required removing the pre-existing unused imports of
Sheaf.AlgebraicGeometry.SetLocalSystemCalculus and
Sheaf.DeligneLaumon.TorsionFiniteSubsystem from TorsionTorsorDescent: both are
listed in coord/route-pivot-dropped-modules.txt. Its statement mentions no name
from them and its proof is the existing named sorry. Recompilation validates
that removing those imports preserves the statement. No proof or declaration
changes accompany this cleanup.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.GmPicardPullback | unclaimed | Only proof import line 13 changes; existing theorem application and all proofs stay verbatim. |
| Sheaf.AlgebraicGeometry.LocalSystemTensorMonodromy | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.AlgebraicGeometry.TorsionTorsorDescent | unclaimed | Replace proof import line 15 and remove two unused route-pivot imports; named hole untouched. |
| Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.Paper.GaloisPartitionTensorClosure | unclaimed | No signature, definition or proof changes; transitive theorem provider is the official twin. |
| Sheaf.Paper.PurityConventions | quarantined, not restored here | Preserve archive and mathematical dependencies; restoration must replace the archived import as specified below. |
| Sheaf.Paper.KummerAdditivity | quarantined, not restored here | Preserve archive and mathematical dependencies; restoration must replace the archived import as specified below. |
| Sheaf.Paper.ProjectiveBundleFormula | quarantined, not restored here | Preserve archive and mathematical dependencies; restoration must replace the archived import as specified below. |


The following archived import migrations are recorded for their own rework items;
the quarantine snapshots are preserved and are not compiled or restored here:

```diff
--- quarantine/Sheaf/Paper/PurityConventions.lean
-public import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
+public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
--- quarantine/Sheaf/Paper/KummerAdditivity.lean
-import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
+import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
--- quarantine/Sheaf/Paper/ProjectiveBundleFormula.lean
-import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
+import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality
```

The DAG parents are lem-sbc-torsor-cohomology-lift-criterion, sk-def-purity-conv,
lem-per-torsion-torsor-descent, lem-weil-pbc-finite-etale-equivalence-h1,
lem-weil-pbc-scheme-torsor-pullback-equivariant-hom-is-iso, lem-pur-kummer-additivity,
thm-pur-projective-bundle-formula, def-pur-affine-line-datum and
lem-sc-h1-gm-pic-pullback. They keep citing exactly the same mathematical node and
Lean declaration, now supplied upstream. No parent argument is bypassed.
The unit sk-prop-ext-invariance has no realized attachment requiring the duplicate
module itself. The theorem and its supporting mathematics are retained.

## Status

landed 20261020T221223-L-4159988 2026-10-20 (merge of deliver/J5/Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality)
