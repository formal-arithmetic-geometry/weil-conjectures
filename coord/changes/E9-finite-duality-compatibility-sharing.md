# AlgebraicGeometry.ProEtale.FiniteDualityCompatibility and FiniteDualityComparisonData

## Reason

Kernel profiles show expensive repeated conversion of the expanded conjunction and of
existentially selected evaluation maps. Share the generic compatibility formula, use the
canonical evaluation and double-dual formulas, and store the full conclusion in a Prop
structure. The fields retain all original clauses. Pairing normalization proves that the
selected maps equal these canonical maps. There is no weaker evaluation or biduality claim.
This changes definitions reached by the targets and requires independent statement review;
no target declaration signature changes.

## Old

```lean
noncomputable def FiniteDualityCompatibility
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (ω : (comparisonUpperStar A X).mapDerivedCategory.obj W ≅ W')
    (hEt : Etale.AmbientDualityPairing A X W)
    (hPro : AmbientDualityPairing A X W')
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let HC := Etale.derivedHom A X
  let HD := derivedHom A X
  ∃ cK : F.obj ((HC.obj (op K)).obj W) ≅ (HD.obj (op (F.obj K))).obj W',
    cK.hom = siteComparisonEvaluationHom A X K W ≫
      (HD.obj (op (F.obj K))).map ω.hom ∧
    ∃ cDK : F.obj ((HC.obj (op ((HC.obj (op K)).obj W))).obj W) ≅
        (HD.obj (op (F.obj ((HC.obj (op K)).obj W)))).obj W',
      cDK.hom = siteComparisonEvaluationHom A X ((HC.obj (op K)).obj W) W ≫
        (HD.obj (op (F.obj ((HC.obj (op K)).obj W)))).map ω.hom ∧
      ((derivedTensor A X).map cK.hom).app (F.obj K) ≫
          hPro.choose_spec.2.choose (F.obj K) =
        (siteComparisonTensorIso A X ((HC.obj (op K)).obj W)).inv.app K ≫
          F.map (hEt.choose_spec.2.choose K) ≫ ω.hom ∧
      F.map (Etale.AmbientDualityPairing.bidualityMap A X hEt K) ≫
          cDK.hom ≫ (HD.map cK.inv.op).app W' =
        AmbientDualityPairing.bidualityMap A X hPro (F.obj K)

noncomputable def FiniteDualityComparisonData
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (w : (comparisonUpperStar A X).mapDerivedCategory.obj W ⟶ W')
    (Pet Qet : ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (Ppro : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) : Prop :=
  (∀ K M : DerivedCategory (Sheaf X.smallEtaleTopology A),
    Pet K → Qet M → IsIso (siteComparisonEvaluationHom A X K M)) ∧
  ∃ ω : (comparisonUpperStar A X).mapDerivedCategory.obj W ≅ W',
    ω.hom = w ∧
    ∃ hEt : Etale.AmbientDualityPairing A X W,
    ∃ hPro : AmbientDualityPairing A X W',
      (∀ K : DerivedCategory (Sheaf X.smallEtaleTopology A), Pet K →
        FiniteDualityCompatibility A X W W' ω hEt hPro K) ∧
      (∃ e : Pet.FullSubcategory ≌ Ppro.FullSubcategory,
        Nonempty (e.functor ⋙ Ppro.ι ≅
          Pet.ι ⋙ (comparisonUpperStar A X).mapDerivedCategory)) ∧
      (∃ d : Ppro.FullSubcategoryᵒᵖ ≌ Ppro.FullSubcategory,
        Nonempty (d.functor ⋙ Ppro.ι ≅ Ppro.ι.op ⋙ (derivedHom A X).flip.obj W')) ∧
      ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
        Ppro K → IsIso (AmbientDualityPairing.bidualityMap A X hPro K)
```

## New

```lean
noncomputable def FiniteDualityCompatibility
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (ω : (comparisonUpperStar A X).mapDerivedCategory.obj W ≅ W')
    (hEt : Etale.AmbientDualityPairing A X W)
    (hPro : AmbientDualityPairing A X W')
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  CategoryTheory.evaluationDualityCompatibility
    (comparisonUpperStar A X).mapDerivedCategory
    (Etale.derivedHom A X) (derivedHom A X)
    (Etale.derivedTensor A X) (derivedTensor A X)
    (siteComparisonEvaluationHom A X)
    (fun K M ↦ (siteComparisonTensorIso A X K).inv.app M) ω
    (nativeEtaleEvaluation A X W) (nativeProEtaleEvaluation A X W')
    (finiteDualityNativeBidual A X W)
    (nativeProEtaleBiduality A X W') K

noncomputable def FiniteDualityComparisonData
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (w : (comparisonUpperStar A X).mapDerivedCategory.obj W ⟶ W')
    (Pet Qet : ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (Ppro : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) : Prop :=
  CategoryTheory.EvaluationDualityData (comparisonUpperStar A X).mapDerivedCategory
    (Etale.derivedHom A X) (derivedHom A X)
    (Etale.derivedTensor A X) (derivedTensor A X)
    (siteComparisonEvaluationHom A X)
    (fun K M ↦ (siteComparisonTensorIso A X K).inv.app M)
    (Etale.AmbientDualityPairing A X) (AmbientDualityPairing A X)
    (fun W _ ↦ nativeEtaleEvaluation A X W) (fun W _ ↦ nativeProEtaleEvaluation A X W)
    (fun W _ ↦ finiteDualityNativeBidual A X W)
    (fun W _ ↦ nativeProEtaleBiduality A X W) W W' w Pet Qet Ppro
```

The native evaluation is the descended Koszul symmetry followed by internal-Hom evaluation.
The native biduality is its transpose. Pairing normalization proves the original selected
maps equal these canonical maps. The generic Prop structure stores the former conjunction's
two components with all the same remaining clauses. The site definition specializes it;
it is a definition, not a new structure declaration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | E9 | Complete proof and shared formulas. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Destruct `hc.transport`; rewrite the canonical biduality with pairing normalization. Existing signatures stay identical. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Uses compatibility in a statement; same mathematical equations. |
| Sheaf.Paper.BoundaryFiniteSiteData | unclaimed | Uses compatibility in a statement; same mathematical equations. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | C8 | Transitive consumer through BoundaryFiniteSiteData; no source edit. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed | Uses compatibility in a statement; same mathematical equations. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Unfolds `FiniteDualityComparisonData` with `dsimp only` (line 284); compiles unchanged against the new definition (reviewer check). |

Textual users checked with `tools/downstream.py --uses` and `rg` across both library roots.
The only consumer whose source had to change is FiniteStageVerdierBiduality.
The adopted WeilConjectures tree is unchanged. AmbientDualityPairing is unchanged.

The delivery path of this record is
`coord/changes/E9-finite-duality-compatibility-sharing.md`. For a reviewer override,
`tools/batch_land.py` maps it to the fix-directory filename
`E9-finite-duality-compatibility-sharing.change.md` (the `.change.md` suffix is required).
The ordinary `.md` basename is not an accepted reviewer-override filename.
The Old definitions above were checked verbatim against the current shared source,
and the New definitions against the delivered module.

## Status

landed 20261026T001410-L-4189220 2026-10-26 (merge of deliver/E9/Sheaf.SixFunctors.FiniteDualitySiteComparison)
