# AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry

## Reason

Human-authorized retirement, listed in coord/retire-items.tsv (depth 2, class DIFFERENT).
The Sheaf copy duplicates the official diagram and projections but gives the cone the
small coordinate-ring colimit as vertex. Upstream uses the full-colimit strictLocalization.
The two schemes are canonically isomorphic, not definitionally equal. Replacing the import
alone would change the domains of cone legs in proved source-restriction formulas.

Use the official structure and its proved existence theorem. The new, fully proved
StrictLocalSmallModel.NeighbourhoodGeometry API transports its legs and limiting property
along pullback.map of Spec(smallStrictHenselizationColimitIso.inv). The existing proved
smallStrictHenselizationColimitIso_toBase supplies its equation over S. The inverse colimit
coprojection equation proves the exact first-component formula; pullback.map proves the
over equation. This is actual canonical transport, with no arbitrary witness or new hole.

The continuity and injective-section statements retain their original small-model schemes,
structural morphisms, cohomology source and target groups, and mate. Their auxiliary Q now
has the official type, and every use of its cone uses the transported API. This is an
isomorphic presentation of the same uniquely specified cone; it adds no assumption and
changes no target statement or mathematical meaning. The DAG geometry attachment moves
to the official library. The chapter and unit route are unchanged.

## Old

The retired Sheaf structure, verbatim:

```lean
structure StrictLocalNeighbourhoodGeometry {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) where
  legs : (Functor.const (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))).obj
      (pullback f (Scheme.strictHenselizationStructuralMap s)) ⟶
    strictLocalNeighbourhoodDiagram f s
  isLimit : IsLimit (Cone.mk _ legs)
  [compact : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i)]
  [quasiSeparated : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i)]
  [affine : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a)]
  first : ∀ i, legs.app i ≫ pullback.fst ((strictLocalNeighbourhoods s).obj i).hom f =
    pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
      (Scheme.strictHenselizationCone s).π.app (op (op i)) ≫
        Spec.map (Scheme.ΓSpecIso
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            i).1.left.unop).inv
  over : ∀ i, legs.app i ≫ (strictLocalNeighbourhoodProjection f s).app i =
    pullback.fst f (Scheme.strictHenselizationStructuralMap s)
```

The copied diagram/projection definitions are identical to the official ones. The two
live direct imports of the retired module occur in StrictLocalCohomologyGerms and
StrictLocalSmallModel.StrictLocalNeighbourhoodGeometryExistence. Their original import is:

```lean
public import Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
```

The existence helper duplicated the cone construction using the original-model
strictHenselizationBaseChangeCone_exists. All downstream Q.legs, Q.isLimit, Q.first and
Q.over referred to that small-model structure.

## New

The adopted official structure is left verbatim:

```lean
structure StrictLocalNeighbourhoodGeometry {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) where
  legs : (Functor.const (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))).obj
      (pullback f (Scheme.strictLocalizationToBase s)) ⟶
    strictLocalNeighbourhoodDiagram f s
  isLimit : IsLimit (Cone.mk _ legs)
  [compact : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i)]
  [quasiSeparated : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i)]
  [affine : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a)]
  first : ∀ i, legs.app i ≫ pullback.fst ((strictLocalNeighbourhoods s).obj i).hom f =
    pullback.snd f (Scheme.strictLocalizationToBase s) ≫
      (Scheme.strictHenselizationAffineCone s).π.app (op (op i)) ≫
        Spec.map (Scheme.ΓSpecIso
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            i).1.left.unop).inv
  over : ∀ i, legs.app i ≫ (strictLocalNeighbourhoodProjection f s).app i =
    pullback.fst f (Scheme.strictLocalizationToBase s)
```

All consumers whose signatures or definitions use the transported legs explicitly publicly import
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry, which publicly imports
WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry and the existing
structural-map comparison. The new module contains only the canonical pullback isomorphism
and its transported-cone API:

```lean
noncomputable def strictLocalSmallModelPullbackIso {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    pullback f (Scheme.strictHenselizationStructuralMap s) ≅
      pullback f (Scheme.strictLocalizationToBase s) :=
  asIso (pullback.map _ _ _ _ (𝟙 X)
    (Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv) (𝟙 S)
    (by simp) (by simpa using (Scheme.smallStrictHenselizationColimitIso_toBase s).symm))

namespace StrictLocalNeighbourhoodGeometry

/-- Upstream's legs expressed on the small coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport). -/
noncomputable def smallModelLegs {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s) :
    (Functor.const (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))).obj
      (pullback f (Scheme.strictHenselizationStructuralMap s)) ⟶
        strictLocalNeighbourhoodDiagram f s :=
  (Cone.mk _ Q.legs).extend (strictLocalSmallModelPullbackIso f s).hom |>.π

/-- Transport preserves the limiting property of the cone.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport).
Proof: extend the upstream limiting cone along the pullback comparison isomorphism;
`Cone.extendIso` identifies it with the original limit cone. -/
noncomputable def smallModelIsLimit {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s) : IsLimit (Cone.mk _ Q.smallModelLegs) :=
  Q.isLimit.ofIsoLimit
    (Cone.extendIso (Cone.mk _ Q.legs) (strictLocalSmallModelPullbackIso f s).symm)

/-- The transported legs have the original projection to X.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport).
Proof: compose the upstream projection equation with the comparison and use the
first projection formula for the pullback map. -/
theorem smallModelOver {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Q.smallModelLegs.app i ≫ (strictLocalNeighbourhoodProjection f s).app i =
      pullback.fst f (Scheme.strictHenselizationStructuralMap s) := by
  change (strictLocalSmallModelPullbackIso f s).hom ≫ Q.legs.app i ≫ _ = _
  rw [Q.over]
  simp [strictLocalSmallModelPullbackIso]

/-- The transported base component is exactly the small-model colimit leg.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport).
Proof: the inverse final-functor colimit comparison preserves each coprojection.
Apply Spec, compose with the affine Gamma-Spec identification, then use the second
projection formula for the pullback comparison and the upstream first-component equation. -/
theorem smallModelFirst {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Q.smallModelLegs.app i ≫ pullback.fst ((strictLocalNeighbourhoods s).obj i).hom f =
      pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
        (Scheme.strictHenselizationCone s).π.app (op (op i)) ≫
          Spec.map (Scheme.ΓSpecIso
            ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              i).1.left.unop).inv := by
  classical
  let rep := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse
  let incl := Scheme.strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := Scheme.strictHenselizationAffineInclusion_isEquivalence s
  have h := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (Scheme.strictHenselizationDiagram s) (op i)
  change colimit.ι (Scheme.strictHenselizationDiagram s) (op (incl.obj (rep.obj i))) ≫
    (Scheme.smallStrictHenselizationColimitIso s).inv =
      colimit.ι (Scheme.strictHenselizationAffineDiagram s) (op i) at h
  have hh := congrArg Spec.map h
  simp only [Spec.map_comp] at hh
  change (strictLocalSmallModelPullbackIso f s).hom ≫ Q.legs.app i ≫ _ = _
  rw [Q.first]
  simp only [strictLocalSmallModelPullbackIso, asIso_hom, pullback.map,
    Category.assoc, pullback.lift_snd_assoc]
  change pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
    Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv ≫
      Spec.map (colimit.ι (Scheme.strictHenselizationDiagram s)
        (op (incl.obj (rep.obj i)))) ≫ _ = _
  simpa only [Category.assoc] using congrArg
    (fun k ↦ pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫ k ≫
      Spec.map (Scheme.ΓSpecIso (rep.obj i).1.left.unop).inv) hh

end StrictLocalNeighbourhoodGeometry
end AlgebraicGeometry.Etale
```

Every affected consumer replaces Q.legs by Q.smallModelLegs, Q.isLimit by
Q.smallModelIsLimit, Q.first by Q.smallModelFirst, and Q.over by Q.smallModelOver.
All diagram, stage and projection names are now supplied by the unchanged official module.
The original-model existence helper now directly applies
nonempty_strictLocalNeighbourhoodGeometry; its old private imports of
WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone and
Mathlib.AlgebraicGeometry.Morphisms.Affine are unnecessary.

Exact consumer edits (the minus and plus lines give the original and adapted text):

### Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison

```diff
--- lean/Sheaf/AlgebraicGeometry/EtaleInjectiveSectionsComparison.lean

+++ lean/Sheaf/AlgebraicGeometry/EtaleInjectiveSectionsComparison.lean

@@ -7,4 +7,5 @@

 
 public import Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
 import WeilConjectures.AlgebraicGeometry.EtaleSectionsTriangleNaturality
@@ -195,5 +196,5 @@

       (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
         ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
-          (Q.legs.app i)).unit.app
+          (Q.smallModelLegs.app i)).unit.app
             ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
         i)).mapDerivedCategory.obj
@@ -201,6 +202,6 @@

       (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
         ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
-          AddCommGrpCat.{v + 1} (Q.legs.app i)).hom.app
-            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i)).mapDerivedCategory.obj
+          AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).hom.app
+            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).mapDerivedCategory.obj
               ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
         s).app i)).mapDerivedCategory.obj
@@ -209,15 +210,15 @@

         s)) n).map
         ((Functor.mapDerivedCategoryNatIso
-          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
+          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
         ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
         (Scheme.strictHenselizationStructuralMap s))
-            (Q.over i).symm) ≪≫
+            (Q.smallModelOver i).symm) ≪≫
           Functor.mapDerivedCategoryCompIso
             (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
-            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i))).inv.app K.obj) =
-        termwiseSectionsRestriction (Q.legs.app i)
+            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).inv.app K.obj) =
+        termwiseSectionsRestriction (Q.smallModelLegs.app i)
           ((strictLocalNeighbourhoodProjection f s).app i)
           (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
-          (Q.over i).symm
+          (Q.smallModelOver i).symm
           (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
         representativeSectionsComparison
@@ -238,7 +239,7 @@

       _ q n
   · intro i
-    exact sectionsComparison_triangle_naturality (Q.legs.app i)
+    exact sectionsComparison_triangle_naturality (Q.smallModelLegs.app i)
       ((strictLocalNeighbourhoodProjection f s).app i)
-      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.over i).symm
+      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm
       _ q n
 
```

### Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalCohomologyGerms.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalCohomologyGerms.lean

@@ -9,5 +9,5 @@

 public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
 public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
-public import Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 import Sheaf.AlgebraicGeometry.PointedEtaleSectionConeStalkIso
 import Sheaf.Paper.StrictHenselizationFunctoriality
```

### Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean

@@ -7,4 +7,5 @@

 
 public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
 public import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms
@@ -87,9 +88,9 @@

     I := SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)
     D := strictLocalNeighbourhoodDiagram f s
-    c := Cone.mk _ Q.legs
-    isLimit := Q.isLimit
+    c := Cone.mk _ Q.smallModelLegs
+    isLimit := Q.smallModelIsLimit
     t := strictLocalNeighbourhoodProjection f s
     p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
-    «over» := Q.over
+    «over» := Q.smallModelOver
     F := strictLocalCohomologyNeighbourhoodFunctor s
       ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
```

### Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalMateProjectionData.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalMateProjectionData.lean

@@ -7,4 +7,5 @@

 
 public import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
 public import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms
@@ -144,5 +145,5 @@

       (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
         ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
-          (Q.legs.app i)).unit.app
+          (Q.smallModelLegs.app i)).unit.app
             ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
         i)).mapDerivedCategory.obj
@@ -150,6 +151,6 @@

       (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
         ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
-          AddCommGrpCat.{v + 1} (Q.legs.app i)).hom.app
-            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i)).mapDerivedCategory.obj
+          AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).hom.app
+            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).mapDerivedCategory.obj
               ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
         s).app i)).mapDerivedCategory.obj
@@ -158,11 +159,11 @@

         s)) n).map
         ((Functor.mapDerivedCategoryNatIso
-          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
+          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
         ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
         (Scheme.strictHenselizationStructuralMap s))
-            (Q.over i).symm) ≪≫
+            (Q.smallModelOver i).symm) ≪≫
           Functor.mapDerivedCategoryCompIso
             (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
-            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i))).inv.app K.obj) ≫
+            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).inv.app K.obj) ≫
       (strictLocalBaseChangeTargetIso f s K n).inv
 
```

### Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalComplexSectionsMate.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalComplexSectionsMate.lean

@@ -8,4 +8,6 @@

 
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
+import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization
 
@@ -51,6 +53,6 @@

 level evaluate f_*M on the pointed neighbourhood, using smallModel_sourceStageSectionsIso.
 The unit, square comparison, and counit send a section to its restriction on the
-pullback. Q.first identifies the base component of this map with the specified
-strict-henselization leg; Q.over identifies the projection to X. These are the
+pullback. Q.smallModelFirst identifies the base component of this map with the specified
+strict-henselization leg; Q.smallModelOver identifies the projection to X. These are the
 components defining termwiseSectionsRestriction. Apply localization and H^n;
 naturality of the homology and exact-sections comparisons gives the displayed
@@ -87,7 +89,7 @@

       ((NatIso.mapHomologicalComplex (smallModel_sourceStageSectionsIso f s i) (.up ℤ)).hom.app M) ≫
     (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
-    termwiseSectionsRestriction (Q.legs.app i)
+    termwiseSectionsRestriction (Q.smallModelLegs.app i)
       ((strictLocalNeighbourhoodProjection f s).app i)
-      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.over i).symm M n ≫
+      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm M n ≫
     representativeSectionsComparison
       (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n := by
@@ -98,5 +100,5 @@

   let a := (NatIso.mapHomologicalComplex (smallModel_sourceStageSectionsIso f s i)
     (.up ℤ)).hom.app M
-  let b := (NatTrans.mapHomologicalComplex (sectionsPullbackNat (Q.legs.app i))
+  let b := (NatTrans.mapHomologicalComplex (sectionsPullbackNat (Q.smallModelLegs.app i))
       (.up ℤ)).app
       (((upperStar AddCommGrpCat.{v + 1}
@@ -106,7 +108,7 @@

       AddCommGrpCat.{v + 1}).mapHomologicalComplex (.up ℤ)).map
         ((NatIso.mapHomologicalComplex
-          (upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
+          (upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
             ((strictLocalNeighbourhoodProjection f s).app i)
-            (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.over i).symm)
+            (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm)
           (.up ℤ)).inv.app M)
   have hb : (NatTrans.mapHomologicalComplex (smallModel_strictLocalUnderivedMateSections f s i)
```

### Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceDerivedRestriction.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceDerivedRestriction.lean

@@ -8,4 +8,5 @@

 
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate
 
@@ -42,9 +43,9 @@

 passes to homology and then takes the geometric germ of this same class.
 The germ-leg characterization of strictHenselizationStalkRestriction, together
-with Q.first, identifies this with restriction along the base cone leg.
+with Q.smallModelFirst, identifies this with restriction along the base cone leg.
 Expand the derived mate as its adjunction unit, square comparison, and counit.
 Naturality of the units and counits and the two triangle identities identify
 its composite with that germ restriction with the derived adjunction unit along
-Q.legs.app i. Q.over identifies the composite inverse image with the limit
+Q.smallModelLegs.app i. Q.smallModelOver identifies the composite inverse image with the limit
 projection. The resulting map to limit hypercohomology is therefore the derived
 unit, Leray, and inverse composition comparison displayed on the right.
@@ -83,5 +84,5 @@

       (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
         ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
-          (Q.legs.app i)).unit.app
+          (Q.smallModelLegs.app i)).unit.app
             ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
         i)).mapDerivedCategory.obj
@@ -89,6 +90,6 @@

       (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
         ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
-          AddCommGrpCat.{v + 1} (Q.legs.app i)).hom.app
-            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i)).mapDerivedCategory.obj
+          AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).hom.app
+            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).mapDerivedCategory.obj
               ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
         s).app i)).mapDerivedCategory.obj
@@ -97,11 +98,11 @@

         s)) n).map
         ((Functor.mapDerivedCategoryNatIso
-          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
+          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
         ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
         (Scheme.strictHenselizationStructuralMap s))
-            (Q.over i).symm) ≪≫
+            (Q.smallModelOver i).symm) ≪≫
           Functor.mapDerivedCategoryCompIso
             (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
-            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i))).inv.app K.obj) := by
+            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).inv.app K.obj) := by
   intro i
   let M : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ :=
```

### Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceRestriction.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceRestriction.lean

@@ -8,4 +8,5 @@

 
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction
 
@@ -41,6 +42,6 @@

 with the shift isomorphism putting it in degree n. The defining germ-leg equation
 for the unique strict-henselization stalk restriction takes this class to its
-inverse-image restriction on the strict-local pullback. Q.first and Q.over fix
-both projections of that restriction and identify it with Q.legs.app i.
+inverse-image restriction on the strict-local pullback. Q.smallModelFirst and Q.smallModelOver fix
+both projections of that restriction and identify it with Q.smallModelLegs.app i.
 On the injective representative, the derived adjunction unit and counit are the
 classes of their termwise units and counits. Expand mateEquiv and the pullback
@@ -78,8 +79,8 @@

                 |>.natTrans.app K))) =
             (smallModel_strictLocalInjectiveSourceIso f s K n J q i).hom ≫
-              termwiseSectionsRestriction (Q.legs.app i)
+              termwiseSectionsRestriction (Q.smallModelLegs.app i)
                 ((strictLocalNeighbourhoodProjection f s).app i)
                 (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
-                (Q.over i).symm
+                (Q.smallModelOver i).symm
                 (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
               representativeSectionsComparison
```

### Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceSections.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceSections.lean

@@ -8,4 +8,5 @@

 
 public import Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceTransition
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction
@@ -104,8 +105,8 @@

                 |>.natTrans.app K))) =
             (e i).hom ≫
-              termwiseSectionsRestriction (Q.legs.app i)
+              termwiseSectionsRestriction (Q.smallModelLegs.app i)
                 ((strictLocalNeighbourhoodProjection f s).app i)
                 (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
-                (Q.over i).symm
+                (Q.smallModelOver i).symm
                 (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
               representativeSectionsComparison
```

### Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalNeighbourhoodGeometryExistence

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalNeighbourhoodGeometryExistence.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalNeighbourhoodGeometryExistence.lean

@@ -8,7 +8,6 @@

 
 
-public import Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
-import WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone
-import Mathlib.AlgebraicGeometry.Morphisms.Affine
+public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
+import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
 
 /-! # Existence of the canonical strict-local neighbourhood geometry
@@ -38,67 +37,13 @@

 (blueprint: lem-weil-pbc-strict-local-neighbourhood-geometry).
 
-Proof: `strictHenselizationBaseChangeCone_exists` supplies the limiting cone over
-exactly the same small affine neighbourhood diagram, with vertex S_(s) ×_S X and
-both specified projection equations. Precompose its legs with pullback symmetry
-from X ×_S S_(s), and transport the limit by the induced cone isomorphism.
-Precomposing each supplied projection equation with that symmetry proves `first`
-and `over`. Each neighbourhood is a spectrum, hence affine, compact and
-quasi-separated. Its stage projection is a base change of f, so Mathlib's
-`QuasiCompact.compactSpace_of_compactSpace` and
-`quasiSeparatedSpace_of_quasiSeparated` prove the two stage properties. Each
-transition is the base change of a map between affine neighbourhoods, so
-`MorphismProperty.pullbackLift_fst_snd` proves that it is affine. No global qcqs
-assumption on X or S is used. -/
+Proof: apply the proved upstream existence theorem. Its canonical-model cone
+has the same neighbourhood diagram, qcqs stages and affine transitions. The
+`smallModelLegs`, `smallModelIsLimit`, `smallModelFirst` and `smallModelOver` API
+transports that cone to the original coordinate-ring colimit model when needed. -/
 theorem smallModel_nonempty_strictLocalNeighbourhoodGeometry {X S : Scheme.{v}}
     (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
     {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
     Nonempty (StrictLocalNeighbourhoodGeometry f s) := by
-  classical
-  obtain ⟨π, hπ, hp, hf⟩ := Scheme.strictHenselizationBaseChangeCone_exists f s
-  let A := strictLocalNeighbourhoods s
-  let D := strictLocalNeighbourhoodDiagram f s
-  have hAff (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
-      IsAffine (A.obj i).left := by
-    change IsAffine (Spec _)
-    infer_instance
-  let hComp (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
-      CompactSpace (D.obj i) := by
-    let : IsAffine (A.obj i).left := hAff i
-    exact QuasiCompact.compactSpace_of_compactSpace
-      (Y := (A.obj i).left) (pullback.fst (A.obj i).hom f)
-  let hQS (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
-      QuasiSeparatedSpace (D.obj i) := by
-    let : IsAffine (A.obj i).left := hAff i
-    exact quasiSeparatedSpace_of_quasiSeparated
-      (Y := (A.obj i).left) (pullback.fst (A.obj i).hom f)
-  let hTrans {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)}
-      (a : i ⟶ j) : IsAffineHom (D.map a) := by
-    let : IsAffine (A.obj i).left := hAff i
-    let : IsAffine (A.obj j).left := hAff j
-    change IsAffineHom (pullback.lift _ _ _)
-    exact MorphismProperty.pullbackLift_fst_snd
-      (P := @IsAffineHom) f (MorphismProperty.Over.w (A.map a)).symm
-      (isAffineHom_of_isAffine
-        (X := (A.obj i).left) (Y := (A.obj j).left) _)
-  let c : Cone D := Cone.mk _ π
-  let e := pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)
-  let c' := c.extend e.hom
-  refine ⟨{
-    legs := c'.π
-    isLimit := ?_
-    compact := hComp
-    quasiSeparated := hQS
-    affine := hTrans
-    first := ?_
-    over := ?_ }⟩
-  · exact hπ.some.ofIsoLimit (Cone.extendIso c e.symm)
-  · intro i
-    change e.hom ≫ π.app i ≫ pullback.fst (A.obj i).hom f = _
-    simpa [e, A, strictLocalNeighbourhoods, Scheme.strictHenselizationEtaleDiagram] using
-      congrArg (fun g ↦ e.hom ≫ g) (hf i)
-  · intro i
-    change e.hom ≫ π.app i ≫ pullback.snd (A.obj i).hom f = _
-    simpa [e, A, strictLocalNeighbourhoods, Scheme.strictHenselizationEtaleDiagram] using
-      congrArg (fun g ↦ e.hom ≫ g) (hp i)
+  exact nonempty_strictLocalNeighbourhoodGeometry f s
 
 end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalUnderivedSectionsMate.lean

+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalUnderivedSectionsMate.lean

@@ -8,4 +8,5 @@

 
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 public import WeilConjectures.SixFunctors.BaseChange.Square
 import WeilConjectures.AlgebraicGeometry.EtaleObjectSections
@@ -426,6 +427,6 @@

 the stage, identified by smallModel_sourceStageSectionsIso, followed by sectionsPullbackNat
 along the cone leg and the inverse composition comparison upperStarComp.
-Q.first identifies the map on the base with the pointed neighbourhood section;
-Q.over identifies the composite projection to X. These equations determine the
+Q.smallModelFirst identifies the map on the base with the pointed neighbourhood section;
+Q.smallModelOver identifies the composite projection to X. These equations determine the
 map into the scheme pullback, so both evaluations use the same map. All operations
 are functorial in F, giving the equality of natural transformations. No etaleness
@@ -439,10 +440,11 @@

         Functor.whiskerLeft
           (upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
-          (sectionsPullbackNat (Q.legs.app i)) ≫
+          (sectionsPullbackNat (Q.smallModelLegs.app i)) ≫
         (Functor.associator _ _ _).inv ≫
         Functor.whiskerRight
-          (upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
+          (upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
             ((strictLocalNeighbourhoodProjection f s).app i)
-            (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.over i).symm).inv
+            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
+            (Q.smallModelOver i).symm).inv
           (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
             AddCommGrpCat.{v + 1}) := by
@@ -517,5 +519,5 @@

   change ((upperStarLowerStarAdjunction A p).unit.app F).hom.app (op U) ≫
     H.obj.map ψ.op ≫ tX.inv.app H = _
-  have hψ : ψ.left ≫ pullback.fst U.hom p = Q.legs.app i := by
+  have hψ : ψ.left ≫ pullback.fst U.hom p = Q.smallModelLegs.app i := by
     apply pullback.hom_ext
     · change e.inv.left ≫ (h.Etale.map σ).left ≫ (c₂.inv.app W).left ≫
@@ -536,5 +538,5 @@

         exact pullback.lift_fst _ _ _
       simp only [Category.assoc]
-      rw [hσ, Q.first]
+      rw [hσ, Q.smallModelFirst]
       have hew := e.inv.w
       change e.inv.left ≫ pullback.snd (𝟙 _) h = 𝟙 _ at hew
@@ -548,10 +550,11 @@

       change (ψ.left ≫ pullback.fst U.hom p) ≫ U.hom = _
       rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
-      exact (Category.id_comp p).trans (Q.over i).symm
-  have hp := pointedSections_pullback p U (Q.legs.app i) (Q.over i).symm ψ hψ F
+      exact (Category.id_comp p).trans (Q.smallModelOver i).symm
+  have hp := pointedSections_pullback p U (Q.smallModelLegs.app i) (Q.smallModelOver i).symm ψ hψ F
   change _ = (etaleObjectSectionsIso U).hom.app F ≫
-    globalSectionsUpperStarMap A (Q.legs.app i) ((upperStar A U.hom).obj F) ≫
+    globalSectionsUpperStarMap A (Q.smallModelLegs.app i) ((upperStar A U.hom).obj F) ≫
       (Sheaf.Γ (pullback f g).smallEtaleTopology A).map
-        ((upperStarComp A (Q.legs.app i) U.hom p (Q.over i).symm).inv.app F) at hp
+        ((upperStarComp A (Q.smallModelLegs.app i) U.hom p
+          (Q.smallModelOver i).symm).inv.app F) at hp
   rw [hp]
   have hs : (etaleObjectSectionsIso U).hom.app F =
```

## Users

The read-only downstream.py search found 27 live downstream modules, listed below.
None is currently held by another group. The adapted consumers are compiled against the published dependencies. Additional
unchanged downstream sources were checked until the existing LocalizedHomGerm timeout;
that file has no use of the migrated geometry API and is preserved verbatim.
The new module is listed separately. The archived historical helper named by the old
retirement row is noted after the table.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.DerivedCohomologyGermIso | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeSourceTransport | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeTargetTransport | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry | unclaimed | New canonical transport API, all proofs complete. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturality | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturalityCore | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceLocalizedCocycleHomology | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceStageSectionsNaturality | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeGlobalSections | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceTransition | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | unclaimed | No source or signature edit; published dependency retained. An additional unchanged-source check exceeded 60 seconds. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalNeighbourhoodGeometryExistence | unclaimed | Publicly import the official structure module; reuse proved official existence theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalSectionsUnitLeray | unclaimed | No source edit; check existing proof against canonical geometry and changed consumers. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | unclaimed | Use transported cone legs and projection/limit equations; original cohomology objects preserved. |

| Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry | T6 | Assigned retirement; remove duplicate definitions and redirect DAG attachment. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | V8 | Quarantined parent; no source edit or weakening. Its unchanged continuity-presentation statement is preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceSections | unclaimed | Historical quarantined direct importer from the retirement row; current DAG attachment is the restored StrictLocalSmallModel module, adapted here. Archive remains untouched. |
| Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence | unclaimed | Historical retirement-row consumer; current DAG attachment and live consumer are StrictLocalSmallModel.StrictLocalNeighbourhoodGeometryExistence, adapted here. |

The source library is untouched. No target signature, definition of a cohomology object,
or definition of the strict-local mate is edited. The new API needs the closed-fibre
comparison node only as the general structural-map identity between the two models;
its closed-fibre corollary and that unit's proof route are not used.

The changed complex-mate proof also imports the adapted underived-mate module
explicitly: its cached factorization dependency does not expose the new bridge API.
This is a private proof import; no statement is changed by it.

## Reviewer correction (cc review, 2026-10-22)

The existence helper uses nothing of StrictLocalSmallModel.NeighbourhoodGeometry: its
signature needs only the official structure. Its public import is therefore
WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry, the two leftover
`set_option … in` lines before the theorem are removed, and the node
lem-weil-pbc-strict-local-neighbourhood-geometry no longer lists the transport node in
proof_deps. Its only importer, StrictLocalMateContinuityPresentation, imports
NeighbourhoodGeometry itself.

## Status

landed 20261021T214902-L-1880019 2026-10-21 (merge of deliver/T6/Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry)
