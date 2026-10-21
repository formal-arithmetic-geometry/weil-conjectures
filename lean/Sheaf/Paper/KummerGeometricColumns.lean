/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerResolutionColumns
public import Sheaf.Paper.KummerTermMate
public import Sheaf.Paper.KummerNerveCoordinates

/-! # Actual maps of resolved geometric nerve columns
Source: direct-image proof (3), full-root counit and puncture unit.
(blueprint: def-sfb-kummer-geometric-columns).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual n-th simplex followed by the original open immersion.
Source: direct-image proof (3), punctured covering nerve
(blueprint: def-sfb-kummer-geometric-columns). -/
abbrev kummerNerveToBase {T W U : Scheme.{u}} (a : W ⟶ U) (v : T ⟶ W) (n : ℕ) :=
  ((cechOver v).obj (op (.mk n))).hom ≫ a

/-- Evaluation of the resolved actual Cech diagram leaves its module term unchanged.
Source: direct-image proof (3), coherent column
(blueprint: def-sfb-kummer-geometric-columns).
Proof: expand evaluation and mapping a complex by a functor. Both sides are the
same inverse image of the two successive direct images of the nerve pullback. -/
theorem kummerCechColumn_term {T W U S : Scheme.{u}}
    (a : W ⟶ U) (s : S ⟶ U) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ) (n q : ℕ) :
    (kummerDiagramColumn Λ S
      (kummerCechResolution Λ a s v I) n).X q =
        cechImageTerm Λ a s v (I.X q) (.mk n) := by
  sorry


/-- The unique comparison fixed termwise by the direct-image composition isomorphism.
Source: direct-image proof (3), resolved actual nerve columns
(blueprint: def-sfb-kummer-geometric-columns).
Proof: the n-th evaluated diagram has terms s* a* vn* vn* Iq. Apply
lowerStarComp to the middle two direct images, and then s*. Naturality of this
isomorphism gives a chain isomorphism. The displayed components determine a chain
map uniquely, hence determine the chain isomorphism uniquely. -/
theorem kummerCechColumnComposition_existsUnique {T W U S : Scheme.{u}}
    (a : W ⟶ U) (s : S ⟶ U) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ) (n : ℕ) :
    ∃! e : kummerDiagramColumn Λ S
        (kummerCechResolution Λ a s v I) n ≅
      ((upperStar Λ ((cechOver v).obj (op (.mk n))).hom ⋙
        lowerStar Λ (kummerNerveToBase a v n) ⋙ upperStar Λ s).mapHomologicalComplex
          (.up ℕ)).obj I,
      ∀ q : ℕ, e.hom.f q =
        eqToHom (kummerCechColumn_term Λ a s v I n q) ≫
          (upperStar Λ s).map
            ((lowerStarComp Λ ((cechOver v).obj (op (.mk n))).hom a).hom.app
              ((upperStar Λ ((cechOver v).obj (op (.mk n))).hom).obj (I.X q))) := by
  sorry


/-- The composition comparison selected from its uniquely specified actual components.
Source: direct-image proof (3), resolved nerve column
(blueprint: def-sfb-kummer-geometric-columns). -/
def kummerCechColumnComposition {T W U S : Scheme.{u}}
    (a : W ⟶ U) (s : S ⟶ U) (v : T ⟶ W)
    (I : CochainComplex (KummerModules Λ W) ℕ) (n : ℕ) :
    kummerDiagramColumn Λ S
        (kummerCechResolution Λ a s v I) n ≅
      ((upperStar Λ ((cechOver v).obj (op (.mk n))).hom ⋙
        lowerStar Λ (kummerNerveToBase a v n) ⋙ upperStar Λ s).mapHomologicalComplex
          (.up ℕ)).obj I :=
  (kummerCechColumnComposition_existsUnique Λ a s v I n).choose


/-- The resolved Cech column comparison uses the actual right-derived unit.
Source: direct-image proof (3), resolved nerve term
(blueprint: def-sfb-kummer-geometric-columns). -/
def kummerCechColumnMap {T W U S : Scheme.{u}}
    (a : W ⟶ U) (s : S ⟶ U) (v : T ⟶ W)
    {L : KummerModules Λ W} (I : InjectiveResolution L) (n : ℕ) :
    DerivedCategory.Q.obj
        ((kummerDiagramColumn Λ S
          (kummerCechResolution Λ a s v I.cocomplex) n).extend
            ComplexShape.embeddingUpNat) ⟶
      (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ (kummerNerveToBase a v n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar Λ ((cechOver v).obj (op (.mk n))).hom).obj L))) :=
  DerivedCategory.Q.map
      (HomologicalComplex.extendMap (kummerCechColumnComposition Λ a s v I.cocomplex n).hom
        ComplexShape.embeddingUpNat) ≫
    kummerImageColumnMap Λ ((cechOver v).obj (op (.mk n))).hom
      (kummerNerveToBase a v n) s I


/-- A specified full-root term comparison retains both actual maps: the inverse
open unit and the pulled-back direct-image counit. Invertibility is asserted for
this comparison, without replacing either canonical arrow.
Source: direct-image proof (3), full root term calculation
(blueprint: def-sfb-kummer-geometric-columns). -/
structure KummerGeometricTerm {V T U B S : Scheme.{u}}
    (j : V ⟶ T) (q : T ⟶ U) (i : B ⟶ T) (π : B ⟶ S) (s : S ⟶ U)
    (w : i ≫ q = π ≫ s) (N : DerivedCategory (KummerModules Λ T)) where
  comparison : (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ (j ≫ q)).obj
          ((upperStar Λ j).mapDerivedCategory.obj N)) ≅
      (moduleObjectDerivedPushforward Λ π).obj
        ((upperStar Λ i).mapDerivedCategory.obj N)
  normalization : IsKummerTermComparison Λ j q i π s w N comparison

end AlgebraicGeometry.ProEtale.CondensedRing
