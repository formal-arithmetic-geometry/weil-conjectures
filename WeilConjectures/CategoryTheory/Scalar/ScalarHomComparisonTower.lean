/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final

/-! # Evaluation-defined scalar Hom comparisons in coefficient towers

Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 07A4, and the formal
coefficient-tower argument in the proof of the blueprint node
(blueprint: lem-pur-scalar-hom-comparison-tower).

The comparison is the existing `WeilConjectures.coefficientBaseChangeHom`.
It uses evaluation on Hom tensor P, the symmetry-equivalent convention of the
node's P tensor Hom. The tensor comparisons are normalized on K-flat complexes.
Only tensor-tower and identity equations are assumed; Hom maps need not be invertible.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v r w

open CategoryTheory Opposite WeilConjectures SheafOfModules

namespace CategoryTheory

private theorem scalarEvaluation_naturality
    {D : Type*} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem scalarBaseChangeHom_naturality
    {A : Type*} {B : Type*} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P Q P' Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ P' Q' =
      coefficientBaseChangeHom SA SB F μ P Q ≫
        HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  let := SB.monoidal
  have hu (T P Q : B) (h : T ⟶ HB.obj (op P, Q)) :
      (SB.transpose T P Q).symm h =
        SB.tensor.map (Prod.mkHom h (𝟙 P)) ≫ SB.evaluation P Q := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      CoefficientClosedStructure.evaluation] using! (SB.adjunction P).homEquiv_counit T Q h
  apply (SB.transpose _ (F.obj P') (F.obj Q')).symm.injective
  rw [hu, hu]
  have tc {U V Z R : B} (a : U ⟶ V) (b : V ⟶ Z) :
      SB.tensor.map (Prod.mkHom (a ≫ b) (𝟙 R)) =
        SB.tensor.map (Prod.mkHom a (𝟙 R)) ≫ SB.tensor.map (Prod.mkHom b (𝟙 R)) := by
    rw [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  simp only [tc, Category.assoc]
  rw [scalarEvaluation_naturality SB _ _ _ _ (F.map f) (F.map g)]
  have beta (U V : A) :
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ U V) (𝟙 (F.obj U))) ≫
        SB.evaluation (F.obj U) (F.obj V) =
          μ.inv.app (HA.obj (op U, V), U) ≫ F.map (SA.evaluation U V) := by
    rw [← hu, coefficientBaseChangeHom, Equiv.symm_apply_apply]
  rw [beta]
  have hn := μ.inv.naturality (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 P'))
  have hn' := μ.inv.naturality (Prod.mkHom (𝟙 (HA.obj (op P, Q))) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hn'
  erw [F.map_id] at hn
  erw [F.map_id] at hn'
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, scalarEvaluation_naturality SA]
  rw [F.map_comp, F.map_comp]
  have ht : SB.tensor.map
      (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P'))) ≫
      SB.tensor.map (Prod.mkHom (𝟙 _) (F.map f)) =
    SB.tensor.map (Prod.mkHom (𝟙 _) (F.map f)) ≫
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P))) := by
    rw [← SB.tensor.map_comp, ← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% ht, reassoc_of% beta P Q, ← reassoc_of% hn']

private theorem scalarUncurry
    {D : Type*} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T P Q : D) (h : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm h =
      S.tensor.map (Prod.mkHom h (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q h

private theorem scalarTensor_comp
    {D : Type*} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y Z U V W : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : U ⟶ V) (k : V ⟶ W) :
    S.tensor.map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      S.tensor.map (Prod.mkHom f h) ≫ S.tensor.map (Prod.mkHom g k) :=
  S.tensor.map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem scalarUncurry_pre
    {D : Type*} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T U P Q : D}
    (f : T ⟶ U) (h : U ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm (f ≫ h) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose U P Q).symm h := by
  rw [scalarUncurry, scalarUncurry]
  simpa only [Category.id_comp, Category.assoc] using
    congrArg (fun k => k ≫ S.evaluation P Q) (scalarTensor_comp S f h (𝟙 P) (𝟙 P))

private theorem scalarUncurry_post
    {D : Type*} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T P Q P' Q' : D}
    (h : T ⟶ H.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    (S.transpose T P' Q').symm (h ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (S.transpose T P Q).symm h ≫ g := by
  rw [scalarUncurry_pre, scalarUncurry, scalarEvaluation_naturality]
  rw [scalarUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp

private theorem scalarBaseChangeHom_beta
    {A : Type*} {B : Type*} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    (SB.transpose _ (F.obj P) (F.obj Q)).symm (coefficientBaseChangeHom SA SB F μ P Q) =
      μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) :=
  Equiv.symm_apply_apply _ _

private theorem scalarBaseChangeHom_tower
    {A : Type*} {B : Type*} {D : Type c}
    [Category.{v} A] [Category.{w} B] [Category.{r} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D) (K : A ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (ξ : SA.tensor ⋙ K ≅ K.prod K ⋙ SD.tensor) (α : F ⋙ G ≅ K)
    (ht : ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
          SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (SA.tensor.obj (X, Y)) ≫ ξ.hom.app (X, Y)) (P Q : A) :
    G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SD G ν (F.obj P) (F.obj Q) ≫
        HD.map (Prod.mkHom (α.inv.app P).op (α.hom.app Q)) =
      α.hom.app (HA.obj (op P, Q)) ≫ coefficientBaseChangeHom SA SD K ξ P Q := by
  have hi (X Y : A) :
      ν.inv.app (F.obj X, F.obj Y) ≫ G.map (μ.inv.app (X, Y)) ≫
          α.hom.app (SA.tensor.obj (X, Y)) =
        SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫ ξ.inv.app (X, Y) := by
    apply (cancel_mono (ξ.hom.app (X, Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp [← G.map_comp, ← Category.assoc]
  have he : (SD.transpose _ (G.obj (F.obj P)) (G.obj (F.obj Q))).symm
      (G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SD G ν (F.obj P) (F.obj Q)) =
      ν.inv.app (F.obj (HA.obj (op P, Q)), F.obj P) ≫
        G.map (μ.inv.app (HA.obj (op P, Q), P)) ≫ G.map (F.map (SA.evaluation P Q)) := by
    rw [scalarUncurry_pre, scalarBaseChangeHom_beta]
    have hn := ν.inv.naturality
      (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P)))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    erw [G.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
    rw [← scalarUncurry, scalarBaseChangeHom_beta, G.map_comp]
  apply (SD.transpose _ (K.obj P) (K.obj Q)).symm.injective
  rw [← Category.assoc, scalarUncurry_post, he, scalarUncurry_pre,
    scalarBaseChangeHom_beta]
  have hn := α.hom.naturality (SA.evaluation P Q)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi (HA.obj (op P, Q)) P]
  rw [← Category.assoc, ← SD.tensor.map_comp]
  congr 2
  ext <;> simp

private theorem scalarBaseChangeHom_identity
    {A : Type*} [Category.{v} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (F : A ⥤ A)
    (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S.tensor) (u : F ≅ 𝟭 A)
    (hid : ∀ X Y : A,
      S.tensor.map (Prod.mkHom (u.inv.app X) (u.inv.app Y)) =
        u.inv.app (S.tensor.obj (X, Y)) ≫ μ.hom.app (X, Y)) (P Q : A) :
    coefficientBaseChangeHom S S F μ P Q ≫
        H.map (Prod.mkHom (u.inv.app P).op (u.hom.app Q)) =
      u.hom.app (H.obj (op P, Q)) := by
  have hi (X Y : A) : μ.inv.app (X, Y) ≫ u.hom.app (S.tensor.obj (X, Y)) =
      S.tensor.map (Prod.mkHom (u.hom.app X) (u.hom.app Y)) := by
    have : IsIso (S.tensor.map (Prod.mkHom (u.inv.app X) (u.inv.app Y))) := by
      change IsIso ((S.tensor.mapIso (Iso.prod (u.app X).symm (u.app Y).symm)).hom)
      infer_instance
    apply (cancel_epi (S.tensor.map (Prod.mkHom (u.inv.app X) (u.inv.app Y)))).1
    conv_lhs => rw [← Category.assoc, hid]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    rw [← S.tensor.map_comp]
    simp
  apply (S.transpose _ P Q).symm.injective
  rw [scalarUncurry_post, scalarBaseChangeHom_beta, scalarUncurry]
  have hn := u.hom.naturality (S.evaluation P Q)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi, ← Category.assoc, ← S.tensor.map_comp]
  congr 2
  ext <;> simp

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

end CategoryTheory
