/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHomDefinitions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison

/-! Comparison constructions for inverse image along a scheme isomorphism. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v s h
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))

@[irreducible] private noncomputable def reindexHomIso [B.IsEquivalence] :
    (pushforward₀OfCommRingCat.{max s h v} B R).obj (homObj M N) ≅
      homObj ((reindex B R).obj M) ((reindex B R).obj N) := by
  have : ∀ U, IsIso ((reindexHom B R M N).app U) := fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨reindexHom_injective B R M N U, reindexHom_surjective B R M N U⟩
  exact PresheafOfModules.isoMk
    (fun U ↦ asIso ((reindexHom B R M N).app U))
    (fun {_ _} f ↦ (reindexHom B R M N).naturality f)

end AlgebraicGeometry.Scheme.PurHom
namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (c : S ⟶ R) (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))

@[irreducible] private noncomputable def restrictHomIso [IsIso c] :
    (restrict.{u, max s h v} c).obj (homObj M N) ≅
      homObj ((restrict c).obj M) ((restrict c).obj N) := by
  have : ∀ U, IsIso ((restrictHom c M N).app U) := fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨restrictHom_injective c M N U, restrictHom_surjective c M N U⟩
  exact PresheafOfModules.isoMk
    (fun U ↦ asIso ((restrictHom c M N).app U))
    (fun {_ _} f ↦ (restrictHom c M N).naturality f)

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) [B.IsEquivalence] (R : Dᵒᵖ ⥤ CommRingCat.{u}) {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (c : S ⟶ B.op ⋙ R) [IsIso c]
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
@[irreducible] private noncomputable def pushHomIso :
    (PresheafOfModules.pushforward.{max s h v}
      (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj (homObj M N) ≅
      homObj
        ((PresheafOfModules.pushforward.{v}
          (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj M)
        ((PresheafOfModules.pushforward.{v}
          (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj N) :=
  (restrict.{u, max s h v} c).mapIso (reindexHomIso B R M N) ≪≫
    restrictHomIso c ((reindex B R).obj M) ((reindex B R).obj N)

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom

set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def sheafPushHomIso
    {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
    (B : C ⥤ D) [B.IsEquivalence]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [B.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
    (c : S ⟶ (B.sheafPushforwardContinuous CommRingCat.{u} J K).obj R) [IsIso c]
    (M N : SheafOfModules.{v} ((sheafCompose K
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    let p : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S ⟶
        (B.sheafPushforwardContinuous RingCat.{u} J K).obj
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
      ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩
    (SheafOfModules.pushforward.{max s h v} p).obj
        (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := S)
        ((SheafOfModules.pushforward.{v} p).obj M)
        ((SheafOfModules.pushforward.{v} p).obj N) := by
  let c₀ : S.obj ⟶ B.op ⋙ R.obj := c.hom
  have : IsIso c₀ := (sheafToPresheaf J CommRingCat.{u}).map_isIso c
  let e := pushHomIso B R.obj c₀ M.val N.val
  dsimp only
  let p : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S ⟶
      (B.sheafPushforwardContinuous RingCat.{u} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩
  exact liftIso
    (M := (SheafOfModules.pushforward.{max s h v} p).obj
      (SheafOfModules.homObj (R := R) M N))
    (N := SheafOfModules.homObj (R := S)
      ((SheafOfModules.pushforward.{v} p).obj M)
      ((SheafOfModules.pushforward.{v} p).obj N)) e

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
section GenericAdjunction
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) [B.IsEquivalence]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [B.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
  (c : S ⟶ (B.sheafPushforwardContinuous CommRingCat.{u} J K).obj R) [IsIso c]
variable (L : SheafOfModules.{max s h u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{max s h u} ((sheafCompose K
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  (adj : L ⊣ (SheafOfModules.pushforward.{max s h u} (F := B) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩))
  (hunit : ∀ M, IsIso (adj.unit.app M))
  [hreflect : ((SheafOfModules.pushforward.{max s h u} (F := B) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩)).ReflectsIsomorphisms]

@[irreducible] private noncomputable def genericPushComparison
    (M N : SheafOfModules.{max s h u} (targetRing K R)) :
    (push B J K R S c).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := S)
        ((push B J K R S c).obj M) ((push B J K R S c).obj N) :=
  sheafPushHomIso B J K R S c M N

@[irreducible] private noncomputable def unitIso (M : SheafOfModules.{max s h u} (sourceRing J S)) :
    M ≅ (push B J K R S c).obj (L.obj M) := by
  exact @asIso (SheafOfModules.{max s h u} (sourceRing J S)) _ M
    ((push B J K R S c).obj (L.obj M))
    (adj.unit.app M) (hunit M)

@[irreducible] private noncomputable def homUnit
    (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    SheafOfModules.homObj (R := S) F G ≅
      (push B J K R S c).obj (SheafOfModules.homObj
        (R := R)
        (L.obj F)
        (L.obj G)) :=
  homCongr S (unitIso B J K R S c L adj hunit F) (unitIso B J K R S c L adj hunit G) ≪≫
    (genericPushComparison B J K R S c _ _).symm

@[irreducible] private noncomputable def comparisonMap
    (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    L.obj (SheafOfModules.homObj (R := S) F G) ⟶
      SheafOfModules.homObj
        (R := R)
        (L.obj F)
        (L.obj G) :=
  (adj.homEquiv _ _).symm (homUnit B J K R S c L adj hunit F G).hom

@[irreducible] private noncomputable def comparisonIso
    (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    L.obj (SheafOfModules.homObj (R := S) F G) ≅
      SheafOfModules.homObj
        (R := R)
        (L.obj F)
        (L.obj G) := by
  have hi := @mate_isIso _ _ _ _ L (push B J K R S c)
    adj (inferInstance : (push B J K R S c).ReflectsIsomorphisms)
    (SheafOfModules.homObj (R := S) F G)
    (SheafOfModules.homObj
      (R := R)
      (L.obj F) (L.obj G))
    (hunit (SheafOfModules.homObj (R := S) F G)) (homUnit B J K R S c L adj hunit F G)
  exact @asIso _ _ _ _ (comparisonMap B J K R S c L adj hunit F G) (by
    unfold comparisonMap
    exact hi)

end GenericAdjunction
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
