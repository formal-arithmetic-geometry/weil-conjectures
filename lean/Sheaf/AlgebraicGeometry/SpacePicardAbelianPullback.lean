module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.CategoryTheory.Sites.RingedSitePicardData
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Abelian inverse image for the small affine etale models

Source: Stacks Project, Tags 03G2, 03H7, 039Z and 03AJ
(blueprint: def-sfb-space-picard-abelian-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.RingedSitePicard
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- Mathlib's small-Ext construction from enough injectives on the small affine site.
Source: Stacks 01FT (blueprint: def-sfb-space-picard-abelian-pullback). -/
instance picardSmallHasExt (X : AlgebraicSpace S) :
    HasExt.{u} (Sheaf X.smallEtaleModelTopology AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives _

/-- Literal restriction to the existing affine basis. Source: Stacks 039Z
(blueprint: def-sfb-space-picard-abelian-pullback). -/
def picardAbRestriction (X : AlgebraicSpace S) :
    Sheaf X.etaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleModelTopology AddCommGrpCat.{u} :=
  X.smallEtaleInclusion.sheafPushforwardContinuous _ _ _

/-- Restriction to either basis is an equivalence for abelian sheaves.
Source: Stacks 039Z and 03H7 (blueprint: def-sfb-space-picard-abelian-pullback).
Proof: every chart is covered by affine scheme charts, and their overlaps have the
same refinements. Extend by compatible families. Unique gluing makes restriction
and extension inverse. Addition and zero glue componentwise, so the set-sheaf
comparison lifts to abelian sheaves without increasing the coefficient universe. -/
theorem picardAbRestriction_equivalences (X : AlgebraicSpace S) :
    (picardAbRestriction X).IsEquivalence ∧
      (enlargedRestriction X AddCommGrpCat.{u}).IsEquivalence := by
  sorry

/-- The equivalence whose forward functor is literal affine restriction.
Source: Stacks 039Z (blueprint: def-sfb-space-picard-abelian-pullback). -/
def picardAbEquivalence (X : AlgebraicSpace S) :=
  @Functor.asEquivalence _ _ _ _ (picardAbRestriction X)
    (picardAbRestriction_equivalences X).1

/-- The equivalence whose forward functor is literal scheme restriction.
Source: Stacks 03H7 (blueprint: def-sfb-space-picard-abelian-pullback). -/
def picardEnlargedAbEquivalence (X : AlgebraicSpace S) :=
  @Functor.asEquivalence _ _ _ _ (enlargedRestriction X AddCommGrpCat.{u})
    (picardAbRestriction_equivalences X).2

/-- Direct image is evaluation on fibre products, transported through the two bases.
Source: Stacks 03G2 (blueprint: def-sfb-space-picard-abelian-pullback). -/
def picardAbDirect {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf X.smallEtaleModelTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleModelTopology AddCommGrpCat.{u} :=
  (picardAbEquivalence X).inverse ⋙ (picardEnlargedAbEquivalence X).inverse ⋙
    enlargedDirectImage f AddCommGrpCat.{u} ⋙
      (picardEnlargedAbEquivalence Y).functor ⋙ (picardAbEquivalence Y).functor

/-- Pull a direct-image section back on a compatible pair of actual affine charts.
Source: Stacks 03G2 and 03G8 (blueprint: def-sfb-space-picard-abelian-pullback). -/
def picardAbDirectChart {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleModelTopology AddCommGrpCat.{u})
    (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (a : (X.smallEtaleInclusion.obj U).obj.left ⟶ (Y.smallEtaleInclusion.obj V).obj.left)
    (ha : yoneda.map a ≫ (Y.smallEtaleInclusion.obj V).obj.hom =
      (X.smallEtaleInclusion.obj U).obj.hom ≫ f.hom.hom) :
    ((picardAbDirect f).obj F).obj.obj (op V) ⟶ F.obj.obj (op U) :=
  ((picardEnlargedAbEquivalence X).inverse.obj
      ((picardAbEquivalence X).inverse.obj F)).obj.map
        (enlargedChartLift f _ _ a ha).op ≫
    ((picardEnlargedAbEquivalence X).counitIso.hom.app
      ((picardAbEquivalence X).inverse.obj F)).hom.app
        (op (X.smallEtaleInclusion.obj U)) ≫
    ((picardAbEquivalence X).counitIso.hom.app F).hom.app (op U)

/-- An exact inverse image, adjoint to the specified direct image. The integer
comparison preserves the local section 1 under the adjunction unit on every pair
of charts. Thus its induced Ext map is the usual derived global-sections pullback.
Source: Stacks 03AJ and 03G2 (blueprint: def-sfb-space-picard-abelian-pullback). -/
structure PicardAbInverse {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
  functor : Sheaf Y.smallEtaleModelTopology AddCommGrpCat.{u} ⥤
    Sheaf X.smallEtaleModelTopology AddCommGrpCat.{u}
  adj : functor ⊣ picardAbDirect f
  additive : functor.Additive
  finiteLimits : PreservesFiniteLimits functor
  finiteColimits : PreservesFiniteColimits functor
  integers : RingedSitePicard.integers.{u} X.smallEtaleModelTopology ≅
    functor.obj (RingedSitePicard.integers.{u} Y.smallEtaleModelTopology)
  one (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (a : (X.smallEtaleInclusion.obj U).obj.left ⟶ (Y.smallEtaleInclusion.obj V).obj.left)
    (ha : yoneda.map a ≫ (Y.smallEtaleInclusion.obj V).obj.hom =
      (X.smallEtaleInclusion.obj U).obj.hom ≫ f.hom.hom) :
    integers.hom.hom.app (op U) (integerOne.{u} (op U)) =
      picardAbDirectChart f _ U V a ha
        ((adj.unit.app _).hom.app (op V) (integerOne.{u} (op V)))

attribute [instance] PicardAbInverse.additive PicardAbInverse.finiteLimits
  PicardAbInverse.finiteColimits

/-- The unit section on a compatible pair of affine charts.
Source: Stacks 03AJ (blueprint: def-sfb-space-picard-abelian-pullback). -/
def PicardAbInverse.chartSection {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (P : PicardAbInverse f) (F : Sheaf Y.smallEtaleModelTopology AddCommGrpCat.{u})
    (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (a : (X.smallEtaleInclusion.obj U).obj.left ⟶ (Y.smallEtaleInclusion.obj V).obj.left)
    (ha : yoneda.map a ≫ (Y.smallEtaleInclusion.obj V).obj.hom =
      (X.smallEtaleInclusion.obj U).obj.hom ≫ f.hom.hom) :
    F.obj.obj (op V) ⟶ (P.functor.obj F).obj.obj (op U) :=
  (P.adj.unit.app F).hom.app (op V) ≫ picardAbDirectChart f _ U V a ha

/-- Exact-functor transport on Ext, normalized by the integer section 1.
Source: Stacks 03AJ (blueprint: def-sfb-space-picard-abelian-pullback). -/
def PicardAbInverse.cohomology {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (P : PicardAbInverse f)
    [HasExt.{u} (Sheaf X.smallEtaleModelTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf Y.smallEtaleModelTopology AddCommGrpCat.{u})]
    (F : Sheaf Y.smallEtaleModelTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H F n →+ Sheaf.H (P.functor.obj F) n :=
  ((Ext.mk₀ P.integers.hom).precomp _ (zero_add n)).comp
    (P.functor.mapExtAddHom _ F n)

end AlgebraicGeometry.AlgebraicSpace
