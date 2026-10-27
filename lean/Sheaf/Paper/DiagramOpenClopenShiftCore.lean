/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Mathlib.CategoryTheory.Shift.Adjunction
import all Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import all Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift
import Sheaf.CategoryTheory.DerivedCategory.DerivedMateComparison
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import all Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift

/-! # Open and clopen shift models on whole semilinear systems

Source: Stacks Project, Tags 03DI, 03DJ, 04TQ--04TS, 015F, 070H and 07A6;
blueprint `fix-prop-coherence`, maps-used sentence
(blueprint: lem-pur-diagram-open-clopen-shift-models).

The maps are the existing proper/open calculus maps. Representatives are natural
transformations of whole systems, localized through the standard factorizations.
The right-derived shift is the existing K-injective shift, rather than a shift
transported along a clopen isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a av aw b bv bw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The specified exact termwise inverse-image shift. Source: Stacks 015F
(blueprint: lem-pur-diagram-open-clopen-shift-models). -/
instance pullShift {X Y : Scheme.{u}} (v : X ⟶ Y) : (P C τ v).CommShift ℤ :=
  inferInstanceAs ((pull C τ v).mapDerivedCategory.CommShift ℤ)

/-- The specified exact termwise extension shift. Source: Stacks 015F, 03DJ
(blueprint: lem-pur-diagram-open-clopen-shift-models). -/
instance extensionShift {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (J C τ j).CommShift ℤ :=
  inferInstanceAs ((extension C τ j).mapDerivedCategory.CommShift ℤ)

/-- The specified K-injective right-derived shift. Source: Stacks 070H, 07A6
(blueprint: lem-pur-diagram-open-clopen-shift-models). -/
instance directShift {X Y : Scheme.{u}} (v : X ⟶ Y) : (R C τ v).CommShift ℤ :=
  inferInstanceAs ((push C τ v).rightDerivedFunctor.CommShift ℤ)

/-- A simultaneous termwise representative, with its actual localization equation,
complex shift square and degree formula. Source: Stacks 015F, 04VG
(blueprint: lem-pur-diagram-open-clopen-shift-models).
The equation is on the whole system localization; it does not use evaluation to
infer equality of morphisms. `shiftedDegree` uses heterogeneous equality only to
identify the canonically equal indices `r + p` and `p + r`. -/
structure TermwiseModel
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{aw} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{bw} B]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (t : F.mapDerivedCategory ⟶ G.mapDerivedCategory) where
  /-- A natural map of whole ordinary systems, hence compatible with all transitions. -/
  ordinary : F ⟶ G
  /-- Localization is precisely the specified derived map. -/
  localizes : ∀ K : CochainComplex A ℤ,
    t.app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary (.up ℤ)).app K)
  /-- The degree-p map is the ordinary map on the degree-p system. -/
  degree : ∀ (K : CochainComplex A ℤ) (p : ℤ),
    ((NatTrans.mapHomologicalComplex ordinary (.up ℤ)).app K).f p = ordinary.app (K.X p)
  /-- Shifting the input reindexes precisely the same system map. -/
  shiftedDegree : ∀ (K : CochainComplex A ℤ) (r p : ℤ),
    HEq (((NatTrans.mapHomologicalComplex ordinary (.up ℤ)).app (K⟦r⟧)).f p)
      (((NatTrans.mapHomologicalComplex ordinary (.up ℤ)).app K).f (p + r))
  /-- Compatibility with the signed complex differential and all integer shifts. -/
  complexShift : NatTrans.CommShift (NatTrans.mapHomologicalComplex ordinary (.up ℤ)) ℤ

/-- The canonical restriction identification, using the extension compositor and
the inverse open unit of b. Source: Stacks 03DI; blueprint maps-used sentence
(blueprint: lem-pur-diagram-open-clopen-shift-models). -/
def restrictionIso {U V' V : Scheme.{u}} (s : U ⟶ V') (b : V' ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    J C τ (s ≫ b) ⋙ P C τ b ≅ J C τ s :=
  Functor.isoWhiskerRight (jComp C τ s b).symm (P C τ b) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (J C τ s)
      (@asIso _ _ _ _ (jAdj C τ b).unit (jAdj_unit_isIso C τ b)).symm ≪≫
    Functor.rightUnitor _

/-- Ordinary and complex models of c and beta with their normalized adjuncts.
Source: Stacks 03DI, 03DJ, 015F; blueprint maps-used sentence
(blueprint: lem-pur-diagram-open-clopen-shift-models). -/
structure OpenModels {U V' V : Scheme.{u}} (s : U ⟶ V') (b : V' ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion b] where
  /-- The canonical transitivity map, represented before localization. -/
  compositor : TermwiseModel (extension C τ s ⋙ extension C τ b)
    (extension C τ (s ≫ b))
    ((Functor.mapDerivedCategoryCompIso _ _).hom ≫ (jComp C τ s b).hom)
  /-- The ordinary map is precisely the open-adjoint compositor. -/
  compositor_normalization : compositor.ordinary =
    (Adjunction.leftAdjointCompIso (ordinaryOpenAdj C τ s) (ordinaryOpenAdj C τ b)
      (ordinaryOpenAdj C τ (s ≫ b)) (pullComp C τ s b).symm).hom
  /-- On U the ordinary compositor is identity under the normalized open units. -/
  ordinary_compositor_identity : ∀ N : Modules C τ U,
    (ordinaryOpenAdj C τ s).unit.app N ≫
      (pull C τ s).map ((ordinaryOpenAdj C τ b).unit.app ((extension C τ s).obj N)) ≫
      (pull C τ s).map ((pull C τ b).map (compositor.ordinary.app N)) =
    (ordinaryOpenAdj C τ (s ≫ b)).unit.app N ≫
      (pullComp C τ s b).hom.app ((extension C τ (s ≫ b)).obj N)
  /-- The same identity normalization after localization. -/
  compositor_identity : ∀ N : Derived C τ U,
    (jAdj C τ s).unit.app N ≫
      (P C τ s).map ((jAdj C τ b).unit.app ((J C τ s).obj N)) ≫
      (P C τ s).map ((P C τ b).map ((jComp C τ s b).hom.app N)) =
    (jAdj C τ (s ≫ b)).unit.app N ≫
      (pComp C τ s b).hom.app ((J C τ (s ≫ b)).obj N)
  /-- The ordinary restriction identification. -/
  ordinaryRestriction : extension C τ (s ≫ b) ⋙ pull C τ b ≅ extension C τ s
  /-- A termwise representative of the same specified derived beta. -/
  restriction : TermwiseModel (extension C τ (s ≫ b) ⋙ pull C τ b) (extension C τ s)
    ((Functor.mapDerivedCategoryCompIso _ _).hom ≫ (restrictionIso C τ s b).hom)
  /-- Its ordinary representative is the preceding isomorphism. -/
  restriction_ordinary : restriction.ordinary = ordinaryRestriction.hom
  /-- The inverse is exactly the prescribed normalized open-unit adjunct. -/
  ordinary_adjunct : ∀ N : Modules C τ U,
    (ordinaryOpenAdj C τ s).homEquiv _ _ (ordinaryRestriction.inv.app N) =
      (ordinaryOpenAdj C τ (s ≫ b)).unit.app N ≫
        (pullComp C τ s b).hom.app ((extension C τ (s ≫ b)).obj N)
  /-- This is also the specified adjunct after localization. -/
  derived_adjunct : ∀ N : Derived C τ U,
    (jAdj C τ s).homEquiv _ _ ((restrictionIso C τ s b).inv.app N) =
      (jAdj C τ (s ≫ b)).unit.app N ≫
        (pComp C τ s b).hom.app ((J C τ (s ≫ b)).obj N)
  /-- Identity restriction to U under the open-unit identifications. -/
  restriction_identity : ∀ N : Derived C τ U,
    (jAdj C τ (s ≫ b)).unit.app N ≫
      (pComp C τ s b).hom.app ((J C τ (s ≫ b)).obj N) ≫
      (P C τ s).map ((restrictionIso C τ s b).hom.app N) =
        (jAdj C τ s).unit.app N
  /-- On an open disjoint from U the transitivity map is the zero map. -/
  compositor_zero : ∀ {T : Scheme.{u}} (t : T ⟶ V) [IsOpenImmersion t],
    Disjoint (Set.range t) (Set.range (s ≫ b)) → ∀ N : Modules C τ U,
      (pull C τ t).map (compositor.ordinary.app N) = 0
  /-- The compositor commutes with the composite operation shifts. -/
  compositor_shift : NatTrans.CommShift (jComp C τ s b).hom ℤ
  /-- The restriction identification commutes with the composite operation shifts. -/
  restriction_shift : NatTrans.CommShift (restrictionIso C τ s b).hom ℤ

/-- Clopen product models and the actual comparison and component projector.
The complement is any open immersion with complementary image, so in particular
it can be the canonical complementary open subscheme. Source: Stacks 04TQ--04TS,
03DI, 015F; blueprint maps-used sentence
(blueprint: lem-pur-diagram-open-clopen-shift-models). -/
structure ClopenModels {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (hpush : PreservesFiniteColimits (push C τ s)) where
  /-- Restriction gives the ordinary product decomposition of whole systems. -/
  ordinary : Modules C τ X ≌ Modules C τ U × Modules C τ Z
  /-- Both components are the specified inverse images. -/
  ordinaryRestriction : ordinary.functor ≅ (pull C τ s).prod' (pull C τ z)
  /-- Extension is zero insertion under this decomposition. -/
  ordinaryInsertion : extension C τ s ⋙ ordinary.functor ≅
    (𝟭 (Modules C τ U)).prod' ((Functor.const (Modules C τ U)).obj (0 : Modules C τ Z))
  /-- On the U component the insertion is the inverse normalized open unit. -/
  ordinaryInsertion_unit : ∀ N : Modules C τ U,
    (ordinaryOpenAdj C τ s).unit.app N ≫
      (ordinaryRestriction.inv.app ((extension C τ s).obj N) ≫
        ordinaryInsertion.hom.app N).1 = 𝟙 N
  /-- Ordinary direct image is the very same exact zero insertion. -/
  direct : extension C τ s ≅ push C τ s
  /-- Its transpose is the inverse normalized open unit. -/
  direct_adjunct : ∀ N : Modules C τ U,
    ((ordinaryAdj C τ s).homEquiv _ _).symm (direct.hom.app N) ≫
      (ordinaryOpenAdj C τ s).unit.app N = 𝟙 _
  /-- Delta is localized from the exact direct-image comparison, on every complex. -/
  comparison : TermwiseModel (extension C τ s) (push C τ s)
    (openToS C τ s ≫ (push C τ s).rightDerivedFunctorIsoMapDerivedCategory.hom)
  /-- The representative is the normalized ordinary comparison. -/
  comparison_ordinary : comparison.ordinary = direct.hom
  /-- A termwise model of the actual projector used in the proper/open square. -/
  projection : TermwiseModel (𝟭 (Modules C τ X)) (pull C τ s ⋙ extension C τ s)
    ((Functor.mapDerivedCategoryIdIso _).hom ≫ pi C τ s ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv)
  /-- Its composite with delta is the ordinary direct-image unit. -/
  projection_unit : projection.ordinary ≫
    Functor.whiskerLeft (pull C τ s) direct.hom = (ordinaryAdj C τ s).unit
  /-- The ordinary projection has exactly the section-pair formula (x,y) -> (x,0). -/
  ordinary_projection : ∀ M : Modules C τ X,
    ordinary.functor.map (projection.ordinary.app M) ≫
      ordinaryInsertion.hom.app ((pull C τ s).obj M) =
    ordinaryRestriction.hom.app M ≫
      Prod.mkHom (𝟙 ((pull C τ s).obj M))
        (0 : (pull C τ z).obj M ⟶ (0 : Modules C τ Z))
  /-- The product decomposition extends to unbounded ordinary complexes. -/
  complexes : CochainComplex (Modules C τ X) ℤ ≌
    CochainComplex (Modules C τ U) ℤ × CochainComplex (Modules C τ Z) ℤ
  /-- This is termwise restriction, including the differentials. -/
  complexRestriction : complexes.functor ≅
    ((pull C τ s).mapHomologicalComplex (.up ℤ)).prod'
      ((pull C τ z).mapHomologicalComplex (.up ℤ))
  /-- The product decomposition extends to the ordinary unbounded derived categories. -/
  derived : Derived C τ X ≌ Derived C τ U × Derived C τ Z
  /-- The derived functor is exactly restriction to the two components. -/
  derivedRestriction : derived.functor ≅ (P C τ s).prod' (P C τ z)
  /-- Extension remains zero insertion after localization. -/
  derivedInsertion : J C τ s ⋙ derived.functor ≅
    (𝟭 (Derived C τ U)).prod' ((Functor.const (Derived C τ U)).obj (0 : Derived C τ Z))
  /-- On the U component the derived insertion is the inverse normalized open unit. -/
  derivedInsertion_unit : ∀ N : Derived C τ U,
    (jAdj C τ s).unit.app N ≫
      (derivedRestriction.inv.app ((J C τ s).obj N) ≫
        derivedInsertion.hom.app N).1 = 𝟙 N
  /-- The actual derived projector is the component projection. -/
  derived_projection : ∀ M : Derived C τ X,
    derived.functor.map ((pi C τ s).app M) ≫
      derivedInsertion.hom.app ((P C τ s).obj M) =
    derivedRestriction.hom.app M ≫
      Prod.mkHom (𝟙 ((P C τ s).obj M))
        (0 : (P C τ z).obj M ⟶ (0 : Derived C τ Z))
  /-- Delta commutes with the specified K-injective/mate shift on R_s. -/
  comparison_shift : NatTrans.CommShift (openToS C τ s) ℤ
  /-- The component projector commutes with the composite shifts. -/
  projection_shift : NatTrans.CommShift (pi C τ s) ℤ

/-- All section models simultaneously, without coefficient flatness, cartesianness,
boundedness, constructibility, or exclusion of the empty open.
Source: Stacks 03DI, 03DJ, 04TS, 015F, 070H and 07A6; blueprint maps-used sentence
(blueprint: lem-pur-diagram-open-clopen-shift-models). -/
structure Models where
  /-- K-injective shifts agree with the mates of the fixed exact pullback shifts. -/
  direct_adjunction_shift : ∀ {X Y : Scheme.{u}} (v : X ⟶ Y), (adj C τ v).CommShift ℤ
  /-- Open models for every composable pair, including empty and identity opens. -/
  opens : ∀ {U V' V : Scheme.{u}} (s : U ⟶ V') (b : V' ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion b], OpenModels C τ s b
  /-- Clopen models for every complementary pair, with exact termwise direct image. -/
  clopens : ∀ {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z],
    Set.range z = (Set.range s)ᶜ →
      ∃ hpush : PreservesFiniteColimits (push C τ s), Nonempty (ClopenModels C τ s z hpush)
  /-- Iterated open composition is coherent before evaluation or scalar restriction. -/
  composition_assoc : ∀ {U V X Y : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X) (d : X ⟶ Y)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion d] (M : Derived C τ U),
    (J C τ d).map ((jComp C τ s b).hom.app M) ≫ (jComp C τ (s ≫ b) d).hom.app M =
      (jComp C τ b d).hom.app ((J C τ s).obj M) ≫
        (jComp C τ s (b ≫ d)).hom.app M ≫
        (jCongr C τ (Category.assoc s b d)).inv.app M
  /-- The left identity immersion gives the identity transitivity comparison. -/
  composition_left_unit : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    (M : Derived C τ U),
    (jComp C τ (𝟙 U) s).hom.app M ≫
      (jCongr C τ (Category.id_comp s)).hom.app M =
        (J C τ s).map ((jId C τ U).hom.app M)
  /-- The right identity immersion gives the identity transitivity comparison. -/
  composition_right_unit : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    (M : Derived C τ U),
    (jComp C τ s (𝟙 X)).hom.app M ≫
      (jCongr C τ (Category.comp_id s)).hom.app M =
        (jId C τ X).hom.app ((J C τ s).obj M)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

section ExactModels

variable
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{aw} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{bw} B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private def termwiseMapModel (α : F ⟶ G) (t : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
    (ht : ∀ K : CochainComplex A ℤ,
      t.app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
        F.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K)) :
    TermwiseModel F G t where
  ordinary := α
  localizes := ht
  degree := by intros; rfl
  shiftedDegree := by intros; rfl
  complexShift := inferInstance

private def termwiseIsoModel (e : F ≅ G)
    (t : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
    (ht : t = (Functor.mapDerivedCategoryNatIso e).hom) : TermwiseModel F G t :=
  termwiseMapModel e.hom t (by rw [ht]; exact Functor.mapDerivedCategoryNatIso_fac e)

end ExactModels

private theorem openComp_unit
    {A B D : Type*} [Category A] [Category B] [Category D]
    {L : A ⥤ B} {P : B ⥤ A} {M : B ⥤ D} {Q : D ⥤ B}
    {N : A ⥤ D} {R : D ⥤ A}
    (a : L ⊣ P) (b : M ⊣ Q) (c : N ⊣ R) (e : R ≅ Q ⋙ P) (X : A) :
    a.unit.app X ≫ P.map (b.unit.app (L.obj X)) ≫
      P.map (Q.map ((Adjunction.leftAdjointCompIso a b c e.symm).hom.app X)) =
        c.unit.app X ≫ e.hom.app (N.obj X) := by
  simpa only [Adjunction.comp_unit_app, Category.assoc, Functor.comp_map,
    Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans, Iso.symm_inv] using
    (unit_conjugateEquiv_symm c (a.comp b) e.hom X).symm

section ShiftCompositors
variable {A B D : Type*} [Category A] [Category B] [Category D]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
  {L : A ⥤ B} {P : B ⥤ A} {M : B ⥤ D} {Q : D ⥤ B}
  {N : A ⥤ D} {R : D ⥤ A}
  [L.CommShift ℤ] [P.CommShift ℤ] [M.CommShift ℤ] [Q.CommShift ℤ]
  [N.CommShift ℤ] [R.CommShift ℤ]

private theorem leftAdjointComp_shift
    (a : L ⊣ P) (b : M ⊣ Q) (c : N ⊣ R)
    [a.CommShift ℤ] [b.CommShift ℤ] [c.CommShift ℤ]
    (e : R ≅ Q ⋙ P) [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (Adjunction.leftAdjointCompIso a b c e.symm).hom ℤ := by
  have he : (Adjunction.leftAdjointCompIso a b c e.symm).hom =
      (Functor.leftUnitor (L ⋙ M)).inv ≫
        Functor.whiskerRight c.unit (L ⋙ M) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft N (Functor.whiskerRight e.hom (L ⋙ M)) ≫
        Functor.whiskerLeft N (a.comp b).counit ≫
        (Functor.rightUnitor N).hom := by
    ext X
    simp [Adjunction.leftAdjointCompIso_hom_app]
  rw [he]
  infer_instance
end ShiftCompositors

section ExactAdjunctionModels

universe x y z
variable {A B D : Type x} [Category.{y} A] [Category.{y} B] [Category.{y} D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B] [HasDerivedCategory.{z} D]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  preservesBinaryBiproducts_of_preservesBinaryProducts

private theorem factors_comp (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).hom.app
    (DerivedCategory.Q.obj K))).mp
  rw [Iso.hom_inv_id_app_assoc]
  exact (Functor.mapDerivedCategoryCompIso_hom_app_factors F G K).symm

private def compositeFactors (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ≅
      (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    (F ⋙ G).mapDerivedCategoryFactors

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem factors_comp_inv (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex A ℤ) :
    (compositeFactors F G).inv.app K =
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  apply (cancel_mono ((compositeFactors F G).hom.app K)).mp
  rw [Iso.inv_hom_id_app]
  change 𝟙 _ = (_ ≫ _) ≫
    ((Functor.mapDerivedCategoryCompIso F G).inv.app _ ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K)
  rw [factors_comp]
  simp only [Category.assoc]
  erw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

private theorem exact_hom_fac
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    a.mapExactDerivedCategory.homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app L := by
  have hu : a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, G.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp]
  have hn := G.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_comp_hom_fac
    {L : A ⥤ B} {P : B ⥤ A} {M : B ⥤ D} {Q : D ⥤ B}
    [L.Additive] [P.Additive] [M.Additive] [Q.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (a : L ⊣ P) (b : M ⊣ Q) (K : CochainComplex A ℤ) (H : CochainComplex D ℤ)
    (f : ((L ⋙ M).mapHomologicalComplex (.up ℤ)).obj K ⟶ H) :
    (a.mapExactDerivedCategory.comp b.mapExactDerivedCategory).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj H)
        ((Functor.mapDerivedCategoryCompIso L M).inv.app (DerivedCategory.Q.obj K) ≫
          (L ⋙ M).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (((a.comp b).mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        (P.mapDerivedCategoryFactors.inv.app ((Q.mapHomologicalComplex (.up ℤ)).obj H) ≫
          P.mapDerivedCategory.map (Q.mapDerivedCategoryFactors.inv.app H)) := by
  rw [← Category.assoc, factors_comp]
  rw [Adjunction.comp_homEquiv]
  change a.mapExactDerivedCategory.homEquiv _ _
    (b.mapExactDerivedCategory.homEquiv _ _ _) = _
  erw [Category.assoc, b.mapExactDerivedCategory.homEquiv_naturality_left,
    exact_hom_fac b, ← Category.assoc,
    a.mapExactDerivedCategory.homEquiv_naturality_right, exact_hom_fac a]
  simp only [Category.assoc]
  congr 2
  ext p
  simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
    Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.comp_unit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 50000 in
-- Keep this localization calculation below the usual declaration heartbeat budget.
private theorem exact_compositor_localizes
    {L : A ⥤ B} {P : B ⥤ A} {M : B ⥤ D} {Q : D ⥤ B}
    {N : A ⥤ D} {R : D ⥤ A}
    [L.Additive] [P.Additive] [M.Additive] [Q.Additive] [N.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ P) (b : M ⊣ Q) (c : N ⊣ R) (e : R ≅ Q ⋙ P)
    (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso L M).hom.app (DerivedCategory.Q.obj K) ≫
      (Adjunction.leftAdjointCompIso a.mapExactDerivedCategory b.mapExactDerivedCategory
        c.mapExactDerivedCategory
        (Functor.mapDerivedCategoryNatIso e ≪≫
          Functor.mapDerivedCategoryCompIso Q P).symm).hom.app (DerivedCategory.Q.obj K) ≫
      N.mapDerivedCategoryFactors.hom.app K =
    (L ⋙ M).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (Adjunction.leftAdjointCompIso a b c e.symm).hom (.up ℤ)).app K) := by
  let d := Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso Q P
  let f := (Adjunction.leftAdjointCompIso a b c e.symm).hom
  have hh := derivedMate_comparison
    (G := 𝟭 (CochainComplex A ℤ)) (H := 𝟭 (CochainComplex D ℤ))
    (GD := 𝟭 (DerivedCategory A)) (HD := 𝟭 (DerivedCategory D))
    (c.mapHomologicalComplex (.up ℤ)) ((a.comp b).mapHomologicalComplex (.up ℤ))
    c.mapExactDerivedCategory (a.mapExactDerivedCategory.comp b.mapExactDerivedCategory)
    N.mapDerivedCategoryFactors.hom (compositeFactors L M).hom
    R.mapDerivedCategoryFactors (compositeFactors Q P)
    (Iso.refl DerivedCategory.Q) (Iso.refl DerivedCategory.Q)
    (exact_hom_fac c)
    (by
      intro K H f
      rw [factors_comp_inv]
      simpa only [compositeFactors, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
        Category.assoc] using exact_comp_hom_fac a b K H f)
    (TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex e.hom (.up ℤ)))
    (TwoSquare.mk _ _ _ _ d.hom)
    (by
      intro H
      simpa [d, compositeFactors, Category.assoc] using
        Functor.mapDerivedCategoryNatIso_fac e H)
    (NatTrans.mapHomologicalComplex f (.up ℤ))
    (by
      intro H
      ext p
      simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
        Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
        Adjunction.comp_unit_app,
        NatTrans.mapHomologicalComplex_app_f, Functor.comp_map, Functor.id_map]
      change (a.unit.app (H.X p) ≫ P.map (b.unit.app (L.obj (H.X p)))) ≫
        P.map (Q.map (f.app (H.X p))) = c.unit.app (H.X p) ≫
          e.hom.app (N.obj (H.X p))
      simpa only [f, Category.assoc] using openComp_unit a b c e (H.X p)) K
  have hh' := congrArg (fun q ↦
    (Functor.mapDerivedCategoryCompIso L M).hom.app (DerivedCategory.Q.obj K) ≫ q) hh
  simpa [d, f, compositeFactors, Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans, Category.assoc] using hh'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_unit_fac
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex A ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have hu : a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [hu]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_homotopy_unit_fac
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : HomotopyCategory A (.up ℤ)) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    F.mapDerivedCategoryFactorsh_hom_app, G.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.comp_obj, HomotopyCategory.quotient_obj_as]
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc]
  erw [← a.mapExactDerivedCategory.unit.naturality_assoc]
  simp only [Functor.id_map, ← G.mapDerivedCategory.map_comp_assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [reassoc_of% exact_unit_fac a K]
  erw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

private theorem exactAdj_eq
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    a.mapExactDerivedCategory = VaryingRing.exactAdj a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
    G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
  exact (exact_homotopy_unit_fac a K).trans (VaryingRing.exactAdj_unit a K).symm

private theorem iso_comp_localizes
    {R : D ⥤ A} {Q : D ⥤ B} {P : B ⥤ A}
    [R.Additive] [Q.Additive] [P.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : R ≅ Q ⋙ P) (K : CochainComplex D ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryCompIso Q P).hom.app (DerivedCategory.Q.obj K) ≫
      P.mapDerivedCategory.map (Q.mapDerivedCategoryFactors.hom.app K) ≫
      P.mapDerivedCategoryFactors.hom.app ((Q.mapHomologicalComplex (.up ℤ)).obj K) =
    R.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  exact Functor.mapDerivedCategoryNatIso_fac e K

private theorem localized_id_map_fac
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : 𝟭 A ⟶ F ⋙ G) (K : CochainComplex A ℤ)
    (hi : (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K) :
    ((Functor.mapDerivedCategoryIdIso A).inv ≫ VaryingRing.derivedMap α ≫
        (Functor.mapDerivedCategoryCompIso F G).hom).app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K) := by
  dsimp only [NatTrans.comp_app]
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors F G K,
    VaryingRing.derivedMap_fac α K, ← hi]
  change (Functor.mapDerivedCategoryIdIso A).inv.app (DerivedCategory.Q.obj K) ≫
    (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K) = _
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_restriction_localizes
    {N : A ⥤ D} {R : D ⥤ A} {L : A ⥤ B} {P : B ⥤ A} (Q : D ⥤ B)
    [N.Additive] [R.Additive] [L.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (a : N ⊣ R) (c : L ⊣ P) (e : R ≅ Q ⋙ P) (t : L ⟶ N ⋙ Q)
    (ht : ∀ X, c.homEquiv _ _ (t.app X) = a.unit.app X ≫ e.hom.app (N.obj X))
    (d : L.mapDerivedCategory ⟶ N.mapDerivedCategory ⋙ Q.mapDerivedCategory)
    (hd : ∀ X, c.mapExactDerivedCategory.homEquiv _ _ (d.app X) =
      a.mapExactDerivedCategory.unit.app X ≫
        (Functor.mapDerivedCategoryNatIso e ≪≫
          Functor.mapDerivedCategoryCompIso Q P).hom.app (N.mapDerivedCategory.obj X))
    (K : CochainComplex A ℤ) :
    d.app (DerivedCategory.Q.obj K) ≫
      Q.mapDerivedCategory.map (N.mapDerivedCategoryFactors.hom.app K) ≫
      Q.mapDerivedCategoryFactors.hom.app ((N.mapHomologicalComplex (.up ℤ)).obj K) =
    L.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := by
  let w := TwoSquare.mk R.mapDerivedCategory Q.mapDerivedCategory
    (𝟭 (DerivedCategory A)) P.mapDerivedCategory
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso Q P).hom
  have he : ((mateEquiv a.mapExactDerivedCategory c.mapExactDerivedCategory).symm w).natTrans
      = d := by
    ext X
    apply (c.mapExactDerivedCategory.homEquiv _ _).injective
    rw [hd]
    exact (unit_mateEquiv_symm a.mapExactDerivedCategory c.mapExactDerivedCategory w X).symm
  have h := derivedMate_comparison
    (G := 𝟭 (CochainComplex A ℤ)) (H := Q.mapHomologicalComplex (.up ℤ))
    (GD := 𝟭 (DerivedCategory A)) (HD := Q.mapDerivedCategory)
    (a.mapHomologicalComplex (.up ℤ)) (c.mapHomologicalComplex (.up ℤ))
    a.mapExactDerivedCategory c.mapExactDerivedCategory
    N.mapDerivedCategoryFactors.hom L.mapDerivedCategoryFactors.hom
    R.mapDerivedCategoryFactors P.mapDerivedCategoryFactors
    (Iso.refl DerivedCategory.Q) Q.mapDerivedCategoryFactors
    (exact_hom_fac a) (exact_hom_fac c)
    (TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex e.hom (.up ℤ))) w
    (by
      intro H
      dsimp only [w, TwoSquare.mk, Functor.id_map, Iso.refl_hom, NatTrans.id_app]
      change _ = R.mapDerivedCategoryFactors.hom.app H ≫ 𝟙 _ ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app H)
      erw [Category.id_comp]
      exact iso_comp_localizes e H)
    (NatTrans.mapHomologicalComplex t (.up ℤ))
    (by
      intro H
      ext p
      simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
        Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f, Functor.id_map]
      exact ht (H.X p)) K
  change ((mateEquiv a.mapExactDerivedCategory c.mapExactDerivedCategory).symm w).natTrans.app _
    ≫ _ ≫ _ = _ at h
  rw [he] at h
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  dsimp only [Functor.id_obj] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

end ExactAdjunctionModels

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift
