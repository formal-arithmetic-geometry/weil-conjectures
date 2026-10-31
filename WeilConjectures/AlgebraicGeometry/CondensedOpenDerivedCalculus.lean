/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.AlgebraicGeometry.CondensedPullbackTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

public import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
import WeilConjectures.CategoryTheory.DerivedCategory.ExactFunctorCoproducts
import WeilConjectures.AlgebraicGeometry.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionNormalization
import all WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionSuccessive
import all WeilConjectures.CategoryTheory.CompactSupportIdentityCalculus
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!
# Ordinary derived open localization for internal condensed modules

Source: Stacks Project, cohomology.tex, Tag 08BU; sites-cohomology.tex, Tags 08FI,
0D6G and 08JB; sites-modules.tex, open extension by zero
(blueprint: lem-pod-condensed-open-derived-calculus).

Every functor below acts on the ordinary unbounded derived category of the existing
internal module objects over `condensedRingObj Λ T`. The helpers construct only the
canonical comparisons and the prescribed arrows of this node's two-open triangle.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

set_option synthInstance.maxSize 4096

namespace AlgebraicGeometry.ProEtale.CondensedRing.OpenDerivedCalculus

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The extension square is the mate of the actual coefficient-compatible pullback square.
Its component is the transpose of pullback of the open unit followed by that square.
Source: sites-modules.tex, Tags 03DI and 03DJ
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def extensionSquare {S T SU U : Scheme.{u}}
    {f : S ⟶ T} {j : U ⟶ T} {fU : SU ⟶ U} {i : SU ⟶ S}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq i fU f j) :
    D(upperStar Λ fU) ⋙ D(openImmersionLowerShriek Λ i) ⟶
      D(openImmersionLowerShriek Λ j) ⋙ D(upperStar Λ f) :=
  ((mateEquiv (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i)).symm
      (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).hom)).natTrans

/-- Restriction along a specified factorization of open inclusions, using the existing
coefficient compositor. Source: cohomology.tex, Tag 08BU
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def restrictionFactorization {W U T : Scheme.{u}} (v : W ⟶ U) (j : U ⟶ T)
    (k : W ⟶ T) (h : k = v ≫ j) :
    D(upperStar Λ k) ≅ D(upperStar Λ j) ⋙ D(upperStar Λ v) :=
  Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (upperStar Λ) h)) ≪≫
    openCoherenceRestrictionComp Λ v j

/-- The nested-open counit map is the transpose of the restricted open unit.
Source: cohomology.tex, Tag 08BU
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def nestedCounit {W U T : Scheme.{u}} (v : W ⟶ U) (j : U ⟶ T) (k : W ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : k = v ≫ j)
    (K : DerivedCategory (supportModules Λ T)) :
    D(openImmersionLowerShriek Λ k).obj (D(upperStar Λ k).obj K) ⟶
      D(openImmersionLowerShriek Λ j).obj (D(upperStar Λ j).obj K) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ k).homEquiv _ _).symm
    ((restrictionFactorization Λ v j k h).hom.app K ≫
      D(upperStar Λ v).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app
          (D(upperStar Λ j).obj K)) ≫
      (restrictionFactorization Λ v j k h).inv.app
        (D(openImmersionLowerShriek Λ j).obj (D(upperStar Λ j).obj K)))

/-- Termwise open extension and restriction are exact, preserve every small coproduct,
and have their specified adjunction with invertible unit.
Source: sites-modules.tex, Tags 03DI, 03DJ, 04BG and 04BH
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: identify module inverse image with slice restriction using the invertible alpha.
The abelian extension and restriction are exact; coefficient transport preserves this.
Apply exact termwise derivation and localization to the specified module adjunction.
Its unit is invertible by open full faithfulness. Both underived functors are left
adjoints and preserve small coproducts. The module categories are Grothendieck abelian
and have K-injectives; lem-pur-exact-derived-coproducts passes these coproducts through
localization. No completeness, constructibility or Tor hypothesis is used. -/
theorem openLocalization {U T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] :
    D(openImmersionLowerShriek Λ j).IsTriangulated ∧
    D(upperStar Λ j).IsTriangulated ∧
    (∀ I : Type (u + 1),
      PreservesColimitsOfShape (Discrete I) D(openImmersionLowerShriek Λ j)) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) D(upperStar Λ j)) ∧
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · intro I
    exact Functor.mapDerivedCategory_preservesCoproducts (openImmersionLowerShriek Λ j) I
  · intro I
    exact Functor.mapDerivedCategory_preservesCoproducts (upperStar Λ j) I
  · infer_instance

/-- The K-flat pullback square, transported from the exact termwise square by the
specified universal derived comparisons. Source: sites-modules.tex, open base change
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def pullbackSquare {S T SU U : Scheme.{u}}
    {f : S ⟶ T} {j : U ⟶ T} {fU : SU ⟶ U} {i : SU ⟶ S}
    (sq : CommSq i fU f j) :
    moduleObjectDerivedPullback Λ f ⋙ D(upperStar Λ i) ≅
      D(upperStar Λ j) ⋙ moduleObjectDerivedPullback Λ fU :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f) _ ≪≫
    (derivedOpenCoherencePullbackSquare Λ sq).symm ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ fU).symm

/-- The extension square on total K-flat pullbacks, with the same unit normalization.
Source: sites-modules.tex, Tags 03DI and 03DJ
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def totalExtensionSquare {S T SU U : Scheme.{u}}
    {f : S ⟶ T} {j : U ⟶ T} {fU : SU ⟶ U} {i : SU ⟶ S}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq i fU f j) :
    moduleObjectDerivedPullback Λ fU ⋙ D(openImmersionLowerShriek Λ i) ⟶
      D(openImmersionLowerShriek Λ j) ⋙ moduleObjectDerivedPullback Λ f :=
  (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ fU) _).hom ≫
    extensionSquare Λ sq ≫
    (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm).hom

private theorem exactAdjunctionShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ := by
  let a := upperStarLowerStarAdjunction Λ f
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ f
  have hd : a.derivedAdjunction =
      a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft e.symm := by
    have hf := Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac (upperStar Λ f)
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _ e hf.symm
  have he : a.mapDerivedCategoryRightDerivedAdjunction =
      a.derivedAdjunction.ofNatIsoLeft e := by
    apply Adjunction.ext
    rw [hd]
    ext M
    simp [Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp, Category.assoc]
  change a.mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ
  rw [he]
  exact Adjunction.commShift_ofNatIsoLeft (derivedUpperStarLowerStarAdjunction Λ f) e

/-- The three Cartesian open comparisons, with the actual coefficient and adjunction
normalizations, and their compatibility with integer shifts.
Source: sites-cohomology.tex, Tags 08FI and 0D6G; sites-modules.tex, open base change
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: the direct-image clause is `derivedOpenRestrictionNormalization`. The extension
square is the inverse mate of the exact pullback square; its component at `K` is
`i_! f_U^*(η_j)`, then `i_!` of the pullback square, then the counit `ε_i` at
`f^* j_! K`. That counit is invertible by the derived open base-change counit theorem
of the source library, applied to the flipped Cartesian square and transported along
the exact derived composition isomorphism; the other two factors are isomorphisms,
so the extension square is invertible. For shifts, the exact left-derived adjunction
equals the native derived adjunction transported along the exact pullback comparison
(`Adjunction.derived_eq_ofNatIsoLeft`), so it commutes with shifts, and the mate-shift
law gives the direct-image restriction; the inverse mate, the pullback square and
their conjugates by the exact comparisons commute with shifts by composition. -/
theorem openSquare {S T SU U : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    {f : S ⟶ T} {j : U ⟶ T} {fU : SU ⟶ U} {i : SU ⟶ S}
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (sq : IsPullback i fU f j) :
    DirectImageRestrictionNormalized Λ sq.toCommSq ∧
    IsIso (extensionSquare Λ sq.toCommSq) ∧
    NatTrans.CommShift (extensionSquare Λ sq.toCommSq) ℤ ∧
    NatTrans.CommShift (derivedDirectImageOpenRestriction Λ sq.toCommSq) ℤ ∧
    NatTrans.CommShift (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).hom ℤ ∧
    NatTrans.CommShift
      (F₁ := (upperStar Λ f).leftDerivedFunctor ⋙ D(upperStar Λ i))
      (F₂ := D(upperStar Λ j) ⋙ (upperStar Λ fU).leftDerivedFunctor)
      (pullbackSquare Λ sq.toCommSq).hom ℤ ∧
    IsIso (totalExtensionSquare Λ sq.toCommSq) ∧
    NatTrans.CommShift
      (F₁ := (upperStar Λ fU).leftDerivedFunctor ⋙ D(openImmersionLowerShriek Λ i))
      (F₂ := D(openImmersionLowerShriek Λ j) ⋙ (upperStar Λ f).leftDerivedFunctor)
      (totalExtensionSquare Λ sq.toCommSq) ℤ := by
  have hsq : NatTrans.CommShift
      (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).hom ℤ := by
    dsimp only [derivedOpenCoherencePullbackSquare]
    infer_instance
  have hj : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have hi : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).commShift_mapDerivedCategoryAdjunction
  have hext : IsIso (extensionSquare Λ sq.toCommSq) := by
    have hK (K : DerivedCategory (supportModules Λ U)) :
        IsIso ((extensionSquare Λ sq.toCommSq).app K) := by
      have hd := isIso_derivedCounit_app_upperStar_obj_openImmersionLowerShriek
        Λ sq.flip K
      let e := (Functor.mapDerivedCategoryCompIso
        (openImmersionLowerShriek Λ j) (upperStar Λ f)).symm.app K
      have hc : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).counit.app
          (D(upperStar Λ f).obj (D(openImmersionLowerShriek Λ j).obj K))) :=
        (NatTrans.isIso_app_iff_of_iso _ e).mpr hd
      simp only [extensionSquare, mateEquiv_symm_apply, TwoSquare.mk,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.comp_map, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
        Functor.associator_inv_app, Functor.associator_hom_app,
        Category.id_comp]
      dsimp only [TwoSquare.natTrans, Functor.comp_obj]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      refine IsIso.comp_isIso' inferInstance
        (IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hc ?_))
      exact IsIso.id _
    exact NatIso.isIso_of_isIso_app _
  have hextShift : NatTrans.CommShift (extensionSquare Λ sq.toCommSq) ℤ := by
    dsimp only [extensionSquare, mateEquiv, Equiv.symm, Equiv.coe_fn_mk, TwoSquare.natTrans]
    infer_instance
  refine ⟨derivedOpenRestrictionNormalization Λ sq, hext, hextShift, ?_, hsq, ?_, ?_, ?_⟩
  · have : (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction.CommShift
        ℤ := exactAdjunctionShift Λ f
    have : (upperStarLowerStarAdjunction Λ fU).mapDerivedCategoryRightDerivedAdjunction.CommShift
        ℤ := exactAdjunctionShift Λ fU
    unfold derivedDirectImageOpenRestriction
    exact NatTrans.CommShift.mateEquiv _ _ _
  · dsimp only [pullbackSquare]
    infer_instance
  · dsimp only [totalExtensionSquare]
    infer_instance
  · dsimp only [totalExtensionSquare]
    infer_instance

/-- The native K-flat tensor comparison transported to exact termwise restriction.
Source: sites-cohomology.tex, Tags 08J9 and 08JB
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def tensorRestriction {U T : Scheme.{u}} (j : U ⟶ T)
    (K L : DerivedCategory (supportModules Λ T)) :
    D(upperStar Λ j).obj (K ⊗ L) ≅
      D(upperStar Λ j).obj K ⊗ D(upperStar Λ j).obj L :=
  ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app (K ⊗ L)).symm ≪≫
    (((leftDerivedUpperStarTensorIso Λ j).app K).app L) ≪≫
    tensorIso ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app K)
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app L)

/-- The closed comparison is the native evaluation transpose, transported by the exact
pullback comparison in all three places. Source: sites-cohomology.tex, Tag 08JB
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def homRestriction {U T : Scheme.{u}} (j : U ⟶ T)
    (K L : DerivedCategory (supportModules Λ T)) :
    D(upperStar Λ j).obj (((derivedHom Λ T).obj (op K)).obj L) ⟶
      ((derivedHom Λ U).obj (op (D(upperStar Λ j).obj K))).obj
        (D(upperStar Λ j).obj L) :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app _ ≫
    (Functor.LaxMonoidal.ihomComparison (upperStar Λ j).leftDerivedFunctor K).natTrans.app L ≫
    (MonoidalClosed.pre ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app K)).app _ ≫
    ((derivedHom Λ U).obj (op (D(upperStar Λ j).obj K))).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app L)

section ClosedTransport
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  (F G : C ⥤ D) [F.LaxMonoidal] (e : F ≅ G)
open MonoidalClosed

private def transported (K L : C) : G.obj ((ihom K).obj L) ⟶
    (ihom (G.obj K)).obj (G.obj L) :=
  e.inv.app _ ≫ (Functor.LaxMonoidal.ihomComparison F K).natTrans.app L ≫
    (pre (e.inv.app K)).app _ ≫ (ihom (G.obj K)).map (e.hom.app L)
private theorem natural_right (K L L' : C) (b : L ⟶ L') :
    G.map ((ihom K).map b) ≫ transported F G e K L' =
      transported F G e K L ≫ (ihom (G.obj K)).map (G.map b) := by
  let t : ihom K ⋙ G ⟶ G ⋙ ihom (G.obj K) :=
    Functor.whiskerLeft _ e.inv ≫
      (Functor.LaxMonoidal.ihomComparison F K).natTrans ≫
      Functor.whiskerLeft F (pre (e.inv.app K)) ≫
      Functor.whiskerRight e.hom _
  exact t.naturality b
private theorem natural_left (K K' L : C) (a : K' ⟶ K) :
    G.map ((pre a).app L) ≫ transported F G e K' L =
      transported F G e K L ≫ (pre (G.map a)).app (G.obj L) := by
  unfold transported
  rw [e.inv.naturality_assoc,
    Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app_assoc]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc]
  rw [← NatTrans.comp_app_assoc, ← pre_map,
    ← e.inv.naturality, pre_map, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [← (pre (G.map a)).naturality,
    ← (pre (e.inv.app K)).naturality_assoc]
omit [MonoidalClosed C] [MonoidalClosed D] [F.LaxMonoidal] in
private theorem tensor_natural
    (t : curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj F ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (K K' L L' : C) (a : K ⟶ K') (b : L ⟶ L') :
    F.map (a ⊗ₘ b) ≫ (t.app K').hom.app L' =
      (t.app K).hom.app L ≫ (F.map a ⊗ₘ F.map b) := by
  have h := (CategoryTheory.Functor.uncurry.map t.hom).naturality (Prod.mkHom a b)
  change (F.map (a ▷ L) ≫ F.map (K' ◁ b)) ≫ (t.app K').hom.app L' =
    (t.app K).hom.app L ≫ ((F.map a ▷ F.obj L) ≫ (F.obj K' ◁ F.map b)) at h
  simpa only [← F.map_comp, ← MonoidalCategory.tensorHom_def, Category.assoc] using h

omit [MonoidalClosed C] [MonoidalClosed D] [F.LaxMonoidal] in
private theorem tensor_transport_natural
    (t : curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj F ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (K K' L L' : C) (a : K ⟶ K') (b : L ⟶ L') :
    G.map (a ⊗ₘ b) ≫
      (e.inv.app (K' ⊗ L') ≫ (t.app K').hom.app L' ≫
        (e.hom.app K' ⊗ₘ e.hom.app L')) =
      (e.inv.app (K ⊗ L) ≫ (t.app K).hom.app L ≫
        (e.hom.app K ⊗ₘ e.hom.app L)) ≫ (G.map a ⊗ₘ G.map b) := by
  rw [e.inv.naturality_assoc, reassoc_of% (tensor_natural F t K K' L L' a b)]
  simp only [Category.assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    e.hom.naturality, e.hom.naturality, MonoidalCategory.tensorHom_comp_tensorHom]

end ClosedTransport

/-- Restriction of relative derived tensor and closed Hom, naturally in both inputs.
Source: sites-cohomology.tex, Tags 08J9, 08JB and 08JC
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: the native internal-Hom comparison of the derived pullback along an open
immersion is invertible (`isIso_ihomComparison_leftDerivedUpperStar_of_isOpenImmersion`);
`homRestriction` conjugates it by the invertible exact pullback comparison, a
precomposition by an isomorphism and covariant internal-Hom functoriality, so it is
invertible. The tensor comparison is the native derived tensor isomorphism conjugated by
the exact comparison; naturality of the uncurried native transformation and of the
comparison give its two-variable naturality. For Hom, naturality in the target is
naturality of the composite transformation and naturality in the source follows from
`map_pre_app_comp_ihomComparison_app` and `pre_map`; the two compose to the stated
identity. No finite Tor amplitude or boundedness is assumed. -/
theorem tensorHom {U T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K L : DerivedCategory (supportModules Λ T), IsIso (homRestriction Λ j K L)) ∧
    (∀ (K K' L L' : DerivedCategory (supportModules Λ T)) (a : K ⟶ K') (b : L ⟶ L'),
      D(upperStar Λ j).map (a ⊗ₘ b) ≫ (tensorRestriction Λ j K' L').hom =
        (tensorRestriction Λ j K L).hom ≫
          (D(upperStar Λ j).map a ⊗ₘ D(upperStar Λ j).map b)) ∧
    (∀ (K K' L L' : DerivedCategory (supportModules Λ T)) (a : K' ⟶ K) (b : L ⟶ L'),
      D(upperStar Λ j).map
          (((derivedHom Λ T).map a.op).app L ≫ ((derivedHom Λ T).obj (op K')).map b) ≫
        homRestriction Λ j K' L' =
      homRestriction Λ j K L ≫
        ((derivedHom Λ U).map (D(upperStar Λ j).map a).op).app _ ≫
        ((derivedHom Λ U).obj (op (D(upperStar Λ j).obj K'))).map
          (D(upperStar Λ j).map b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K L
    have := isIso_ihomComparison_leftDerivedUpperStar_of_isOpenImmersion Λ j K
    have : IsIso ((MonoidalClosed.pre
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app K)).app
          ((upperStar Λ j).leftDerivedFunctor.obj L)) := by
      change IsIso ((MonoidalClosed.internalHom.map
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app K).op).app _)
      infer_instance
    unfold homRestriction
    infer_instance
  · intro K K' L L' a b
    exact tensor_transport_natural (upperStar Λ j).leftDerivedFunctor
      D(upperStar Λ j) (leftDerivedUpperStarIsoMapDerivedCategory Λ j)
      (leftDerivedUpperStarTensorIso Λ j) K K' L L' a b
  · intro K K' L L' a b
    have e : ∀ K L, homRestriction Λ j K L = transported (upperStar Λ j).leftDerivedFunctor
        D(upperStar Λ j) (leftDerivedUpperStarIsoMapDerivedCategory Λ j) K L := fun _ _ => rfl
    have h1 : D(upperStar Λ j).map ((MonoidalClosed.internalHom.obj (op K')).map b) ≫
        transported (upperStar Λ j).leftDerivedFunctor D(upperStar Λ j)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ j) K' L' =
        transported (upperStar Λ j).leftDerivedFunctor D(upperStar Λ j)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ j) K' L ≫
          (MonoidalClosed.internalHom.obj (op (D(upperStar Λ j).obj K'))).map
            (D(upperStar Λ j).map b) :=
      natural_right (upperStar Λ j).leftDerivedFunctor D(upperStar Λ j)
        (leftDerivedUpperStarIsoMapDerivedCategory Λ j) K' L L' b
    have h2 := natural_left (upperStar Λ j).leftDerivedFunctor D(upperStar Λ j)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ j) K K' L a
    simp only [e, derivedHom, MonoidalClosed.internalHom_map, Quiver.Hom.unop_op,
      Functor.map_comp, Category.assoc, h1]
    rw [reassoc_of% h2]

/-- Successive open restrictions and extension exchanges agree with their direct
comparisons; the comparison maps include all coefficient and adjunction transports.
Source: sites-cohomology.tex, Tags 08FI, 0D6G and 08JB
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: the direct-image clause is `derivedOpenRestrictionSuccessive`. The exact
pullback square of the pasted square, after the two restriction compositors, is the
pasting of the two exact pullback squares (`exactSquare_horiz`). The mate-pasting
calculation `push_pasting_canonical` for the four open adjunctions and their composites
then identifies the extension square of the pasted square, preceded by the extension
compositor `mateOpenExtensionComp`, with the pasting of the two extension squares
followed by the compositor; cancelling the invertible target compositor gives the
stated identity. -/
theorem successiveSquares {S T SU U SW W : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    {f : S ⟶ T} {j : U ⟶ T} {fU : SU ⟶ U} {i : SU ⟶ S}
    {v : W ⟶ U} {fW : SW ⟶ W} {w : SW ⟶ SU}
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    [IsOpenImmersion v] [QuasiCompact v] [IsOpenImmersion w]
    (sq : IsPullback i fU f j) (sq' : IsPullback w fW fU v) :
    DirectImageSuccessiveRestriction Λ sq.toCommSq sq'.toCommSq ∧
    (∀ K : DerivedCategory (supportModules Λ W),
      (extensionSquare Λ (sq'.toCommSq.horiz_comp sq.toCommSq)).app K =
        (mateOpenExtensionComp Λ w i).inv.app (D(upperStar Λ fW).obj K) ≫
          D(openImmersionLowerShriek Λ i).map ((extensionSquare Λ sq'.toCommSq).app K) ≫
          (extensionSquare Λ sq.toCommSq).app (D(openImmersionLowerShriek Λ v).obj K) ≫
          D(upperStar Λ f).map ((mateOpenExtensionComp Λ v j).hom.app K)) := by
  refine ⟨derivedOpenRestrictionSuccessive Λ sq sq', ?_⟩
  have hc : Functor.whiskerRight (exactSquare Λ sq.toCommSq).hom D(upperStar Λ w) ≫
        Functor.whiskerLeft D(upperStar Λ j) (exactSquare Λ sq'.toCommSq).hom ≫
        Functor.whiskerRight (openCoherenceRestrictionComp Λ v j).inv
          D(upperStar Λ fW) =
      Functor.whiskerLeft D(upperStar Λ f) (openCoherenceRestrictionComp Λ w i).inv ≫
        (exactSquare Λ (sq'.toCommSq.horiz_comp sq.toCommSq)).hom := by
    ext M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [exactSquare_horiz Λ sq.toCommSq sq'.toCommSq]
    rw [exactComp_eq, exactComp_eq]
    simp only [Iso.inv_hom_id_app_assoc]
  have hp := WeilConjectures.CompactSupportCondensedRealization.push_pasting_canonical
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (v ≫ j))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ w)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (w ≫ i))
    (exactSquare Λ sq'.toCommSq) (exactSquare Λ sq.toCommSq)
    (exactSquare Λ (sq'.toCommSq.horiz_comp sq.toCommSq))
    (openCoherenceRestrictionComp Λ v j) (openCoherenceRestrictionComp Λ w i) hc
  intro K
  have h := hp K
  simp only [exactSquare_eq, Iso.symm_inv, Adjunction.pushHomOfComapIso] at h
  change (mateOpenExtensionComp Λ w i).hom.app (D(upperStar Λ fW).obj K) ≫
      (extensionSquare Λ (sq'.toCommSq.horiz_comp sq.toCommSq)).app K = _ at h
  change (mateOpenExtensionComp Λ w i).hom.app (D(upperStar Λ fW).obj K) ≫
      (extensionSquare Λ (sq'.toCommSq.horiz_comp sq.toCommSq)).app K =
    D(openImmersionLowerShriek Λ i).map ((extensionSquare Λ sq'.toCommSq).app K) ≫
      (extensionSquare Λ sq.toCommSq).app (D(openImmersionLowerShriek Λ v).obj K) ≫
      D(upperStar Λ f).map ((mateOpenExtensionComp Λ v j).hom.app K) at h
  rw [← h]
  simp only [Iso.inv_hom_id_app_assoc]


section SuccessiveMonoidal

@[instance_reducible]
private def exactMonoidal {U T : Scheme.{u}} (j : U ⟶ T) :
    D(upperStar Λ j).Monoidal :=
  Functor.Monoidal.transport (leftDerivedUpperStarIsoMapDerivedCategory Λ j)

attribute [local instance] exactMonoidal

private theorem exactComparisonMonoidal {U T : Scheme.{u}} (j : U ⟶ T) :
    NatTrans.IsMonoidal (leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom := by
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro K L
  rw [Functor.Monoidal.transport_δ]
  simp only [Iso.hom_inv_id_app_assoc]

attribute [local instance] exactComparisonMonoidal

private theorem tensorRestriction_eq {U T : Scheme.{u}} (j : U ⟶ T)
    (K L : DerivedCategory (supportModules Λ T)) :
    (tensorRestriction Λ j K L).hom = Functor.OplaxMonoidal.δ D(upperStar Λ j) K L := by
  rw [Functor.Monoidal.transport_δ]
  rfl

private theorem homRestriction_eq {U T : Scheme.{u}} (j : U ⟶ T)
    (K L : DerivedCategory (supportModules Λ T)) :
    homRestriction Λ j K L =
      (Functor.LaxMonoidal.ihomComparison D(upperStar Λ j) K).natTrans.app L := by
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ j
  have h := Functor.LaxMonoidal.ihomComparison_app_comp_map_app e.inv K L
  apply (cancel_mono ((ihom (D(upperStar Λ j).obj K)).map
    (e.inv.app L))).mp
  dsimp only [homRestriction, derivedHom, MonoidalClosed.internalHom, e]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

private theorem nativeCompMonoidal {W U T : Scheme.{u}} (v : W ⟶ U) (j : U ⟶ T) :
    NatTrans.IsMonoidal (leftDerivedUpperStarComp Λ v j).hom := by
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro K L
  exact (leftDerivedUpperStarTensor_comp Λ v j K L).symm

attribute [local instance] nativeCompMonoidal

private theorem exactComp_native {W U T : Scheme.{u}} (v : W ⟶ U) (j : U ⟶ T) :
    (openCoherenceRestrictionComp Λ v j).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (v ≫ j)).inv ≫
        (leftDerivedUpperStarComp Λ v j).hom ≫
        Functor.whiskerLeft (upperStar Λ j).leftDerivedFunctor
          (leftDerivedUpperStarIsoMapDerivedCategory Λ v).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom
          D(upperStar Λ v) := by
  ext M
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    openCoherenceRestrictionComp, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]

private theorem exactCompMonoidal {W U T : Scheme.{u}} (v : W ⟶ U) (j : U ⟶ T) :
    NatTrans.IsMonoidal (openCoherenceRestrictionComp Λ v j).hom := by
  rw [exactComp_native]
  infer_instance

attribute [local instance] exactCompMonoidal

/-- Tensor and closed-Hom comparisons commute with successive open restrictions.
Source: sites-cohomology.tex, Tag 08JB, normalized slice comparisons
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: the balanced-generator formula and its total-summand normalization identify
successive and direct tensor comparison. The ringed-site comparison supplies the Hom
identity, and the section-action equivalence preserves evaluation and slice restriction.
Transport through the exact K-flat comparison gives the displayed native maps. -/
theorem successiveTensorHom {W U T : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    (v : W ⟶ U) (j : U ⟶ T) [IsOpenImmersion v] [IsOpenImmersion j]
    [QuasiCompact v] [QuasiCompact j]
    (K L : DerivedCategory (supportModules Λ T)) :
    (openCoherenceRestrictionComp Λ v j).hom.app (K ⊗ L) ≫
        D(upperStar Λ v).map (tensorRestriction Λ j K L).hom ≫
        (tensorRestriction Λ v (D(upperStar Λ j).obj K) (D(upperStar Λ j).obj L)).hom =
      (tensorRestriction Λ (v ≫ j) K L).hom ≫
        (tensorIso ((openCoherenceRestrictionComp Λ v j).app K)
          ((openCoherenceRestrictionComp Λ v j).app L)).hom ∧
    (openCoherenceRestrictionComp Λ v j).hom.app (((derivedHom Λ T).obj (op K)).obj L) ≫
        D(upperStar Λ v).map (homRestriction Λ j K L) ≫
        homRestriction Λ v (D(upperStar Λ j).obj K) (D(upperStar Λ j).obj L) =
      homRestriction Λ (v ≫ j) K L ≫
        (MonoidalClosed.pre ((openCoherenceRestrictionComp Λ v j).inv.app K)).app _ ≫
        ((derivedHom Λ W).obj
          (op (D(upperStar Λ v).obj (D(upperStar Λ j).obj K)))).map
            ((openCoherenceRestrictionComp Λ v j).hom.app L) := by
  constructor
  · simp only [tensorRestriction_eq, MonoidalCategory.tensorIso_hom, Iso.app_hom]
    change (openCoherenceRestrictionComp Λ v j).hom.app (K ⊗ L) ≫
        Functor.OplaxMonoidal.δ (D(upperStar Λ j) ⋙ D(upperStar Λ v)) K L = _
    rw [← cancel_epi (Functor.LaxMonoidal.μ D(upperStar Λ (v ≫ j)) K L),
      ← Category.assoc, NatTrans.IsMonoidal.tensor, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id, Functor.Monoidal.μ_δ_assoc]
  · simp only [homRestriction_eq]
    dsimp only [derivedHom, MonoidalClosed.internalHom]
    rw [← Functor.LaxMonoidal.ihomComparison_comp_app]
    have h := Functor.LaxMonoidal.ihomComparison_app_comp_map_app
      (openCoherenceRestrictionComp Λ v j).inv K L
    simp only [Functor.comp_obj] at h
    apply (cancel_mono ((ihom
      ((D(upperStar Λ j) ⋙ D(upperStar Λ v)).obj K)).map
        ((openCoherenceRestrictionComp Λ v j).inv.app L))).mp
    simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rw [h, Iso.hom_inv_id_app_assoc]

end SuccessiveMonoidal

/-- The canonical tensor comparisons commute with shifts in either variable.
Source: sites-cohomology.tex, unbounded tensor and signed shifts
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: on a K-flat representative the comparison is fixed on each total summand, and
reindexing a shifted totalization gives the same map with the same Koszul sign. Exact
localization and the invertible derived counits descend the two identities. -/
theorem tensorShifts {U T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (supportModules Λ T)) :
    NatTrans.CommShift
      (F₁ := (curriedTensor _).obj K ⋙ (upperStar Λ j).leftDerivedFunctor)
      (F₂ := (upperStar Λ j).leftDerivedFunctor ⋙
        (curriedTensor _).obj ((upperStar Λ j).leftDerivedFunctor.obj K))
      ((leftDerivedUpperStarTensor Λ j).app K) ℤ ∧
    NatTrans.CommShift
      (F₁ := (curriedTensor _).flip.obj K ⋙ (upperStar Λ j).leftDerivedFunctor)
      (F₂ := (upperStar Λ j).leftDerivedFunctor ⋙
        (curriedTensor _).flip.obj ((upperStar Λ j).leftDerivedFunctor.obj K))
      (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ j) K) ℤ := by
  exact ⟨inferInstance, inferInstance⟩

/-- Tensor shift in the first variable, natural in its second variable.
Source: sites-cohomology.tex, signed total tensor reindexing
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def tensorSourceShift {T : Scheme.{u}} (K : DerivedCategory (supportModules Λ T)) (m : ℤ) :
    (curriedTensor (DerivedCategory (supportModules Λ T))).obj ((shiftFunctor _ m).obj K) ≅
      (curriedTensor (DerivedCategory (supportModules Λ T))).obj K ⋙ shiftFunctor _ m :=
  NatIso.ofComponents
    (fun L ↦
      (((curriedTensor (DerivedCategory (supportModules Λ T))).flip.obj L).commShiftIso m).app K)
    (fun f ↦ (NatTrans.shift_app_comm
      ((curriedTensor (DerivedCategory (supportModules Λ T))).flip.map f) m K).symm)

/-- The canonical target shift of closed Hom, obtained from the tensor-Hom adjunction.
Source: sites-cohomology.tex, Tag 08JB, Koszul Hom reindexing
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def homTargetShift {T : Scheme.{u}} (K : DerivedCategory (supportModules Λ T)) (m : ℤ) :
    shiftFunctor _ m ⋙ (derivedHom Λ T).obj (op K) ≅
      (derivedHom Λ T).obj (op K) ⋙ shiftFunctor _ m :=
  Adjunction.RightAdjointCommShift.iso
    (F := (curriedTensor (DerivedCategory (supportModules Λ T))).obj K)
    (derivedTensorHomAdjunction Λ K) m

/-- The canonical contravariant source shift of closed Hom, the conjugate of tensor
reindexing under the actual tensor-Hom and shift adjunctions.
Source: sites-cohomology.tex, Tag 08JB, source Koszul formula
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def homSourceShift {T : Scheme.{u}} (K : DerivedCategory (supportModules Λ T)) (m : ℤ) :
    (derivedHom Λ T).obj (op ((shiftFunctor _ m).obj K)) ≅
      (derivedHom Λ T).obj (op K) ⋙ shiftFunctor _ (-m) :=
  conjugateIsoEquiv (derivedTensorHomAdjunction Λ ((shiftFunctor _ m).obj K))
      ((derivedTensorHomAdjunction Λ K).comp
        (shiftEquiv (DerivedCategory (supportModules Λ T)) m).toAdjunction)
      (tensorSourceShift Λ K m).symm ≪≫ homTargetShift Λ K (-m)

/-- Restriction commutes with the canonical source and target shifts of closed Hom.
Source: sites-cohomology.tex, Tags 08JB and 08JC
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: compute in the ringed-site model on normalized total-Hom representatives. Reindex
with the source Koszul sign and target shift formula. Slice restriction preserves each
term and differential. The section-action comparison preserves evaluation; consequently
these identities transfer to the native closed structure and its adjunction-defined
shift comparisons. This covers arbitrary integers in either variable. -/
theorem homShifts {U T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (K L : DerivedCategory (supportModules Λ T)) (m : ℤ) :
    D(upperStar Λ j).map ((homTargetShift Λ K m).hom.app L) ≫
        (D(upperStar Λ j).commShiftIso m).hom.app (((derivedHom Λ T).obj (op K)).obj L) ≫
        (shiftFunctor _ m).map (homRestriction Λ j K L) =
      homRestriction Λ j K ((shiftFunctor _ m).obj L) ≫
        ((derivedHom Λ U).obj (op (D(upperStar Λ j).obj K))).map
          ((D(upperStar Λ j).commShiftIso m).hom.app L) ≫
        (homTargetShift Λ (D(upperStar Λ j).obj K) m).hom.app (D(upperStar Λ j).obj L) ∧
    D(upperStar Λ j).map ((homSourceShift Λ K m).hom.app L) ≫
        (D(upperStar Λ j).commShiftIso (-m)).hom.app
          (((derivedHom Λ T).obj (op K)).obj L) ≫
        (shiftFunctor _ (-m)).map (homRestriction Λ j K L) =
      homRestriction Λ j ((shiftFunctor _ m).obj K) L ≫
        (MonoidalClosed.pre ((D(upperStar Λ j).commShiftIso m).inv.app K)).app _ ≫
        (homSourceShift Λ (D(upperStar Λ j).obj K) m).hom.app (D(upperStar Λ j).obj L) := by
  sorry

/-- Transport of exact open extension along an equality of open morphisms.
Source: sites-modules.tex, open extension by zero
(blueprint: lem-pod-condensed-open-derived-calculus). -/
def extensionCongr {W X : Scheme.{u}}
    (a b : {a : W ⟶ X // IsOpenImmersion a}) (h : a = b) :
    D(@openImmersionLowerShriek.{u} Λ _ W X a.val a.property) ≅
      D(@openImmersionLowerShriek.{u} Λ _ W X b.val b.property) :=
  eqToIso (congrArg
    (fun c : {a : W ⟶ X // IsOpenImmersion a} ↦
      D(@openImmersionLowerShriek.{u} Λ _ W X c.val c.property)) h)

private def extensionFactorization {W U T : Scheme.{u}} (v : W ⟶ U) (j : U ⟶ T)
    [IsOpenImmersion v] [IsOpenImmersion j]
    (k : {k : W ⟶ T // IsOpenImmersion k}) (h : k.val = v ≫ j) :
    D(openImmersionLowerShriek Λ v) ⋙ D(openImmersionLowerShriek Λ j) ≅
      D(@openImmersionLowerShriek Λ _ W T k.val k.property) :=
  mateOpenExtensionComp Λ v j ≪≫
    extensionCongr Λ ⟨v ≫ j, inferInstance⟩ k (Subtype.ext h.symm)

private theorem extensionFactorization_eq {W U T : Scheme.{u}} (v : W ⟶ U) (j : U ⟶ T)
    [IsOpenImmersion v] [IsOpenImmersion j]
    (k : {k : W ⟶ T // IsOpenImmersion k}) (h : k.val = v ≫ j) :
    extensionFactorization Λ v j k h =
      Adjunction.leftAdjointCompIso
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
        (@derivedOpenImmersionLowerShriekUpperStarAdjunction Λ _ _ W T k.val k.property)
        (exactComp Λ v j k.val h).symm := by
  have hk : k = ⟨v ≫ j, inferInstance⟩ := Subtype.ext h
  subst k
  simp only [extensionFactorization, extensionCongr, eqToIso_refl, Iso.trans_refl,
    exactComp_eq, Adjunction.leftAdjointCompIso]
  exact WeilConjectures.CompactSupportCondensedRealization.scalarComp_eq_conjugate
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (v ≫ j))
    (openCoherenceRestrictionComp Λ v j).symm

/-- The canonical open-extension compositors are associative and commute with shifts.
Source: sites-modules.tex, uniqueness of left adjoints and composite counits
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: both composites are left-adjoint comparisons to the same associative restriction
compositor and have the same composite counit. Uniqueness of left adjoints identifies
them. Termwise adjunction maps commute with shifts and exact localization preserves this. -/
theorem extensionCompositionCoherence {W U T X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (w : W ⟶ U) (v : U ⟶ T) (j : T ⟶ X)
    [IsOpenImmersion w] [IsOpenImmersion v] [IsOpenImmersion j]
    [QuasiCompact w] [QuasiCompact v] [QuasiCompact j] :
    NatTrans.CommShift (mateOpenExtensionComp Λ v j).hom ℤ ∧
    (Functor.isoWhiskerRight (mateOpenExtensionComp Λ w v)
        D(openImmersionLowerShriek Λ j) ≪≫ mateOpenExtensionComp Λ (w ≫ v) j ≪≫
        extensionCongr Λ ⟨(w ≫ v) ≫ j, inferInstance⟩ ⟨w ≫ (v ≫ j), inferInstance⟩
          (Subtype.ext (Category.assoc w v j))) =
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D(openImmersionLowerShriek Λ w)
          (mateOpenExtensionComp Λ v j) ≪≫ mateOpenExtensionComp Λ w (v ≫ j)) := by
  refine ⟨?_, ?_⟩
  · have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).CommShift ℤ :=
      (openImmersionLowerShriekUpperStarAdjunction Λ v).commShift_mapDerivedCategoryAdjunction
    have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
      (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
    have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (v ≫ j)).CommShift ℤ :=
      (openImmersionLowerShriekUpperStarAdjunction Λ (v ≫ j)).commShift_mapDerivedCategoryAdjunction
    change NatTrans.CommShift
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j) |>.leftAdjointUniq
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (v ≫ j)).ofNatIsoRight
            (openCoherenceRestrictionComp Λ v j))).hom ℤ
    have he := WeilConjectures.CompactSupportCondensedRealization.scalarComp_eq_conjugate
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (v ≫ j))
      (openCoherenceRestrictionComp Λ v j).symm
    simp only [Iso.symm_symm_eq] at he
    rw [he]
    dsimp only [openCoherenceRestrictionComp]
    infer_instance
  · have hc := exactComp_assoc Λ w v j (w ≫ v) (v ≫ j) (w ≫ (v ≫ j))
      rfl rfl (Category.assoc w v j).symm
    have hp := Adjunction.leftAdjointCompIso_assoc
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ w)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (w ≫ v))
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (v ≫ j))
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (w ≫ (v ≫ j)))
      (exactComp Λ w v (w ≫ v) rfl).symm
      (exactComp Λ v j (v ≫ j) rfl).symm
      (exactComp Λ w (v ≫ j) (w ≫ (v ≫ j)) rfl).symm
      (exactComp Λ (w ≫ v) j (w ≫ (v ≫ j)) (Category.assoc w v j).symm).symm
      (by
        apply Iso.ext_inv
        ext M
        simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
          Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
          Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, Category.comp_id] using
          NatTrans.congr_app hc.symm M)
    rw [← extensionFactorization_eq Λ v j ⟨v ≫ j, inferInstance⟩ rfl,
      ← extensionFactorization_eq Λ w (v ≫ j) ⟨w ≫ (v ≫ j), inferInstance⟩ rfl,
      ← extensionFactorization_eq Λ w v ⟨w ≫ v, inferInstance⟩ rfl,
      ← extensionFactorization_eq Λ (w ≫ v) j ⟨w ≫ (v ≫ j), inferInstance⟩
        (Category.assoc w v j).symm] at hp
    apply Iso.ext
    ext M
    have hh := NatTrans.congr_app (congrArg Iso.hom hp) M
    simpa only [extensionFactorization, extensionCongr, eqToIso_refl,
      Iso.trans_refl, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.assoc] using hh.symm

/-- The complementary closed restriction annihilates open extension by zero, and the
open unit identifies restriction of extension with the identity.
Source: sites-modules.tex, open/closed localization
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: lem-sfb-condensed-support-derived-localization gives the invertible actual open
unit and the zero mixed restriction, for arbitrary condensed coefficients. Its support
pullback is canonically identified with upperStar, so the assertion is exactly the one
on the ordinary internal-module derived categories. -/
theorem complementaryRestriction {Z U T : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    (z : Z ⟶ T) (j : U ⟶ T) [IsClosedImmersion z] [IsOpenImmersion j] [QuasiCompact j]
    (h : Set.range z.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (supportModules Λ U)) :
    IsZero (D(upperStar Λ z).obj (D(openImmersionLowerShriek Λ j).obj K)) ∧
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app K) := by
  have hs := condensedSupportDerivedLocalization Λ z j h
  let e := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ z)
  refine ⟨?_, ?_⟩
  · exact (hs.2.2.2.1 K).of_iso (e.symm.app _)
  · infer_instance

/-- The two-open Mayer--Vietoris triangle with difference and sum of the actual counits.
Source: cohomology.tex, Tag 08BU, lemma-exact-sequence-lower-shriek
(blueprint: lem-pod-condensed-open-derived-calculus).

Proof: choose any complex representing K. On complexes form extension from W, the sum
of the extensions from U and V, and K, using the nested counits. The maps are (a,-c)
and (epsilon_U,epsilon_V); their composite is zero because both composites from W are
epsilon_W. On U the sequence is (h,-1) followed by (1,h), and on V it is (1,-h') followed
by (h',1). These are split exact. The two subterminal restrictions jointly detect
exactness on the pro-etale site; the section-action equivalence preserves these maps.
Thus this is a degreewise short exact sequence of internal-module complexes. Apply
lem-weil-pbc-complex-ses-triangle and the exact derived factorizations. This produces
precisely the displayed arrows and a distinguished triangle in the unbounded category. -/
theorem mayerVietoris {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (U V : T.Opens) (hU : IsCompact (U : Set T)) (hV : IsCompact (V : Set T))
    (hcover : U ⊔ V = ⊤) (K : DerivedCategory (supportModules Λ T)) :
    ∃ δ : K ⟶ (shiftFunctor _ (1 : ℤ)).obj
      (D(openImmersionLowerShriek Λ (U ⊓ V).ι).obj
        (D(upperStar Λ (U ⊓ V).ι).obj K)),
      Triangle.mk
        (biprod.lift
          (nestedCounit Λ (T.homOfLE (inf_le_left : U ⊓ V ≤ U)) U.ι
            (U ⊓ V).ι (T.homOfLE_ι _).symm K)
          (-(nestedCounit Λ (T.homOfLE (inf_le_right : U ⊓ V ≤ V)) V.ι
            (U ⊓ V).ι (T.homOfLE_ι _).symm K)))
        (biprod.desc
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app K)
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ V.ι).counit.app K))
        δ ∈ distTriang (DerivedCategory (supportModules Λ T)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.OpenDerivedCalculus
