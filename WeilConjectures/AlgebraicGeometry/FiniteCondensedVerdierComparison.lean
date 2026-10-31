/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
public import WeilConjectures.SecSmoothPurity.FiniteNativeTensorComparison
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteCondensedNormalizedAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteCondensedRealizationClosed
import WeilConjectures.AlgebraicGeometry.FiniteCondensedRealizationSymmetric

/-! # Finite condensed Verdier comparison

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i)
(blueprint: lem-sf-finite-condensed-verdier-comparison).
The statement uses actual module objects and records the compact-support counit
normalization and the evaluation transpose, without any double-dual assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
universe u v w v₀ w₀ c d c₀ d₀
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The clauses of the finite Verdier comparison, with all ambient functors and
compact-support comparisons fixed before its witnesses are quantified. The monoidal
structures are parameters, never witnesses of this structure.
`Gp` is a right adjoint on the actual full constructible subcategories. Its counit
is carried by their inclusions. The Hom arrow is the canonical evaluation transpose.
Source: latest blueprint, finite coefficients in paragraph (i)
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
structure FiniteCondensedVerdierComparisonData
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ i : ℤ, (shiftFunctor C i).Additive] [Pretriangulated C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    [HasShift D ℤ] [HasZeroObject D] [Preadditive D]
    [∀ i : ℤ, (shiftFunctor D i).Additive] [Pretriangulated D]
    {C₀ : Type c₀} [Category.{v₀} C₀] [MonoidalCategory C₀]
    {D₀ : Type d₀} [Category.{w₀} D₀] [MonoidalCategory D₀]
    (F : C ⥤ D) (F₀ : C₀ ⥤ D₀)
    [monoidal : F.Monoidal] [baseMonoidal : F₀.Monoidal]
    (Le : C ⥤ C₀) (Lp : D ⥤ D₀)
    (Ge : C₀ ⥤ C) (adje : Le ⊣ Ge)
    (P : ObjectProperty C) (Q : ObjectProperty D) (Q₀ : ObjectProperty D₀)
    (bC : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X)
    (bD : ∀ X Y : D, X ⊗ Y ≅ Y ⊗ X)
    (B : Type (max c d)) [Category B] (iB : B ⥤ C)
    (alpha : iB ⋙ Le ⋙ F₀ ≅ iB ⋙ F ⋙ Lp) where
  [shift : F.CommShift ℤ]
  exact : F.IsTriangulated
  symmetric : ∀ K L : C,
    (Functor.Monoidal.μIso F K L).hom ≫ F.map (bC K L).hom =
      (bD (F.obj K) (F.obj L)).hom ≫ (Functor.Monoidal.μIso F L K).hom
  restriction : ∃ e : P.FullSubcategory ≌ Q.FullSubcategory,
    Nonempty (e.functor ⋙ Q.ι ≅ P.ι ⋙ F)
  unit_constructible : Q₀ (𝟙_ D₀)
  support_preserves : ∀ K : Q.FullSubcategory, Q₀ (Lp.obj K.obj)
  Gp : Q₀.FullSubcategory ⥤ Q.FullSubcategory
  adjp : Q₀.lift (Q.ι ⋙ Lp) support_preserves ⊣ Gp
  dualizing_bounded : B
  dualizing_bounded_spec : iB.obj dualizing_bounded = Ge.obj (𝟙_ C₀)
  w : F.obj (Ge.obj (𝟙_ C₀)) ≅ (Gp.obj ⟨𝟙_ D₀, unit_constructible⟩).obj
  normalization :
    Lp.map (F.map (eqToHom dualizing_bounded_spec) ≫ w.hom) ≫
        (adjp.counit.app ⟨𝟙_ D₀, unit_constructible⟩).hom =
      alpha.inv.app dualizing_bounded ≫
        F₀.map (Le.map (eqToHom dualizing_bounded_spec) ≫ adje.counit.app (𝟙_ C₀)) ≫
          (Functor.Monoidal.εIso F₀).inv
  beta_isIso : ∀ K : C, P K →
    IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app (Ge.obj (𝟙_ C₀)))
  comparison :
    P.ι.op ⋙ (MonoidalClosed.internalHom.flip.obj (Ge.obj (𝟙_ C₀))) ⋙ F ⟶
      (P.ι ⋙ F).op ⋙ MonoidalClosed.internalHom.flip.obj
        (Gp.obj ⟨𝟙_ D₀, unit_constructible⟩).obj
  comparison_formula : ∀ K : P.FullSubcategory,
    comparison.app (op K) =
      (Functor.LaxMonoidal.ihomComparison F K.obj).natTrans.app (Ge.obj (𝟙_ C₀)) ≫
        (ihom (F.obj K.obj)).map w.hom
  comparison_isIso : ∀ K : P.FullSubcategory, IsIso (comparison.app (op K))
  evaluation : ∀ K : P.FullSubcategory,
    (𝟙 (F.obj K.obj) ⊗ₘ comparison.app (op K)) ≫
        (ihom.ev (F.obj K.obj)).app (Gp.obj ⟨𝟙_ D₀, unit_constructible⟩).obj =
      (Functor.Monoidal.μIso F K.obj ((ihom K.obj).obj (Ge.obj (𝟙_ C₀)))).hom ≫
        F.map ((ihom.ev K.obj).app (Ge.obj (𝟙_ C₀))) ≫ w.hom

private theorem finiteCondensedHomComparison
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.Monoidal] (P : ObjectProperty C)
    {W : C} {W' : D} (w : F.obj W ≅ W')
    (hβ : ∀ K : C, P K →
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W)) :
    ∃ comparison : P.ι.op ⋙ MonoidalClosed.internalHom.flip.obj W ⋙ F ⟶
        (P.ι ⋙ F).op ⋙ MonoidalClosed.internalHom.flip.obj W',
      (∀ K : P.FullSubcategory,
        comparison.app (op K) =
          (Functor.LaxMonoidal.ihomComparison F K.obj).natTrans.app W ≫
            (ihom (F.obj K.obj)).map w.hom) ∧
      (∀ K : P.FullSubcategory, IsIso (comparison.app (op K))) ∧
      ∀ K : P.FullSubcategory,
        (𝟙 (F.obj K.obj) ⊗ₘ comparison.app (op K)) ≫
            (ihom.ev (F.obj K.obj)).app W' =
          (Functor.Monoidal.μIso F K.obj ((ihom K.obj).obj W)).hom ≫
            F.map ((ihom.ev K.obj).app W) ≫ w.hom := by
  let comparison : P.ι.op ⋙ MonoidalClosed.internalHom.flip.obj W ⋙ F ⟶
      (P.ι ⋙ F).op ⋙ MonoidalClosed.internalHom.flip.obj W' :=
    { app := fun K ↦
        (Functor.LaxMonoidal.ihomComparison F K.unop.obj).natTrans.app W ≫
          (ihom (F.obj K.unop.obj)).map w.hom
      naturality := by
        intro K L f
        change F.map ((MonoidalClosed.pre f.unop.hom).app W) ≫ _ =
          _ ≫ (MonoidalClosed.pre (F.map f.unop.hom)).app W'
        rw [← Category.assoc, Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app,
          Category.assoc, MonoidalClosed.pre_comm_ihom_map, Category.assoc] }
  refine ⟨comparison, fun _ ↦ rfl, ?_, ?_⟩
  · intro K
    have := hβ K.obj K.property
    dsimp [comparison]
    infer_instance
  · intro K
    change (𝟙 (F.obj K.obj) ⊗ₘ
        ((Functor.LaxMonoidal.ihomComparison F K.obj).natTrans.app W ≫
          (ihom (F.obj K.obj)).map w.hom)) ≫ _ = _
    rw [id_tensorHom, ← MonoidalClosed.uncurry_eq,
      MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_eq,
      Functor.LaxMonoidal.ihomComparison_ev, Category.assoc, Functor.Monoidal.μIso_hom]


private theorem finiteCondensedVerdierOfComponents
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ i : ℤ, (shiftFunctor C i).Additive] [Pretriangulated C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    [HasShift D ℤ] [HasZeroObject D] [Preadditive D]
    [∀ i : ℤ, (shiftFunctor D i).Additive] [Pretriangulated D]
    {C₀ : Type c₀} [Category.{v₀} C₀] [MonoidalCategory C₀]
    {D₀ : Type d₀} [Category.{w₀} D₀] [MonoidalCategory D₀]
    (F : C ⥤ D) (F₀ : C₀ ⥤ D₀)
    [monoidal : F.Monoidal] [baseMonoidal : F₀.Monoidal]
    (Le : C ⥤ C₀) (Lp : D ⥤ D₀)
    (Ge : C₀ ⥤ C) (adje : Le ⊣ Ge)
    (P : ObjectProperty C) (Q : ObjectProperty D) (Q₀ : ObjectProperty D₀)
    (bC : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X)
    (bD : ∀ X Y : D, X ⊗ Y ≅ Y ⊗ X)
    (B : Type (max c d)) [Category B] (iB : B ⥤ C)
    (alpha : iB ⋙ Le ⋙ F₀ ≅ iB ⋙ F ⋙ Lp)
    [F.CommShift ℤ] [F.IsTriangulated]
    (d : FiniteCondensedNormalizedAdjunctionData F F₀ Le Lp Ge adje P Q Q₀ B iB alpha)
    (hsym : ∀ K L : C,
      (Functor.Monoidal.μIso F K L).hom ≫ F.map (bC K L).hom =
        (bD (F.obj K) (F.obj L)).hom ≫ (Functor.Monoidal.μIso F L K).hom)
    (hrestriction : ∃ e : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (e.functor ⋙ Q.ι ≅ P.ι ⋙ F))
    (hβ : ∀ K : C, P K →
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app (Ge.obj (𝟙_ C₀)))) :
    Nonempty (FiniteCondensedVerdierComparisonData
      F F₀ Le Lp Ge adje P Q Q₀ bC bD B iB alpha) := by
  obtain ⟨comparison, hformula, hiso, heval⟩ := finiteCondensedHomComparison F P d.w hβ
  exact ⟨{ exact := inferInstance
           symmetric := hsym
           restriction := hrestriction
           unit_constructible := d.unit_constructible
           support_preserves := d.support_preserves
           Gp := d.Gp
           adjp := d.adjp
           dualizing_bounded := d.dualizing_bounded
           dualizing_bounded_spec := d.dualizing_bounded_spec
           w := d.w
           normalization := d.normalization
           beta_isIso := hβ
           comparison := comparison
           comparison_formula := hformula
           comparison_isIso := hiso
           evaluation := heval }⟩

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

/-- The inverse-image mate of the normalized direct-image section identity.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingPullbackIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.upperStar (coefficient A) f ⋙
        (eU.ordinary.trans eU.fixed).functor ≅
      (eT.ordinary.trans eT.fixed).functor ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅
      EU.functor ⋙ R := encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- The open-extension mate of the normalized restriction comparison.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingOpenShriekIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙
        (eT.ordinary.trans eT.fixed).functor ≅
      (eU.ordinary.trans eU.fixed).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let i := finiteCondensedEncodingPullbackIso A j eT eU
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- The canonical derived direct-image encoding comparison.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingDerivedPushforwardIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (encodingPushforwardNatIso A T U f eT eU) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

/-- The canonical derived open-extension encoding comparison.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingDerivedOpenShriekIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.openImmersionLowerShriek (coefficient A) j
  let G := openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.mapDerivedCategory ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso F ET.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (finiteCondensedEncodingOpenShriekIso A j eT eU) ≪≫
    Functor.mapDerivedCategoryCompIso EU.functor G

/-- The canonical support comparison: the normalized section-action proper and open
comparisons, conjugated by the inverse encodings, followed by the ordinary site map.
It is defined on bounded-below complexes; only its constructible restriction is used.
Source: latest blueprint, paragraph (i), compatibility with compact support
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedSupportComparison
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    {T S : Scheme.{u}} {a : T ⟶ S} (c : Compactification a)
    (eT : Encoding A T) (eS : Encoding A S) (eZ : Encoding A c.Z) :
    _root_.DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⋙ internalEtaleRealization A S eS ≅
      _root_.DerivedCategory.Plus.ι ⋙ internalEtaleRealization A T eT ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c := by
  let d : CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
      eS.fixedDerived.functor ≅ eT.fixedDerived.functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (finiteCondensedEncodingDerivedPushforwardIso A c.g eS eZ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (finiteCondensedEncodingDerivedOpenShriekIso A c.i eZ eT) _ ≪≫
      Functor.associator _ _ _
  let di := Iso.inverseCompIso (G := eT.fixedDerived)
    (Iso.isoCompInverse (H := eS.fixedDerived) d ≪≫ Functor.associator _ _ _)
  let j := (compactSupportSiteComparison (ULift.{u + 1} A) c).symm
  exact Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
      (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight j eS.fixedDerived.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
      (Functor.isoWhiskerLeft
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory
        di.symm) ≪≫
    Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary


namespace Padic

/-- The specified positive-level coefficient ring is finite.
Source: the coefficient extension finiteness interface
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
instance finiteCondensedVerdierCoefficientFinite
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (n : ℕ) [hn : Fact (1 ≤ n)] :
    Finite (coefficientExtensionRing ℓ E n) :=
  finite_coefficientExtensionRing ℓ E n hn.out

end Padic

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary


private theorem coefficient_invertibleExponent
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (n : ℕ) :
    ((ℓ ^ n : ℕ) : Padic.coefficientExtensionRing ℓ E n) = 0 ∧
      HasInvertibleExponent (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n))
        (Spec (.of k)) := by
  have h := (Padic.extension_integers_dvr ℓ E (Padic.coefficientExtensionAbsoluteValue ℓ E)
    (spectralNorm_extends (K := Padic ℓ) (L := E))).choose_spec.choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue ℓ E (ℓ : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue ℓ E (ℓ : E) = ‖(ℓ : Padic ℓ)‖ := by
        change spectralNorm (Padic ℓ) E (ℓ : E) = ‖(ℓ : Padic ℓ)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic ℓ) (L := E) (ℓ : Padic ℓ))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (ℓ : Padic.coefficientExtensionIntegers ℓ E) ∈
      Padic.coefficientExtensionMaximalIdeal ℓ E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ℓ E} :
      Set (Padic.coefficientExtensionIntegers ℓ E)) =
      Padic.coefficientExtensionMaximalIdeal ℓ E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (ℓ : Padic.coefficientExtensionIntegers ℓ E) ^ n ∈
      Padic.coefficientExtensionIdeal ℓ E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer ℓ E} :
      Set (Padic.coefficientExtensionIntegers ℓ E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  have hkill : ((ℓ ^ n : ℕ) : Padic.coefficientExtensionRing ℓ E n) = 0 := by
    change ((ℓ ^ n : ℕ) :
      Padic.coefficientExtensionIntegers ℓ E ⧸ Padic.coefficientExtensionIdeal ℓ E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  have hlk : (ℓ : k) ≠ 0 := fun hz ↦
    (Ne.symm hpℓ) ((CharP.ringChar_of_prime_eq_zero (Fact.out : ℓ.Prime) hz).symm.trans
      (ringChar.eq k p))
  have hu : IsUnit ((ℓ ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hlk).pow n
  refine ⟨hkill, ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos n, ?_, ?_⟩
  · exact ULift.down_injective hkill
  · simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom

/-- Finite-coefficient comparison of the ambient etale dualizing object with the
actual constructible condensed dualizing object, its internal Hom, and evaluation.
The encodings are the normalized section-action encodings, not arbitrary equivalences.
Both monoidal structures are the canonical `FiniteNativeTensor.realizationMonoidal`,
including its specified unit map. The support isomorphism is fixed by the canonical
site and section-action maps.

Source: latest blueprint, det-pd-biduality-coefficients.proof.md, paragraph (i)
(blueprint: lem-sf-finite-condensed-verdier-comparison).

Proof:
1. The coefficient quotient is finite. Its defining ideal contains ell^n; since
ell differs from the field characteristic, this is an invertible additive exponent.
Choose the normalized encodings. Termwise derived inverse encoding and exact site
pullback give the shift comparison and exactness of realization.
2. finiteCondensedCtfEquivalence assembles the ordered Tor-interval equivalences
into an equivalence on the full finite-Tor constructible domains. It uses bounded-below
full faithfulness and min/max endpoint enlargement, without a common interval choice.
3. finiteCondensedNormalizedAdjunction restricts the etale adjunction, transports it
across these equivalences and the specified compact-support comparison, and constructs
the dualizing comparison with its counit normalization. No Brown adjoint is needed.
4. Apply finiteCondensedRealizationSymmetric and finiteCondensedRealizationClosed.
The latter applies to the constructible etale dualizing object provided by step 3.
Postcompose its canonical mate by internal Hom applied to w. Naturality of the mate
in its contravariant variable gives comparison, and its evaluation-transpose equation
gives the evaluation identity. This last assembly is proved generically before any
geometric categories are substituted; no double-dual morphism is used. -/
theorem finiteCondensedVerdierComparison
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n : ℕ) [Fact (1 ≤ n)]
    [TopologicalSpace (Padic.coefficientExtensionRing ℓ E n)]
    [DiscreteTopology (Padic.coefficientExtensionRing ℓ E n)]
    [IsTopologicalRing (Padic.coefficientExtensionRing ℓ E n)]
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ enc : ∀ X : Scheme.{u}, Encoding (Padic.coefficientExtensionRing ℓ E n) X,
      Nonempty (CategoryTheory.FiniteCondensedVerdierComparisonData
        (monoidal := FiniteNativeTensor.realizationMonoidal
          (Padic.coefficientExtensionRing ℓ E n) T (enc T))
        (baseMonoidal := FiniteNativeTensor.realizationMonoidal
          (Padic.coefficientExtensionRing ℓ E n) (Spec (.of k)) (enc (Spec (.of k))))
        (internalEtaleRealization (Padic.coefficientExtensionRing ℓ E n) T (enc T))
        (internalEtaleRealization (Padic.coefficientExtensionRing ℓ E n)
          (Spec (.of k)) (enc (Spec (.of k))))
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)))
          (NagataCompactification a))
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (coefficient (Padic.coefficientExtensionRing ℓ E n)) (NagataCompactification a))
        (Etale.rightDerivedUpperShriekOfCompactification
          (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)) (NagataCompactification a))
        (Etale.rightDerivedUpperShriekOfCompactificationAdjunction
          (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)) (NagataCompactification a))
        (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)) T ⊓
            _root_.DerivedCategory.finiteTorAmplitude _)
        (constantModelBoundedConstructible
          (coefficient (Padic.coefficientExtensionRing ℓ E n)) T ⊓
            _root_.DerivedCategory.finiteTorAmplitude _)
        (constantModelBoundedConstructible
          (coefficient (Padic.coefficientExtensionRing ℓ E n)) (Spec (.of k)) ⊓
            _root_.DerivedCategory.finiteTorAmplitude _)
        (_root_.DerivedCategory.braidedCategory'
          (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n))))).braiding
        (_root_.DerivedCategory.braidedCategory'
          (Internal (Padic.coefficientExtensionRing ℓ E n) T)).braiding
        (_root_.DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n)))))
        _root_.DerivedCategory.Plus.ι
        (finiteCondensedSupportComparison (Padic.coefficientExtensionRing ℓ E n)
          (NagataCompactification a) (enc T) (enc (Spec (.of k)))
          (enc (NagataCompactification a).Z))) := by
  let A := Padic.coefficientExtensionRing ℓ E n
  have hexp := coefficient_invertibleExponent p ℓ hpℓ k E n
  let := hexp.2
  let enc : ∀ X : Scheme.{u}, Encoding A X :=
    fun X ↦ Classical.choice (encoding_exists A X)
  let := FiniteNativeTensor.realizationMonoidal A T (enc T)
  let := FiniteNativeTensor.realizationMonoidal A (Spec (.of k)) (enc (Spec (.of k)))
  let : ((enc T).fixed.inverse ⋙ (enc T).ordinary.inverse).Additive := inferInstance
  let : (enc T).fixedDerived.inverse.CommShift ℤ := by
    change ((enc T).fixed.inverse ⋙ (enc T).ordinary.inverse).mapDerivedCategory.CommShift ℤ
    infer_instance
  let : (enc T).fixedDerived.inverse.IsTriangulated := by
    change ((enc T).fixed.inverse ⋙ (enc T).ordinary.inverse).mapDerivedCategory.IsTriangulated
    infer_instance
  let : (internalEtaleRealization A T (enc T)).CommShift ℤ := by
    unfold internalEtaleRealization
    infer_instance
  let : (internalEtaleRealization A T (enc T)).IsTriangulated := by
    unfold internalEtaleRealization
    infer_instance
  obtain ⟨d⟩ := finiteCondensedNormalizedAdjunction p ℓ hpℓ k A enc T a
    (finiteCondensedSupportComparison A (NagataCompactification a)
      (enc T) (enc (Spec (.of k))) (enc (NagataCompactification a).Z))
  have hsym := finiteCondensedRealizationSymmetric A T (enc T)
  have hclosed := finiteCondensedRealizationClosed p ℓ hpℓ k A ⟨n, hexp.1⟩ enc T a
  have hβ := fun K hK ↦ hclosed K _ hK d.dualizing_constructible
  refine ⟨enc, CategoryTheory.finiteCondensedVerdierOfComponents
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ d hsym ?_ hβ⟩
  obtain ⟨hF, h⟩ := finiteCondensedCtfEquivalence p ℓ hpℓ k A enc T a
  let P := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let Q := constantModelBoundedConstructible (coefficient A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let R := Q.lift (P.ι ⋙ internalEtaleRealization A T (enc T)) hF
  have : R.IsEquivalence := h
  exact ⟨R.asEquivalence, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
