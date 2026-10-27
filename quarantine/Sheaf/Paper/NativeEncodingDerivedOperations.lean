module

public import Sheaf.Paper.NativeAdicEncodingCore

public import Sheaf.Paper.LocallyFiniteCoefficientRingRealization
public import Sheaf.Paper.CondensedQbarCoefficientConstruction
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.Adic.SectionAction

/-! # Native encoding and ordinary unbounded derived operations

Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3; native Adic/Module.lean,
WeilSheaf/LowerStar.lean and RightDerivedFunctor/IsoAlgebra.lean.
(blueprint: lem-sf-native-encoding-derived-operations).

The encoding is the existing lax-monoidal forgetful functor on module objects,
followed by restriction along the actual normalized coefficient-ring isomorphism.
All derived categories below are ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.NativeEncoding


/-- Forget the actual fixed-pair structure and apply the exact encoding, on derived categories.
Source: native WeilSheaf/Category.lean and RightDerivedFunctor/IsoAlgebra.lean.
(blueprint: lem-sf-native-encoding-derived-operations). -/
abbrev realization (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))] :=
  (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory ⋙
    derivedEncoding l (T ↘ Spec (CommRingCat.of k₀)).geometricFiber

private theorem unitQ_eq_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ K =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) := by
  unfold Functor.rightDerivedFunctorUnitQ
  change 𝟙 _ ≫ _ ≫ F.rightDerivedFunctor.map (𝟙 _) = _
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem exact_factors_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.inv.app K := by
  have h : F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app K ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.comp_id, Category.id_comp]
  apply (cancel_epi (F.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ _).obj K))).mp
  rw [Iso.hom_inv_id_app, h, Iso.hom_inv_id_app]
  rfl

private theorem homotopy_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 _ := by
  apply (cancel_epi
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K)).mp
  rw [Iso.hom_inv_id_app, Category.comp_id,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app]

@[reassoc] private theorem derived_comp_exact_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : CochainComplex C ℤ) :
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ K) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).inv.app
          (DerivedCategory.Q.obj K) =
      (F ⋙ G).rightDerivedFunctorUnitQ K := by
  have h :
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G).app
          ((HomotopyCategory.quotient _ _).obj K) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).inv.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      (F ⋙ G).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) := by
    simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedNatIso]
  simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, homotopy_comp_inv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  erw [Category.id_comp] at h
  rw [Category.assoc] at h
  rw [unitQ_eq_unit, unitQ_eq_unit]
  rw [← exact_factors_inv G ((F.mapHomologicalComplex (.up ℤ)).obj K)]
  convert! h using 1

@[reassoc] private theorem derived_natIso_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ K ≫
        (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) ≫
        G.rightDerivedFunctorUnitQ K := by
  rw [unitQ_eq_unit, unitQ_eq_unit]
  change F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    (Functor.rightDerivedFunctorNatIso e).hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) = _
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedNatTrans_app, Functor.whiskerRight_app]
  rfl

@[reassoc] private theorem derived_comp_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (K : CochainComplex C ℤ) :
    (F ⋙ G).rightDerivedFunctorUnitQ K ≫
        (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnitQ K) := by
  have h : (F ⋙ G).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj K) ≫
      (Functor.rightDerivedFunctorCompIso F G).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      (Functor.rightDerivedFunctorCompUnit F G).app
        ((HomotopyCategory.quotient _ _).obj K) := by
    simp [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedNatIso]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, homotopy_comp_inv, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  erw [Category.id_comp] at h
  simp only [unitQ_eq_unit]
  convert! h using 1

@[reassoc] private theorem derived_exact_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ K ≫
        F.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.inv.app K := by
  have h := NatTrans.congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient _ _).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, exact_factors_inv] at h
  rw [unitQ_eq_unit]
  convert! h using 1

private theorem derived_square_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) (G : C ⥤ D) (r : A ⥤ C) (s : B ⥤ D)
    [F.Additive] [G.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [r.PreservesKInjectiveComplexes] (e : F ⋙ s ≅ r ⋙ G)
    (K : CochainComplex A ℤ) :
    s.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        s.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ K) ≫
        ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F s).symm ≪≫
          Functor.rightDerivedFunctorNatIso e ≪≫
          Functor.rightDerivedFunctorCompIso r G ≪≫
          Functor.isoWhiskerRight r.rightDerivedFunctorIsoMapDerivedCategory
            G.rightDerivedFunctor).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) ≫
        G.rightDerivedFunctorUnitQ ((r.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.inv.app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [derived_comp_exact_unit_assoc, derived_natIso_unit_assoc, derived_comp_unit_assoc,
    ← Functor.map_comp, derived_exact_unit]

/-- The derived direct-image comparison is the ordinary comparison on K-injective models,
normalized by the two actual right-derived units and exact-localization factors.
Source: Stacks 070I and 070Y; native RightDerivedFunctor/MapDerivedCategory.lean.
(blueprint: lem-sf-native-encoding-derived-operations).
Proof: insert the defining composition of derivedPushComparison. Naturality of the
right-derived comparison with its unit identifies the middle map with pushComparison
on the complex. The exact-localization factors are the two outside maps. Since encoding
preserves K-injectives, both units are invertible on this I; cancelling them is exactly
the computation on the same underlying resolution. -/
theorem derivedPushComparison_unit (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : CochainComplex (AdicSheaf l X) ℤ) (hI : I.IsKInjective) :
    (encoding l Y).mapDerivedCategoryFactors.inv.app
        (((adicLowerStar l f).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (derivedEncoding l Y).map ((adicLowerStar l f).rightDerivedFunctorUnitQ I) ≫
      (derivedPushComparison l f).hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pushComparison l f) (.up ℤ)).hom.app I) ≫
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctorUnitQ
        (((encoding l X).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) f).map
        ((encoding l X).mapDerivedCategoryFactors.inv.app I) := by
  have _ := hI
  exact derived_square_unit (adicLowerStar l f)
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f)
    (encoding l X) (encoding l Y) (pushComparison l f) I

/-- The native constant-function action recovers the vector scalar action on every module,
including the inverse image under the equivalence. This fixes the inverse scalar rule.
Source: Stacks 03EK; native module unit law and adicConstantSheaf_one_app.
(blueprint: lem-sf-native-encoding-derived-operations).
Proof: multiply the native module unit equation by a vector scalar. Vector linearity
moves the scalar to the unit function, which becomes the constant function of that value.
The tensorator below is the presheaf-to-sheaf tensor map, so no sectionwise-tensor
identification is assumed. Applied to the inverse module this is precisely restriction
of its B-action along constant functions, after transporting the R-action by theta inverse. -/
theorem native_constant_action (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (M : AdicSheaf l T) (V : T.ProEtᵒᵖ)
    (a : ULift.{u + 1} (PadicAlgCl l)) (m : M.X.obj.obj V) :
    ((Mod.act M.X).hom.app V)
      (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T)
        (WeilCoefficients.{u} l)) (adicConstantSheaf l T) M.X).app V)
        (((CategoryTheory.MonObj.one (X := (adicConstantSheaf l T).obj)).app V a)
          ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] m)) = a • m := by
  exact AdicSheaf.algebraMap_sectionAct M a m

section WeilComparisons

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
  [f.IsOver (Spec (CommRingCat.of k₀))]

/-- The canonical ambient pullback comparison, localized from the actual fixed-pair
forgetting square and the normalized module pullback square.
Source: native WeilSheaf/Category.lean:444--450; Stacks 015F.
(blueprint: lem-sf-native-encoding-derived-operations). -/
def weilDerivedPullComparison :
    (ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory ⋙ realization k₀ l X ≅
      realization k₀ l Y ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap f
            (comp_over f (Spec (CommRingCat.of k₀))))).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategorySquareIso
      (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
        (adicUpperStarGeometricFiberMapCompFrobeniusIso l f
          (comp_over f (Spec (CommRingCat.of k₀)))))) _ ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft _
    (Functor.mapDerivedCategorySquareIso
      (pullComparison l (Scheme.Hom.geometricFiberMap f
        (comp_over f (Spec (CommRingCat.of k₀)))))) ≪≫
  (Functor.associator _ _ _).symm

/-- The canonical ambient direct-image comparison, using the given native Frobenius
transport and the same underlying K-injective resolutions.
Source: native WeilSheaf/LowerStar.lean:72--79 and RightDerivedFunctor/IsoAlgebra.lean.
(blueprint: lem-sf-native-encoding-derived-operations). -/
def weilDerivedPushComparison :
    (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor ⋙ realization k₀ l Y ≅
      realization k₀ l X ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) (Scheme.Hom.geometricFiberMap f
          (comp_over f (Spec (CommRingCat.of k₀)))) := by
  letI := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  letI := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
        (WeilSheaf.frobeniusPullback k₀ l X)
        (adicLowerStarGeometricFiberMapCompFrobeniusIso l f
          (comp_over f (Spec (CommRingCat.of k₀))))) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (derivedPushComparison l (Scheme.Hom.geometricFiberMap f
        (comp_over f (Spec (CommRingCat.of k₀))))) ≪≫
    (Functor.associator _ _ _).symm

/-- Underlying native resolutions are also internal-module K-injective resolutions.
Source: native RightDerivedFunctor/IsoAlgebra.lean; Stacks 070I and 070Y.
(blueprint: lem-sf-native-encoding-derived-operations).
Proof: the fixed-pair forgetful functor is right adjoint to the exact coproduct of
Frobenius iterates, so preserves K-injectives by
lem-sf-fixed-pair-derived-forget-comparison. Apply encoding_exact_derived to its image.
Exactness of both functors also preserves a resolution quasi-isomorphism. -/
theorem weil_resolution_comparison (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙
        encoding l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).mapHomologicalComplex
          (.up ℤ)).obj I) := by
  have := hI
  let := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let E := encoding l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have : CochainComplex.IsKInjective ((U.mapHomologicalComplex (.up ℤ)).obj I) :=
    inferInstance
  have : CochainComplex.IsKInjective
      ((E.mapHomologicalComplex (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
  exact CochainComplex.isKInjective_of_iso
    (L₁ := (E.mapHomologicalComplex (.up ℤ)).obj
      ((U.mapHomologicalComplex (.up ℤ)).obj I))
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ E)) (.up ℤ)).app I)

end WeilComparisons

/-- The displayed ambient derived comparisons for the actual native Weil operations.
Source: native WeilSheaf/Category.lean, LowerStar.lean:72--79, and
RightDerivedFunctor/IsoAlgebra.lean:62--97; Stacks 015F, 070I and 070Y.
(blueprint: lem-sf-native-encoding-derived-operations).

Proof:
1. The constant-scalar inverse of encoding_isEquivalence proves the specified exact
heart equivalence and encoding_exact_derived proves preservation and reflection of
K-injectives and its unbounded derived equivalence.
2. The ordinary comparison encoding_ordinary_operations uses actual precomposition
coefficient maps, including those for Frobenius. The fixed-pair framework equips
native pullback and direct image with exactly the given Frobenius transports.
3. Forgetting native Weil pullback is native pullback term by term. Localize its
ordinary comparison with encoding, giving the first displayed natural isomorphism.
4. The fixed-pair forgetful functor preserves K-injectives by
lem-sf-fixed-pair-derived-forget-comparison: its free left adjoint is the exact
coproduct of Frobenius iterates indexed by integers. Thus a native Weil K-injective
resolution remains K-injective after forgetting, and after applying encoding.
5. Apply lem-weil-pbc-kinjective-exact-square-comparison to the ordinary direct-image
square, normalized by its identity on sections. On this same resolution the two
sides are the ordinary comparison. Composing with the fixed-pair derived-forgetting
comparison gives the second displayed isomorphism. Universality makes it natural
and independent of the resolution, with the given Frobenius transport.
6. Since internal pullback is exact, its total left derived functor is its exact
termwise localization. No boundedness or constructibility is used anywhere. -/
theorem native_encoding_derived_operations
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty ((ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory ⋙ realization k₀ l X ≅
      realization k₀ l Y ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap f
            (comp_over f (Spec (CommRingCat.of k₀))))).mapDerivedCategory) ∧
    Nonempty ((ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor ⋙
      realization k₀ l Y ≅
      realization k₀ l X ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) (Scheme.Hom.geometricFiberMap f
            (comp_over f (Spec (CommRingCat.of k₀))))) ∧
    Nonempty (CondensedRing.moduleObjectDerivedPullback (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap f
            (comp_over f (Spec (CommRingCat.of k₀)))) ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap f
            (comp_over f (Spec (CommRingCat.of k₀))))).mapDerivedCategory) := by
  let g := Scheme.Hom.geometricFiberMap f
    (comp_over f (Spec (CommRingCat.of k₀)))
  have hexact := encoding_ordinary_operations l g
  obtain ⟨_, _, _, _, hlim, hcolim, _⟩ := hexact
  let := hlim
  let := hcolim
  exact ⟨⟨weilDerivedPullComparison k₀ l f⟩, ⟨weilDerivedPushComparison k₀ l f⟩,
    ⟨Functor.leftDerivedFunctorIsoMapDerivedCategory
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)⟩⟩

end AlgebraicGeometry.ProEtale.NativeEncoding
