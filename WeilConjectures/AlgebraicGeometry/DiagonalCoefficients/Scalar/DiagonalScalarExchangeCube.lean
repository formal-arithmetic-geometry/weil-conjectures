/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Scalar extension and the normalized model exchange cube

## Implementation details

- Transposing along the scalar adjunctions reduces the cube to a cube of restriction
  isomorphisms (`pushHomOfComapIso_cube`).
- A canonical restriction square is the mate of the derived restriction/pullback comparison
  along the derived upper/lower adjunctions: its unit normalization follows from the
  levelwise mate computation, and it is unique by the universal property of the model.
- The remaining cube of mates (`mateEquiv_app_cube`) reduces to the compatibility of the
  restriction/pullback comparison with the pullback composition isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
  (a : R ⟶ T) [IsMonHom a]

/-- The unit transpose of the mate of a restriction isomorphism. -/
private theorem unit_comp_map_pushHomOfComapIso_app {A B C D : Type*} [Category* A]
    [Category* B] [Category* C] [Category* D] {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    (adj : L ⊣ U) (adj' : L' ⊣ U') {G : A ⥤ C} {H : B ⥤ D} (κ : H ⋙ U' ≅ U ⋙ G) (K : A) :
    adj'.unit.app (G.obj K) ≫ U'.map ((Adjunction.pushHomOfComapIso adj adj' κ).app K) =
      G.map (adj.unit.app K) ≫ κ.inv.app (L.obj K) :=
  (unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ κ.inv) K).symm

/-- Mates along scalar adjunctions turn a cube of restriction isomorphisms and exchange maps
into the corresponding cube of scalar extensions. -/
private theorem pushHomOfComapIso_cube
    {DX DS DX' DS' EX ES EX' ES' : Type*} [Category* DX] [Category* DS] [Category* DX']
    [Category* DS'] [Category* EX] [Category* ES] [Category* EX'] [Category* ES']
    {LX : DX ⥤ EX} {UX : EX ⥤ DX} {LS : DS ⥤ ES} {US : ES ⥤ DS}
    {LX' : DX' ⥤ EX'} {UX' : EX' ⥤ DX'} {LS' : DS' ⥤ ES'} {US' : ES' ⥤ DS'}
    (aX : LX ⊣ UX) (aS : LS ⊣ US) (aX' : LX' ⊣ UX') (aS' : LS' ⊣ US')
    {F : DX ⥤ DS} {F' : DX' ⥤ DS'} {FT : EX ⥤ ES} {FT' : EX' ⥤ ES'}
    {P : DS ⥤ DS'} {Q : DX ⥤ DX'} {PT : ES ⥤ ES'} {QT : EX ⥤ EX'}
    (ξ : F ⋙ P ⟶ Q ⋙ F') (ξT : FT ⋙ PT ⟶ QT ⋙ FT')
    (κS : PT ⋙ US' ≅ US ⋙ P) (κX : QT ⋙ UX' ≅ UX ⋙ Q)
    (ι : FT ⋙ US ≅ UX ⋙ F) (ι' : FT' ⋙ US' ≅ UX' ⋙ F')
    (h : ∀ M, κS.inv.app (FT.obj M) ≫ US'.map (ξT.app M) ≫ ι'.hom.app (QT.obj M) =
      P.map (ι.hom.app M) ≫ ξ.app (UX.obj M) ≫ F'.map (κX.inv.app M)) (K : DX) :
    (Adjunction.pushHomOfComapIso aS aS' κS).app (F.obj K) ≫
        PT.map ((Adjunction.pushHomOfComapIso aX aS ι).app K) ≫ ξT.app (LX.obj K) =
      LS'.map (ξ.app K) ≫ (Adjunction.pushHomOfComapIso aX' aS' ι').app (Q.obj K) ≫
        FT'.map ((Adjunction.pushHomOfComapIso aX aX' κX).app K) := by
  have h' : κS.inv.app (FT.obj (LX.obj K)) ≫ US'.map (ξT.app (LX.obj K)) =
      P.map (ι.hom.app (LX.obj K)) ≫ ξ.app (UX.obj (LX.obj K)) ≫
        F'.map (κX.inv.app (LX.obj K)) ≫ ι'.inv.app (QT.obj (LX.obj K)) := by
    rw [← reassoc_of% (h (LX.obj K)), Iso.hom_inv_id_app]
    simp
  have u₀ := unit_comp_map_pushHomOfComapIso_app aS aS' κS (F.obj K)
  have u₃ := unit_comp_map_pushHomOfComapIso_app aX' aS' ι' (Q.obj K)
  have n₀ := aS'.unit.naturality (ξ.app K)
  have n₁ := κS.inv.naturality ((Adjunction.pushHomOfComapIso aX aS ι).app K)
  have n₂ := ι'.inv.naturality ((Adjunction.pushHomOfComapIso aX aX' κX).app K)
  have u₁ := unit_comp_map_pushHomOfComapIso_app aX aS ι K
  have u₂ := unit_comp_map_pushHomOfComapIso_app aX aX' κX K
  have n₃ := ξ.naturality (aX.unit.app K)
  apply (aS'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at n₀ n₁ n₂ u₀ u₁ u₂ u₃ n₃ h' ⊢
  simp only [Functor.map_comp]
  rw [reassoc_of% u₀, ← reassoc_of% n₀, reassoc_of% u₃, ← reassoc_of% n₁, ← n₂,
    ← P.map_comp_assoc, u₁,
    P.map_comp_assoc, h', ← F'.map_comp_assoc, u₂, F'.map_comp_assoc, ← reassoc_of% n₃]
  simp only [← P.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- Exact functors send quasi-isomorphisms between K-injective complexes to isomorphisms. -/
private theorem kInjectives_derives {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro I J f hf
  have : I.obj.IsKInjective := I.property
  have : J.obj.IsKInjective := J.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  exact (inferInstance : IsIso
    (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom)))

/-- The levelwise derived adjunction is the derived upper/lower adjunction, transported
along the exactness of inverse image. -/
private theorem mapDerivedCategoryRightDerivedAdjunction_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f) := by
  unfold CondensedRing.derivedUpperStarLowerStarAdjunction
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  refine Adjunction.derived_eq_ofNatIsoLeft
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.symm ?_
  ext K
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

/-- Mates along adjunctions with modified left adjoints. -/
private lemma mate_ofNatIsoLeft'
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α) =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

/-- The canonical restriction/direct-image comparison: the mate of the derived
restriction/pullback comparison along the derived upper/lower adjunctions. -/
private def restrictionLowerComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    derivedLower T f ⋙ (Mod.comap (coefficientMap a S)).mapDerivedCategory ⟶
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙ derivedLower R f :=
  mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction T f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
    (CondensedRing.derivedComapLeftDerivedUpperStarIso a f).hom

/-- The canonical comparison is the mate of the levelwise restriction/pullback comparison. -/
private theorem restrictionLowerComparison_eq {X S : Scheme.{u}} (f : X ⟶ S) :
    restrictionLowerComparison a f =
      mateEquiv
        (CondensedRing.upperStarLowerStarAdjunction T f).mapDerivedCategoryRightDerivedAdjunction
        (CondensedRing.upperStarLowerStarAdjunction R f).mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (CondensedRing.comapUpperStarIso a f).symm).hom) := by
  rw [mapDerivedCategoryRightDerivedAdjunction_eq, mapDerivedCategoryRightDerivedAdjunction_eq,
    mate_ofNatIsoLeft']
  unfold restrictionLowerComparison
  congr 1
  ext K
  simp [CondensedRing.derivedComapLeftDerivedUpperStarIso_hom_app, TwoSquare.whiskerRight,
    TwoSquare.whiskerLeft, CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory]

/-- The canonical comparison satisfies the unit normalization of a restriction square. -/
private theorem restrictionLowerComparison_normalization {X S : Scheme.{u}} (f : X ⟶ S)
    (P : CochainComplex (Modules T X) ℤ) :
    (Mod.comap (coefficientMap a S)).mapDerivedCategory.map
        ((CondensedRing.lowerStar T f).rightDerivedFunctorUnitQ P) ≫
      (restrictionLowerComparison a f).app (DerivedCategory.Q.obj P) ≫
      (derivedLower R f).map
        ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactors.hom.app P) =
    (Mod.comap (coefficientMap a S)).mapDerivedCategoryFactors.hom.app
        (((CondensedRing.lowerStar T f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (CondensedRing.comapLowerStarIso a f).hom (.up ℤ)).app P) ≫
      (CondensedRing.lowerStar R f).rightDerivedFunctorUnitQ
        (((Mod.comap (coefficientMap a X)).mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := derived_mate_factors
    (CondensedRing.upperStarLowerStarAdjunction T f)
    (CondensedRing.upperStarLowerStarAdjunction R f)
    (CondensedRing.comapUpperStarIso a f).symm P
  simp only [Iso.symm_hom] at h
  rw [CondensedRing.comapUpperStarIso_mate] at h
  rw [restrictionLowerComparison_eq]
  simpa only [chainDerivedUnit, Functor.rightDerivedFunctorUnitQ, derivedLower] using h

universe a v w wc in
/-- The comparison of an exact square of models is unique given its unit normalization. -/
private theorem exactSquare_iso_hom_eq
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    [Abelian.HasKInjectiveResolutions A]
    {F : A ⥤ B} {G : C ⥤ D} [F.Additive] [G.Additive]
    {U : A ⥤ C} {V : B ⥤ D} [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {RF : DiagonalRightDerived F} {RG : DiagonalRightDerived G}
    {e : F ⋙ V ≅ U ⋙ G}
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG e)
    (c : RF.R ⋙ V.mapDerivedCategory ⟶ U.mapDerivedCategory ⋙ RG.R)
    (hc : ∀ P : CochainComplex A ℤ, V.mapDerivedCategory.map (RF.η.app P) ≫
        c.app (DerivedCategory.Q.obj P) ≫ RG.R.map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
        RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P)) :
    s.iso.hom = c := by
  let eta : (F ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (RF.R ⋙ V.mapDerivedCategory) :=
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      V.mapDerivedCategoryFactors.inv ≫ Functor.whiskerRight RF.η V.mapDerivedCategory
  have : (RF.R ⋙ V.mapDerivedCategory).IsRightDerivedFunctor eta
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (kInjectives_derives (F ⋙ V)).isRightDerivedFunctor_of_isIso eta
    intro I
    have := RF.computation I.obj I.property
    exact (inferInstance : IsIso (V.mapDerivedCategoryFactors.inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫ V.mapDerivedCategory.map (RF.η.app I.obj)))
  apply Functor.rightDerived_ext _ eta (HomologicalComplex.quasiIso A (.up ℤ))
  ext P
  have hh := (s.normalization P).trans (hc P).symm
  rw [← Category.assoc, ← Category.assoc, cancel_mono] at hh
  simp only [eta, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  exact congrArg (fun k ↦ V.mapDerivedCategoryFactors.inv.app _ ≫ k) hh

/-- The exact restriction/pullback comparison inverts the derived one. -/
private theorem scalarRestrictionPullbackIso_inv_app {X S : Scheme.{u}} (f : X ⟶ S)
    (M : DerivedCategory (Modules T S)) :
    (scalarRestrictionPullbackIso a f).inv.app M =
      (CondensedRing.derivedComapLeftDerivedUpperStarIso a f).hom.app M := by
  simp [scalarRestrictionPullbackIso, CondensedRing.derivedComapLeftDerivedUpperStarIso_hom_app,
    CondensedRing.derivedComapUpperStarIso, CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.mapDerivedCategoryNatIso_symm]

/-- Restriction commutes with transport of derived inverse images along an equality of
morphisms. -/
private theorem derivedComapLeftDerivedUpperStarIso_eqToHom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y}
    (h : g = g') (N : DerivedCategory (Modules T Y))
    (p : (derivedUpper T g).obj N = (derivedUpper T g').obj N)
    (p' : (derivedUpper R g).obj ((Mod.comap (coefficientMap a Y)).mapDerivedCategory.obj N) =
      (derivedUpper R g').obj ((Mod.comap (coefficientMap a Y)).mapDerivedCategory.obj N)) :
    (CondensedRing.derivedComapLeftDerivedUpperStarIso a g).hom.app N ≫
        (Mod.comap (coefficientMap a Z)).mapDerivedCategory.map (eqToHom p) =
      eqToHom p' ≫ (CondensedRing.derivedComapLeftDerivedUpperStarIso a g').hom.app N := by
  subst h
  simp

/-- Pasting two triangles with a middle square, written with explicit inverses. -/
private theorem paste_comp_triangles {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {a₀ a₁ a₂ a₀' a₃ a₄ : D} {b₀ b₁ b₀' b₂ : C}
    {Ahom : a₀ ⟶ a₁} {Ainv : a₁ ⟶ a₀} {x : a₁ ⟶ a₂} {y : a₂ ⟶ P.obj b₁}
    {t₁ : a₀ ⟶ P.obj b₀} {Bhom : b₀ ⟶ b₁} {Binv : b₁ ⟶ b₀} {E : b₀ ⟶ b₀'} {E' : a₀ ⟶ a₀'}
    {t₂ : a₀' ⟶ P.obj b₀'} {Chom : a₀' ⟶ a₃} {z : a₃ ⟶ a₄} {w : a₄ ⟶ P.obj b₂}
    {Dhom : b₀' ⟶ b₂}
    (c₁ : Ahom ≫ x ≫ y = t₁ ≫ P.map Bhom) (c₂ : Chom ≫ z ≫ w = t₂ ≫ P.map Dhom)
    (hA : Ainv ≫ Ahom = 𝟙 a₁) (hB : Bhom ≫ Binv = 𝟙 b₀) (hc : t₁ ≫ P.map E = E' ≫ t₂) :
    x ≫ y ≫ P.map Binv ≫ P.map E ≫ P.map Dhom = Ainv ≫ E' ≫ Chom ≫ z ≫ w := by
  rw [c₂, ← reassoc_of% hc]
  calc x ≫ y ≫ P.map Binv ≫ P.map E ≫ P.map Dhom
      = Ainv ≫ (Ahom ≫ x ≫ y) ≫ P.map Binv ≫ P.map E ≫ P.map Dhom := by
        simp only [Category.assoc, reassoc_of% hA]
    _ = Ainv ≫ t₁ ≫ P.map E ≫ P.map Dhom := by
        rw [c₁, Category.assoc, ← P.map_comp_assoc, hB, P.map_id, Category.id_comp]

/-- The cube of restriction isomorphisms with the canonical exchange maps commutes. -/
private theorem restriction_exchange_cube {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) (M : DerivedCategory (Modules T X)) :
    (scalarRestrictionPullbackIso a hS).inv.app ((derivedLower T f).obj M) ≫
      (Mod.comap (coefficientMap a S')).mapDerivedCategory.map
        ((derivedExchange T f f' hX hS h).app M) ≫
      (restrictionLowerComparison a f').app ((derivedUpper T hX).obj M) =
    (derivedUpper R hS).map ((restrictionLowerComparison a f).app M) ≫
      (derivedExchange R f f' hX hS h).app
        ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj M) ≫
      (derivedLower R f').map ((scalarRestrictionPullbackIso a hX).inv.app M) := by
  unfold derivedExchange restrictionLowerComparison
  rw [Adjunction.exchangeRight_eq_mateEquiv, Adjunction.exchangeRight_eq_mateEquiv]
  refine mateEquiv_app_cube _ _ _ _ _ _ _ _ (scalarRestrictionPullbackIso a hS).inv
    (scalarRestrictionPullbackIso a hX).inv ?_ M
  intro N
  simp only [TwoSquare.mk, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    scalarRestrictionPullbackIso_inv_app, Functor.map_comp, Category.assoc]
  refine paste_comp_triangles _
    (CondensedRing.derivedComapLeftDerivedUpperStarIso_comp_hom_app a f' hS N)
    (CondensedRing.derivedComapLeftDerivedUpperStarIso_comp_hom_app a hX f N) ?_ ?_ ?_
  · simp
  · simp
  · simp only [CondensedRing.upperStarCongr, Functor.leftDerivedFunctorNatIso_eqToIso_hom_app]
    exact derivedComapLeftDerivedUpperStarIso_eqToHom a h N _ _

/-- A restriction square between canonical models is the canonical comparison. -/
private theorem restrictionSquare_iso_hom {X S : Scheme.{u}} (f : X ⟶ S)
    (D₀ : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D : DiagonalRightDerived (CondensedRing.lowerStar T f))
    (e₀ : D₀.R = derivedLower R f) (e : D.R = derivedLower T f)
    (he₀ : IsCanonicalRightDerived (CondensedRing.lowerStar R f) D₀ e₀)
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar T f) D e)
    (r : RestrictionSquare a f D₀ D) (M : DerivedCategory (Modules T X)) :
    r.iso.hom.app M = (Mod.comap (coefficientMap a S)).mapDerivedCategory.map
        ((eqToIso e).hom.app M) ≫ (restrictionLowerComparison a f).app M ≫
      (eqToIso e₀).inv.app ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj M) := by
  cases D₀
  cases D
  dsimp only at e₀ e
  subst e₀ e
  have h := exactSquare_iso_hom_eq r (restrictionLowerComparison a f) (fun P ↦ by
    have h₀ := he₀ ((Mod.comap (coefficientMap a X)).mapHomologicalComplex (.up ℤ) |>.obj P)
    have h₁ := he P
    simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app] at h₀ h₁
    erw [Category.comp_id] at h₀ h₁
    dsimp only
    rw [h₀, h₁]
    exact restrictionLowerComparison_normalization a f P)
  simp [h]

/-- Scalar extension commutes with the normalized geometric exchange mate.
This is an equality of comparisons on arbitrary derived objects and contains
no trace, invertibility assertion, or line endpoint. -/
theorem scalar_model_exchange_cube
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D₀ : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D₀' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (D : DiagonalRightDerived (CondensedRing.lowerStar T f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar T f'))
    (e₀ : D₀.R = derivedLower R f) (e₀' : D₀'.R = derivedLower R f')
    (e : D.R = derivedLower T f) (e' : D'.R = derivedLower T f')
    (he₀ : IsCanonicalRightDerived (CondensedRing.lowerStar R f) D₀ e₀)
    (he₀' : IsCanonicalRightDerived (CondensedRing.lowerStar R f') D₀' e₀')
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar T f) D e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar T f') D' e')
    (r : RestrictionSquare a f D₀ D) (r' : RestrictionSquare a f' D₀' D')
    (K : DerivedCategory (Modules R X)) :
    (scalarPullbackComparison a hS).app (D₀.R.obj K) ≫
        (derivedUpper T hS).map ((r.mate a).app K) ≫
        modelExchange T f f' hX hS h D D' e e' ((derivedScalars a X).obj K) =
      (derivedScalars a S').map (modelExchange R f f' hX hS h D₀ D₀' e₀ e₀' K) ≫
        (r'.mate a).app ((derivedUpper R hX).obj K) ≫
        D'.R.map ((scalarPullbackComparison a hX).app K) := by
  cases D₀
  cases D₀'
  cases D
  cases D'
  dsimp only at e₀ e₀' e e'
  subst e₀ e₀' e e'
  have hr (M : DerivedCategory (Modules T X)) :
      r.iso.hom.app M = (restrictionLowerComparison a f).app M := by
    rw [restrictionSquare_iso_hom a f _ _ rfl rfl he₀ he r M]
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hr' (M : DerivedCategory (Modules T X')) :
      r'.iso.hom.app M = (restrictionLowerComparison a f').app M := by
    rw [restrictionSquare_iso_hom a f' _ _ rfl rfl he₀' he' r' M]
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  unfold scalarPullbackComparison RestrictionSquare.mate modelExchange
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id]
  refine pushHomOfComapIso_cube _ _ _ _ (derivedExchange R f f' hX hS h)
    (derivedExchange T f f' hX hS h) _ _ r.iso r'.iso (fun M ↦ ?_) K
  rw [hr, hr']
  exact restriction_exchange_cube a f f' hX hS h M

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
