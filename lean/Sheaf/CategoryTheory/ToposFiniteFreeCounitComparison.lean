module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates
public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.CategoryTheory.ExactSquareDerivedCounit
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Finite-free counit comparison on arbitrary sheaf topoi

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL; Derived Categories,
Tags 08BJ and 09T5. The specified finite-coordinate calculation is the one in the
DAG proof (blueprint: lem-sfb-topos-finite-free-counit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w vA uA
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules.RingedTensor

/-- A finite biproduct inclusion in the finite-product presentation of an additive category.
Source: Stacks, Categories, finite biproduct identities
(blueprint: lem-sfb-topos-finite-free-counit-comparison). -/
def finitePowerInclusion {A : Type uA} [Category.{vA} A] [Preadditive A]
    [HasFiniteProducts A] (d : ℕ) (M : A) (i : Fin d) :
    M ⟶ ∏ᶜ (fun _ : Fin d ↦ M) :=
  Pi.lift (fun j : Fin d ↦ if i = j then 𝟙 M else 0)

/-- The counit mate is the finite-sum comparison in the specified scalar coordinates.
All adjunctions and comparisons below are normalized by their underlying sheaf maps
or by their localization maps, so none is an arbitrary isomorphism.
Source: Stacks 03D7, 03EL, 08BJ, 09T5
(blueprint: lem-sfb-topos-finite-free-counit-comparison).

Proof:
1. Ordinary extension and restriction are adjoint (lem-pur-sheaf-ring-coefficient-
   ordinary-adjunction); finite-free coordinates make extension exact. The pulled
   frame is obtained by inverse image. The two inverse images are exact by
   lem-trf-geometric-inverse-image-exact. The ordinary module adjunctions are those
   of lem-weil-pbc-ringed-topoi-module-adjunction. Restriction leaves the underlying
   geometric direct image and its evaluation counit unchanged, giving c and rho.
2. Small-site module sheaves have unbounded K-injective resolutions
   (prop-pur-kinjective-resolutions-exist). Exact extension implies that restriction
   preserves K-injectives (lem-weil-pbc-right-adjoint-preserves-kinjective).
   Compute both composites on these resolutions using c, obtaining d. The
   K-injective Hom comparison (lem-weil-pbc-kinjective-hom-derived) makes d natural
   and independent of representatives (lem-weil-pbc-kinjective-total-derived).
3. The ordinary evaluation counits agree under c and rho. Apply
   lem-weil-pbc-exact-square-derived-counit and the localization comparisons of
   lem-weil-pbc-exact-functor-derived-factorization. The resulting derived counit
   equality implies the displayed equality of adjoint transposes.
4. Normalize chi by balancing (lem-sfb-kflat-scalar-comparison-normalization), and
   Phi by lem-sfb-derived-finite-free-scalar-coordinates on every representative.
   On the ith basis insertion the restricted pullback/tensor map inserts the
   pulled-back basis vector in the ith slot. After the R-counit its transpose is
   inclusion_i composed with the R-counit. The transpose of G_R(inclusion_i) is
   the same by naturality. Injectivity of the adjunction bijection gives the
   inclusion identity, and the finite coproduct property gives the matrix formula.
5. A right adjoint preserves finite products and zero objects
   (lem-weil-pbc-right-adjoint-preserves-limits). The biproduct matrix identities
   prove both inverse equations for the displayed sum. For d = 0 these are the
   unique maps between zero objects and the empty sums give their identities.
6. Exact scalar restriction commutes with cohomology and reflects isomorphisms
   on module sheaves. Thus it reflects derived isomorphisms by
   lem-weil-pbc-unbounded-derived-iso-cohomology. The coordinate equality and the
   inverse equations imply that gamma is invertible for every unbounded K.
-/
theorem topos_finiteFree_counit_comparison
    {CY CX : Type u} [SmallCategory CY] [SmallCategory CX]
    {JY : GrothendieckTopology CY} {JX : GrothendieckTopology CX}
    (h : GeometricMorphism (Sheaf JX (Type u)) (Sheaf JY (Type u)))
    {RY SY : Sheaf JY CommRingCat.{u}} {RX SX : Sheaf JX CommRingCat.{u}}
    (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (IR : AlgebraicInverseImage h.inverse RY RX)
    (IS : AlgebraicInverseImage h.inverse SY SX)
    (ha : h.inverse.map ((sheafCompose JY (CategoryTheory.forget CommRingCat)).map aY) ≫
      IS.ringUnderlying.hom = IR.ringUnderlying.hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat)).map aX)
    (d : ℕ)
    (θY : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf RY)) ≅
      (restriction.{u, u} aY).obj (unit (ringSheaf SY)))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf RY))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf SY))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf RX))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (ringSheaf SX))]
    (EY : DerivedCategory (SheafOfModules.{u} (ringSheaf RY)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf SY)))
    (EX : DerivedCategory (SheafOfModules.{u} (ringSheaf RX)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringSheaf SX)))
    (εY : DerivedCategory.Q ⋙ EY ⟶
      (tensorFunctor aY).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εX : DerivedCategory.Q ⋙ EX ⟶
      (tensorFunctor aX).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [EY.IsLeftDerivedFunctor εY
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf RY)) (.up ℤ))]
    [EX.IsLeftDerivedFunctor εX
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf RX)) (.up ℤ))] :
    ∃ (_ : IR.modules.Additive) (_ : IS.modules.Additive)
      (_ : PreservesFiniteLimits IR.modules) (_ : PreservesFiniteColimits IR.modules)
      (_ : PreservesFiniteLimits IS.modules) (_ : PreservesFiniteColimits IS.modules)
      (_ : PreservesFiniteLimits (restriction.{u, u} aY))
      (_ : PreservesFiniteColimits (restriction.{u, u} aY))
      (_ : PreservesFiniteLimits (restriction.{u, u} aX))
      (_ : PreservesFiniteColimits (restriction.{u, u} aX))
      (HR : SheafOfModules.{u} (ringSheaf RX) ⥤ SheafOfModules.{u} (ringSheaf RY))
      (HS : SheafOfModules.{u} (ringSheaf SX) ⥤ SheafOfModules.{u} (ringSheaf SY))
      (_ : HR.Additive) (_ : HS.Additive)
      (adjR : IR.modules ⊣ HR) (adjS : IS.modules ⊣ HS)
      (pR : HR ⋙ underlying RY ≅ underlying RX ⋙ h.direct)
      (pS : HS ⋙ underlying SY ≅ underlying SX ⋙ h.direct),
    (∀ (M : SheafOfModules.{u} (ringSheaf RY))
      (N : SheafOfModules.{u} (ringSheaf RX)) (f : IR.modules.obj M ⟶ N),
      (underlying RY).map (adjR.homEquiv M N f) ≫ pR.hom.app N =
        h.adj.homEquiv _ _ (IR.moduleUnderlying.inv.app M ≫ (underlying RX).map f)) ∧
    (∀ (M : SheafOfModules.{u} (ringSheaf SY))
      (N : SheafOfModules.{u} (ringSheaf SX)) (f : IS.modules.obj M ⟶ N),
      (underlying SY).map (adjS.homEquiv M N f) ≫ pS.hom.app N =
        h.adj.homEquiv _ _ (IS.moduleUnderlying.inv.app M ≫ (underlying SX).map f)) ∧
    ∃ (ρ : restriction.{u, u} aY ⋙ IR.modules ≅ IS.modules ⋙ restriction.{u, u} aX)
      (c : HS ⋙ restriction.{u, u} aY ≅ restriction.{u, u} aX ⋙ HR),
    (∀ N : SheafOfModules.{u} (ringSheaf SY),
      (underlying RX).map (ρ.hom.app N) ≫ IS.moduleUnderlying.hom.app N =
        IR.moduleUnderlying.hom.app ((restriction.{u, u} aY).obj N)) ∧
    (∀ N : SheafOfModules.{u} (ringSheaf SX),
      (underlying RY).map (c.hom.app N) ≫ pR.hom.app ((restriction.{u, u} aX).obj N) =
        pS.hom.app N) ∧
    ∀ (GR : DerivedCategory (SheafOfModules.{u} (ringSheaf RX)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringSheaf RY)))
      (GS : DerivedCategory (SheafOfModules.{u} (ringSheaf SX)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringSheaf SY)))
      (ηR : HR.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ GR)
      (ηS : HS.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ GS)
      [GR.IsRightDerivedFunctor ηR
        (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf RX)) (.up ℤ))]
      [GS.IsRightDerivedFunctor ηS
        (HomologicalComplex.quasiIso (SheafOfModules.{u} (ringSheaf SX)) (.up ℤ))],
    ∃ (DR : IR.modules.mapDerivedCategory ⊣ GR)
      (DS : IS.modules.mapDerivedCategory ⊣ GS),
    Adjunction.HasExactDerivedHomFormula IR.modules HR adjR GR ηR DR ∧
    Adjunction.HasExactDerivedHomFormula IS.modules HS adjS GS ηS DS ∧
    ∃ (δ : GS ⋙ (restriction.{u, u} aY).mapDerivedCategory ≅
        (restriction.{u, u} aX).mapDerivedCategory ⋙ GR)
      (χ : tensorFunctor aY ⋙ IS.modules ≅ IR.modules ⋙ tensorFunctor aX)
      (β : EY ⋙ IS.modules.mapDerivedCategory ≅ IR.modules.mapDerivedCategory ⋙ EX)
      (κR : IR.modules.obj (unit (ringSheaf RY)) ≅ unit (ringSheaf RX))
      (κS : IS.modules.obj (unit (ringSheaf SY)) ≅ unit (ringSheaf SX))
      (τ : IR.modules.obj (∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf RY))) ≅
        ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf RX)))
      (θX : ∏ᶜ (fun _ : Fin d ↦ unit (ringSheaf RX)) ≅
        (restriction.{u, u} aX).obj (unit (ringSheaf SX)))
      (φY : tensorFunctor aY ⋙ restriction.{u, u} aY ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
      (φX : tensorFunctor aX ⋙ restriction.{u, u} aX ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
      (ΦY : EY ⋙ (restriction.{u, u} aY).mapDerivedCategory ≅
        Functor.const (Discrete (Fin d)) ⋙ lim)
      (ΦX : EX ⋙ (restriction.{u, u} aX).mapDerivedCategory ≅
        Functor.const (Discrete (Fin d)) ⋙ lim),
    (∀ I : CochainComplex (SheafOfModules.{u} (ringSheaf SX)) ℤ,
      I.IsKInjective →
      (restriction.{u, u} aY).mapDerivedCategory.map (ηS.app I) ≫
          δ.hom.app (DerivedCategory.Q.obj I) ≫
          GR.map ((restriction.{u, u} aX).mapDerivedCategoryFactors.hom.app I) =
        (restriction.{u, u} aY).mapDerivedCategoryFactors.hom.app
            ((HS.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I) ≫
          ηR.app (((restriction.{u, u} aX).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ (M : DerivedCategory (SheafOfModules.{u} (ringSheaf SY)))
      (N : DerivedCategory (SheafOfModules.{u} (ringSheaf SX)))
      (f : IS.modules.mapDerivedCategory.obj M ⟶ N),
      DR.homEquiv _ _
        ((Functor.mapDerivedCategorySquareIso ρ).hom.app M ≫
          (restriction.{u, u} aX).mapDerivedCategory.map f) =
        (restriction.{u, u} aY).mapDerivedCategory.map (DS.homEquiv _ _ f) ≫ δ.hom.app N) ∧
    IsScalarInverseImageComparison h.inverse IR IS aY aX χ ∧
    (∀ P : CochainComplex (SheafOfModules.{u} (ringSheaf RY)) ℤ,
      β.hom.app (DerivedCategory.Q.obj P) ≫
          EX.map (IR.modules.mapDerivedCategoryFactors.hom.app P) ≫
          εX.app ((IR.modules.mapHomologicalComplex (.up ℤ)).obj P) =
        IS.modules.mapDerivedCategory.map (εY.app P) ≫
          IS.modules.mapDerivedCategoryFactors.hom.app
            (((tensorFunctor aY).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
                (Iso.refl (tensorFunctor aY ⋙ IS.modules)) (.up ℤ)).hom.app P ≫
              (χ.hom.mapHomologicalComplex (.up ℤ)).app P ≫
              (Functor.mapHomologicalComplexCompIso
                (Iso.refl (IR.modules ⋙ tensorFunctor aX)) (.up ℤ)).inv.app P)) ∧
    ((underlying RX).map κR.hom =
      IR.moduleUnderlying.hom.app (unit (ringSheaf RY)) ≫ IR.ringUnderlying.hom) ∧
    ((underlying SX).map κS.hom =
      IS.moduleUnderlying.hom.app (unit (ringSheaf SY)) ≫ IS.ringUnderlying.hom) ∧
    (∀ i : Fin d, τ.hom ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf RX)) i =
      IR.modules.map (Pi.π (fun _ : Fin d ↦ unit (ringSheaf RY)) i) ≫ κR.hom) ∧
    (τ.hom ≫ θX.hom = IR.modules.map θY.hom ≫ ρ.hom.app (unit (ringSheaf SY)) ≫
      (restriction.{u, u} aX).map κS.hom) ∧
    IsFiniteFreeScalarCoordinateIso aY d θY φY ∧
    IsFiniteFreeScalarCoordinateIso aX d θX φX ∧
    IsDerivedFiniteFreeScalarCoordinateIso aY d EY εY φY ΦY ∧
    IsDerivedFiniteFreeScalarCoordinateIso aX d EX εX φX ΦX ∧
    ∀ K : DerivedCategory (SheafOfModules.{u} (ringSheaf RX)),
    ∃ (γ : EY.obj (GR.obj K) ⟶ GS.obj (EX.obj K))
      (σ : ∏ᶜ (fun _ : Fin d ↦ GR.obj K) ⟶ GR.obj (∏ᶜ (fun _ : Fin d ↦ K))),
      γ = DS.homEquiv _ _
        (β.hom.app (GR.obj K) ≫ EX.map (DR.counit.app K)) ∧
      (ΦY.inv.app (GR.obj K) ≫ (restriction.{u, u} aY).mapDerivedCategory.map γ ≫
        δ.hom.app (EX.obj K) ≫ GR.map (ΦX.hom.app K) = σ) ∧
      (∀ i : Fin d, finitePowerInclusion d (GR.obj K) i ≫ σ =
        GR.map (finitePowerInclusion d K i)) ∧
      (σ ≫ (∑ i : Fin d, GR.map (Pi.π (fun _ : Fin d ↦ K) i) ≫
        finitePowerInclusion d (GR.obj K) i) = 𝟙 _) ∧
      ((∑ i : Fin d, GR.map (Pi.π (fun _ : Fin d ↦ K) i) ≫
        finitePowerInclusion d (GR.obj K) i) ≫ σ = 𝟙 _) ∧
      IsIso γ := by
  sorry

end SheafOfModules.RingedTensor
