/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso

/-! # Normalizing the derived unit through the open pullback square

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-unit-square-factorization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A separate step of the open counit factorization.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-unit-square-factorization).

Proof: Put P = F_h(I), beta = F.rightDerivedFunctorUnit(I), and let v be
 the homotopy tensor adjunction counit at I. Apply the pinned derived Hom-equivalence
 compatibility to the homotopy morphism v. The homotopy adjunction sends v to the
 identity of P, so its localized image followed by beta is beta itself. Injectivity
 of the derived Hom equivalence, whose inverse sends beta to Lf(beta) followed by
 the derived counit, gives
 Lf(beta) followed by a_f.counit = epsilon_f(P) followed by Qh(v).
 Let S be the composite natural isomorphism formed by the five displayed factors.
 Its naturality at beta moves Lf0(rY(beta)) from before S to rX(Lf(beta)) after S.
 First distribute Lf0 over the composite with the inverse source factorization.
 Then substitute this naturality equation, combine the two successive rX images,
 apply the normalized counit identity, and distribute rX over its two factors.
 Associativity gives exactly the displayed intermediate composite. This uses no
 tensor comparison cancellation, no boundedness, and no inverse of beta; hence it
 also applies to empty opens and the zero complex. -/
theorem singleComplexOpen_unit_square_factorization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
        (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I))) ≪≫
        (c (f ∣_ V) V.ι).app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))).hom ≫
      rX.mapDerivedCategory.map ((a f).counit.app (DerivedCategory.Qh.obj I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I))) ≪≫
        (c (f ∣_ V) V.ι).app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))).hom ≫
      rX.mapDerivedCategory.map ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
          |>.mapHomotopyCategory (.up ℤ)).counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I := by sorry

end AlgebraicGeometry
