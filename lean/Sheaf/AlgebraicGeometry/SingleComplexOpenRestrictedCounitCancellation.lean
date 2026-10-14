/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import Sheaf.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # Cancelling the restricted homotopy counit comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A separate step of the open counit factorization.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).

Proof: Put P = F_h(I), let v be the homotopy tensor adjunction counit at I,
 and write t for the homotopy tensor restriction isomorphism. Apply
 open_pinned_counit_homotopy_restriction to P and the restricted square. Its identity
 input contributes only an identity map, so its left side is S(Qh(P)) followed by
 rX(epsilon_f(P)), the target restriction factorization at the homotopy pullback of
 P, and Qh(t.hom(P)). Its right side is Lf0 of the source restriction factorization
 followed by epsilon_f0(rY_h(P)). Precompose both sides with Lf0 of the inverse
 source restriction factorization, and postcompose both sides with Qh(t.inv(P)).
 Functoriality and the inverse identities cancel the source factorization and the
 pair t.hom, t.inv. Next postcompose with Qh(rX_h(v)). Naturality of the target
 restriction factorization at v identifies its composite with this arrow with
 rX(Qh(v)) followed by the restriction factorization at I. Finally combine the two
 Qh images on the right by functoriality. This gives precisely the asserted
 equality. No derived unit or derived-adjunction counit occurs. All cancellations
 are of isomorphisms, so empty opens and zero complexes require no exceptions. -/
theorem singleComplexOpen_restricted_counit_cancellation
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
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (ε (f ∣_ V)).app ((rY.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
            (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          (rX.mapHomotopyCategory (.up ℤ)).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
              |>.mapHomotopyCategory (.up ℤ)).counit.app I)) := by sorry

end AlgebraicGeometry
