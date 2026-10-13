/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenDirectImageUnit
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction

/-! # The open pullback square evaluated on a direct-image representative

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-e2-open-pullback-counit-representative).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The pullback-composition route, after the direct-image unit, is the localization
of the sectionwise counit. This calculation does not use the derived open direct-image
comparison: it compares the explicit pullback factors with the underived adjunction.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-e2-open-pullback-counit-representative).

Proof: Write F for module direct image along f, F0 for direct image along f restricted
to V, and rX,rY for exact open restriction. On the homotopy category the sectionwise
comparison e identifies rY(F(I)) with F0(rX(I)). The tensor adjunctions transpose e
to the pullback square. Indeed the composition comparisons for tensor pullback are
conjugates of pushforward composition, and the open pullback comparison is the unique
left-adjoint comparison with exact restriction. Evaluate on sections: both routes
send a local tensor a tensor x to a times the restriction of x. Thus their composite
with the underived counit is the same morphism. Apply Qh and use the left-derived
counit factorization for each composition comparison. Cancel the open-restriction
factorization isomorphisms, and use naturality of the recorded right-derived unit.
The pinning of the derived Hom equivalence identifies the derived counit after that
unit with the left-derived counit followed by Qh of the underived counit. These
factorizations yield exactly the displayed equality. The calculation works for every
homotopy-category I: it uses the unit, not its inverse, and needs no resolution or
boundedness assumption. Empty opens and zero complexes satisfy the same sectionwise
identity, so no exceptional cases are excluded. -/
theorem singleComplexOpen_pullback_counit_representative
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ := (Classical.choose exists_derivedPullbackComposition) (f ∣_ V)
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
      rX.mapDerivedCategory.map ((a f).counit.app (DerivedCategory.Qh.obj I)) =
    (derivedPullback (f ∣_ V)).map
        (DerivedCategory.Qh.map ((singleComplexOpenHomotopyDirectImageIso f V).hom.app I)) ≫
      (ε (f ∣_ V)).app ((F₀.mapHomotopyCategory (.up ℤ)).obj
        ((rX.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
          |>.mapHomotopyCategory (.up ℤ)).counit.app
          ((rX.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategoryFactorsh.inv.app I := by sorry

end AlgebraicGeometry
