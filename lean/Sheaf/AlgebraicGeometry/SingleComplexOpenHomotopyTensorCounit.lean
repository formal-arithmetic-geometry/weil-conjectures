/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenDirectImageUnit
public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Sectionwise counit identity for the open tensor comparison

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-homotopy-tensor-counit).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The inverse tensor restriction comparison is the mate of the sectionwise
open direct-image comparison, evaluated on a homotopy complex. All arrows here
are in homotopy categories; there are no derived-category arrows or units.

Source: Stacks Project, Tags 08FE (sectionwise direct-image restriction), 08HY
(counit description of the mate), and 0D5S (tensor composition).
(blueprint: lem-pc-k3-open-homotopy-tensor-counit).

Proof: Expand openPinnedTensorRestrictionIso into its four factors: inverse open
pullback comparison on X, inverse tensor composition along the source inclusion,
tensor composition along the restricted morphism and the target inclusion, and
open pullback comparison on Y. The tensor composition factors are conjugates of
pushforwardComp under the chosen tensor adjunctions. The open comparison is the
unique left-adjoint comparison with exact restriction. Consequently the mate of
the inverse composite is pushforwardComp followed by transport across
morphismRestrict_ι followed by inverse pushforwardComp, with the open restriction
identifications inserted. This is singleComplexOpenUnderivedDirectImageIso:
on every open W of V both components identify sections over f inverse image W.
The counit equation for mates therefore says that the inverse tensor comparison
followed by restriction of the f counit equals pullback of the direct-image
comparison followed by the restricted-morphism counit. Apply the termwise complex
functors; their counits act degreewise by the module counits, and the comparison
commutes with differentials by naturality. Descend through the homotopy quotient
and insert the canonical mapHomotopyCategoryCompIso factors. Their composition
identities yield the displayed equality for every I. Empty or top opens and the
zero complex use the same identities; no flatness or boundedness is assumed. -/
theorem singleComplexOpen_homotopy_tensor_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let b := Adjunction.mapHomotopyCategory (.up ℤ)
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    let b₀ := Adjunction.mapHomotopyCategory (.up ℤ)
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
    (openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
      (rX.mapHomotopyCategory (.up ℤ)).map (b.counit.app I) =
    ((Scheme.Modules.tensorPullback (f ∣_ V)).mapHomotopyCategory (.up ℤ)).map
        ((singleComplexOpenHomotopyDirectImageIso f V).hom.app I) ≫
      b₀.counit.app ((rX.mapHomotopyCategory (.up ℤ)).obj I) := by sorry

end AlgebraicGeometry
