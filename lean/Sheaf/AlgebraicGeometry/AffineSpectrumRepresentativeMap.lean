/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Chain-map transport for affine spectrum representatives

Source: Stacks Project, Tags 0DJ8 and 0D5S.
(blueprint: lem-pc-affine-spectrum-representative-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

/-- Canonical representative identifications transport the coefficient chain map.

Proof: Set j=X.isoSpec.inv and j'=X'.isoSpec.inv. Naturality of isoSpec gives
(Spec.map g'.appTop) ≫ j = j' ≫ g'. The conjugates of pushforward composition
under the pinned tensor-pullback adjunctions give the underived composition
isomorphisms. Map these to complexes and combine them with the equality of
composite scheme maps to obtain an isomorphism from (Spec.map g'.appTop)*j*P
to j'*(g'*P). Compose its hom with j'*c.t to obtain t. The two assumptions on
e and e' say precisely that their inverses are the derived images of c.e.inv
and c.e'.inv followed by the pinned counits, with the quotient/localization
comparison isomorphisms inserted. Naturality of those comparisons and of the
counits, the leftDerivedLift factorization equations defining the two derived
composition comparisons, and c.represents identify Q(t) with the transported
coefficient. Cancel the invertible e and e' to obtain the displayed equation.
This construction uses no arbitrary lift of a morphism into the derived
category, no K-injectivity of N, and no quasi-coherence. Zero complexes and
empty schemes obey the same composition equations.
Source: Stacks Project, Tag 0DJ8, affine reduction; Tag 0D5S, composition of
pullbacks and compatibility of the derived counits.
(blueprint: lem-pc-affine-spectrum-representative-map). -/
theorem affineSpectrum_representative_map_eq
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ)
    (e : (DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) : schemeDerivedCategory (Spec Γ(X, ⊤))) ≅
      affineSpectrumDerivedObject X K)
    (e' : (DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N) : schemeDerivedCategory (Spec Γ(X', ⊤))) ≅
      affineSpectrumDerivedObject X' K')
    (he : e.inv = (derivedPullback X.isoSpec.inv).map c.e.inv ≫
      (derivedPullback X.isoSpec.inv).map
        ((DerivedCategory.quotientCompQhIso _).inv.app c.P) ≫
      (counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _)
    (he' : e'.inv = (derivedPullback X'.isoSpec.inv).map c.e'.inv ≫
      (derivedPullback X'.isoSpec.inv).map
        ((DerivedCategory.quotientCompQhIso _).inv.app c.N) ≫
      (counit X'.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.N) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _) :
    let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
      (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
    let t : ((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
        (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) ⟶
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N :=
      (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app c.P ≫
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).map c.t
    (counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
              (.up ℤ)).obj c.P)) ≫
        (DerivedCategory.Q (C := SheafOfModules.{u}
          (moduleRings (Spec Γ(X', ⊤)).toRingedSpace))).map t ≫ e'.hom =
        (derivedPullback (Spec.map g'.appTop)).map e.hom ≫
          affineSpectrumDerivedMorphism g' K K' φ := by
  sorry

end AlgebraicGeometry.SingleComplexBaseChange
