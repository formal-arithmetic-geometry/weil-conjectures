/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.Paper.CompositionModelOrientationDefinitions

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The beta-delta identity on compatible affine charts gives the global orientation
equality once automorphisms of its Tate target are detected on open coverings.
Source: model descent Steps 7--9
(blueprint: lem-pur-model-orientation-chart-descent).

Proof: cover X by the compatible affine charts of f and g. On each chart the DNC
assembly identifies theta_h with beta_h delta_h alpha_h inverse, and identifies
alpha_(gf) kappa with sigma applied to the tensor of alpha_f and f*alpha_g.
Substitute the assumed beta-delta equation and cancel that invertible tensor of
alpha maps. Compatibility with open restriction makes this the restriction of the
global equality. The two sides are isomorphisms by composition_tensor_mate. Their
quotient is therefore an automorphism of the total Tate twist whose restrictions
are identities. The assumed detection gives the identity globally; cancel the
inverse of the right-hand side to obtain the displayed equality. For empty
X use the empty chart cover and the same detection hypothesis. -/
theorem model_orientation_chart_descent (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (hchart : ∀ (U V T : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine T]
      (f' : U ⟶ V) (g' : V ⟶ T)
      [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
      [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
      (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
        ModelChartOrientationEquation P d e f' g' aT)
    (hdetect : ModelOrientationDetection.{u, w} P X (d + e)) :
    letI := P.noetherian aZ
    letI := P.noetherian (g ≫ aZ)
    letI := Dnc.compactifiable P f (g ≫ aZ)
    letI := Dnc.compactifiable P g aZ
    letI := Dnc.compactifiable P (f ≫ g) aZ
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
        (P.modelOrientation (d + e) (f ≫ g) aZ).hom =
      (P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          (P.modelOrientation e g aZ))).hom ≫
        (P.modelOrientationMu d e f (g ≫ aZ)).hom := by sorry

end WeilConjectures.PurityFiniteSetting
