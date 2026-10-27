/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.OpenProjectionIsoCoefficientChange
import Sheaf.Paper.OpenProjectionFactorCompositorTransport

/-! # Coefficient compatibility of the open projection factor

Source: Stacks Project, Tags 0E8I, 07A6 and 0D6D.
(blueprint: lem-sf-open-projection-factor-coefficient-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] scalarTensor scalarPull projectionOpenFactor openComparison
  proEtaleCanonicalTensorComparison

/-- Scalar extension respects the open tensor factor, including the pullback compositor.
There is no proper projection or proper direct image in this equation.

Source: Stacks Project, Tag 0E8I (open tensor identity), Tag 07A6 (mates) and
Tag 0D6D (pullback composition); step 2 of the ordinary compact-support coefficient square
(blueprint: lem-sf-open-projection-factor-coefficient-change).

Proof: first omit the pullback compositor from projectionOpenFactor and work with
openProjectionIso. Its inverse is the transpose of the open unit tensored with
identity, followed by inverse tensor/pullback comparison. The scalar/open mate
commutes with the open unit: transpose its defining restriction square through
the two scalar adjunctions and the open adjunctions. The openRestrictionMap
normalization and the adjunction triangles identify this transpose with the
scalar/pullback comparison. Apply the scalar/pullback tensor coherence to this
unit equation. Naturality of the scalar tensor comparison then identifies the
two transposes of the inverse open projection square. Injectivity of the open
hom-equivalence gives that square; invert the two openProjectionIso arrows to
obtain the forward square. No coefficient comparison or proper projection is
cancelled. Restore the compositor pull(g) pull(i) = pull(f): its compatibility
with scalarPull follows by uniqueness of the composite left adjoint. Indeed,
after taking right adjoints both routes are sectionwise pasting for restriction
and direct image; the coefficient squares and c.comm give identical maps on
each section. Naturality transports the forward square through this compositor,
yielding the displayed equation. Empty opens give zero objects, identity
changes give the unit square, and all arguments use derived scalar extension,
so quotient coefficient maps require no flatness. -/
theorem openProjectionFactor_coefficient_change
    {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (hS : S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map c.Z)).map
        (projectionOpenFactor R c aX aZ hR K L).hom ≫
      (openComparison a c.i).app (aX.tensor.obj (K, (pull R f).obj L)) ≫
      (openExtension S c.i).mapDerivedCategory.map
        ((scalarTensor (a.map X) aX bX).hom.app (K, (pull R f).obj L) ≫
          bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app L))) =
    (scalarTensor (a.map c.Z) aZ bZ).hom.app
        ((openExtension R c.i).mapDerivedCategory.obj K, (pull R c.g).obj L) ≫
      bZ.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a c.g).hom.app L)) ≫
      bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _)) ≫
      (projectionOpenFactor S c bX bZ hS
        ((pbcDerivedExtend (a.map X)).obj K)
        ((pbcDerivedExtend (a.map Y)).obj L)).hom := by
  have ht := openProjectionFactor_compositor_transport a c aX aZ bX bZ hR hS K L
  have hc := openProjectionIso_coefficient_change a c.i aX aZ bX bZ K
    ((pull R c.g).obj L)
  calc
    _ = _ := ht.1
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
        (openExtension S c.i).mapDerivedCategory.map
          (bX.tensor.map (Prod.mkHom (𝟙 _)
            ((pull S c.i).map ((scalarPull a c.g).hom.app L) ≫
              ((geometricPullComposition S c.i c.g hS).symm ≪≫
                eqToIso (congrArg (fun g : X ⟶ Y ↦ pull S g) c.comm.symm)).hom.app
                  ((pbcDerivedExtend (a.map Y)).obj L))))) hc
    _ = _ := ht.2

end WeilConjectures.PurCompactSupport
