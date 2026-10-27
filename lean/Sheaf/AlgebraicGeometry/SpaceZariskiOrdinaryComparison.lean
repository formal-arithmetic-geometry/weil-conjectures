module

public import Sheaf.AlgebraicGeometry.RelativeDualizingTracePair
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Canonical Zariski comparisons on represented algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 071Q and 08GH; descent.tex, Tag 03FH
(blueprint: def-sfb-space-zariski-ordinary-comparison).

The right functor is actual restriction to opens. The ordinary square is normalized
by its projection to the preimage open, and all derived comparisons retain their units.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]
variable [∀ T : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]

/-- Actual restriction to all opens, through the fixed basis equivalence.
Source: Stacks 08GH (blueprint: def-sfb-space-zariski-ordinary-comparison). -/
abbrev spaceZariskiRestriction (Y : Over S) :=
  smallSchemeRestriction (schemeSpace Y) (affineIdentityChart Y)

/-- The open subscheme as a chart of its represented scheme.
Source: Stacks 03FH (blueprint: def-sfb-space-zariski-ordinary-comparison). -/
def spaceZariskiOpenChart (Y : Over S) (W : Y.left.Opens) : (schemeSpace Y).EtaleSite :=
  (schemeOpens (schemeSpace Y) (affineIdentityChart Y)).obj W

/-- Ordinary proof data needed to form the canonical tensor left adjoint. No functor
or coefficient map is freely chosen. Source: Stacks 03FH
(blueprint: def-sfb-space-zariski-ordinary-comparison). -/
structure SpaceZariskiContext (Y : Over S) where
  rightAdjoint : (spaceZariskiRestriction Y).IsRightAdjoint

/-- The adjunction-determined tensor extension.
Source: Stacks 03FH (blueprint: def-sfb-space-zariski-ordinary-comparison). -/
def SpaceZariskiContext.extension {Y : Over S} (c : SpaceZariskiContext Y) :=
  @Functor.leftAdjoint _ _ _ _ (spaceZariskiRestriction Y) c.rightAdjoint

/-- The specified ordinary tensor/restriction adjunction.
Source: Stacks 03FH (blueprint: def-sfb-space-zariski-ordinary-comparison). -/
def SpaceZariskiContext.adjunction {Y : Over S} (c : SpaceZariskiContext Y) :
    c.extension ⊣ spaceZariskiRestriction Y :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (spaceZariskiRestriction Y) c.rightAdjoint

/-- The ordinary right square is the actual projection of compatible sections onto
the preimage-open chart, including the fixed basis-equivalence counit.
Source: Stacks 03FH and 08GH
(blueprint: def-sfb-space-zariski-ordinary-comparison). -/
structure SpaceZariskiOrdinarySquare {Y' Y : Over S} (g : Y' ⟶ Y) where
  comparison : smallModuleDirectImage (traceSchemeMap g) ⋙ spaceZariskiRestriction Y ≅
    spaceZariskiRestriction Y' ⋙ RingedSpace.moduleDirectImage g.left.toLRSHom.toShHom
  chart : ∀ W : Y.left.Opens,
    ModuleChart (traceSchemeMap g) (spaceZariskiOpenChart Y W)
  chart_left : ∀ W : Y.left.Opens,
    (chart W).left = spaceZariskiOpenChart Y' (g.left ⁻¹ᵁ W)
  chart_map : ∀ W : Y.left.Opens,
    (chart W).hom.left.left =
      eqToHom (congrArg (fun V ↦ (etaleForget (schemeSpace Y')).obj V) (chart_left W)) ≫
        morphismRestrict g.left W
  sections : ∀ (M : (schemeSpace Y').SmallModules) (W : Y.left.Opens)
      (s : ((spaceZariskiRestriction Y).obj
        ((smallModuleDirectImage (traceSchemeMap g)).obj M)).val.obj (op W)),
    ((comparison.hom.app M).val.app (op W)) s =
      ((schemeSpace Y').smallModuleEquivalence.inverse.obj M).val.map
        (eqToHom (chart_left W).symm).op
        (((moduleDirectImageModel (traceSchemeMap g)).projection
          ((schemeSpace Y').smallModuleEquivalence.inverse.obj M)
          (spaceZariskiOpenChart Y W)).app (op (chart W))
          ((((schemeSpace Y).smallModuleEquivalence.unitIso.inv.app
            ((moduleDirectImage (traceSchemeMap g)).obj
              ((schemeSpace Y').smallModuleEquivalence.inverse.obj M))).val.app
                (op (spaceZariskiOpenChart Y W)) s)))

end AlgebraicGeometry.AlgebraicSpace
