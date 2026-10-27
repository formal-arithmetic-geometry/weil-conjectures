module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Algebraic-space properties tested on representable stack morphisms

Source: Stacks Project, stacks-properties.tex, Section 04XB, definition preceding
Tag 04XC and Tag 04XC (blueprint: def-sfb-representable-space-property-test).

The property is applied to the entire algebraic-space projection, retaining its
comparison with the actual 2-fibre product. No source-chart locality is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- A presentation of base change to an algebraic space, with its specified projection.
Source: Stacks Project, Section 04XB, Tag 04XC
(blueprint: def-sfb-representable-space-property-test). -/
def HasSpaceTargetBaseChange {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) (W : AlgebraicSpace S)
    (q : BasedFunctor (discreteModuli W.obj.obj) G)
    (V : AlgebraicSpace S) (p : V ⟶ W) : Prop :=
  ∃ e : BasedFunctor (discreteModuli V.obj.obj) (moduliTwoFiberProduct q f),
    e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst q f)) (discreteModuliMap p.hom.hom))

/-- A representable morphism has an algebraic-space property when every scheme base
change has that property on its actual projection to the test scheme.
Source: Stacks Project, Section 04XB, definition preceding Tag 04XC
(blueprint: def-sfb-representable-space-property-test). -/
def ModuliAlgebraicSpaceTest {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t Z p ∧ P (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T)

end CategoryTheory
