/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso

/-! # Tensor compatibility of derived pullback composition on K-flat complexes

Source: Stacks Project, cohomology.tex, Tags 079U, 08HY and 0D5S.
(blueprint: lem-sc-derived-pullback-composition-tensor-kflat).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The fixed composition comparison preserves the normalized tensorator on
localized K-flat complexes.
Source: Stacks Project, cohomology.tex, Lemma 079U and Remark 08HY;
composition of derived pullbacks as in Tag 0D5S.
(blueprint: lem-sc-derived-pullback-composition-tensor-kflat).

Proof: use the normalization equations of the three tensorators at P and N.
Their tensors and their termwise pullbacks are K-flat, so all localization tensor
maps and derived counits in those equations are invertible. The shared counit is
precisely the epsilon chosen by exists_derivedPullbackComposition, so c and the
tensorators have the same normalization. The defining leftDerivedLift equation for c identifies
its composite with the counit of the
composite arrow with the successive counits followed by the localized termwise
composition comparison. Use naturality of c for the invertible localization map
mu_Z(P,N) to replace c at Q(P) tensor Q(N) by c at Q(Tot(P tensor N)). Use naturality
of the f-tensorator in epsilon_g(P), epsilon_g(N) to replace its inputs Lg Q(P),
Lg Q(N) by Q(g*P), Q(g*N). Postcompose the two routes with the tensor of the
composite-arrow counits and the target localization tensor map. Substitute the
c-factorization at P, N and Tot(P tensor N), then the g-, f- and fg-tensorator
normalization equations. The input localization map and all these output maps
are invertible; the cancellations identify the equation with the localized
ordinary chain-map tensor/composition equation. The remaining equality is an equality of
chain maps from the pullback of the total tensor complex. In each total degree,
test on every summand P^p tensor N^q. The normalization of the chain tensorators
identifies these maps with the ordinary tensor-pullback tensorators; the termwise
composition map is the mate of pushforwardComp under the pinned tensor-pullback
adjunctions. On pulled-back pure tensor sections, both routes give the tensor
of the same twice-pulled-back sections, because the composite adjunction unit
is the successive unit. The adjunction Hom bijection and the tensor universal
property give equality of the module maps, hence of the chain maps. Localize
this equality and undo the cancellations. This is a triangle for two composable
arrows, with no cartesian square, equality transport, inverse comparison or
extension to arbitrary derived inputs. Zero complexes, identity arrows, and
empty schemes require no separate assumptions. -/
theorem derivedPullbackComposition_tensor_kFlat
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (hN : N.IsKFlat) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    (derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N)) =
    (c f g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N) ≫
      (mixedHomTensorPullbackIso (f ≫ g)).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) := by sorry

end AlgebraicGeometry
