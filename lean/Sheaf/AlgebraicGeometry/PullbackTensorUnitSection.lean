/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A single pullback cotensorator sends the adjunction unit on an elementary
section tensor to the tensor of the two unit sections.
Source: Stacks Project, Tag 0095, Definition 6.26.1(2); Tag 0096.
(blueprint: lem-sc-pullback-tensor-unit-section)

Proof: On presheaves the pullback cotensorator is the adjoint of the pushforward
lax tensorator. The adjunction unit inserts coefficient 1; the pushforward
tensorator sends a pure tensor to the same pure tensor after restriction of
scalars. Thus its adjoint sends 1 tensor (s tensor t) to
(1 tensor s) tensor (1 tensor t). Sheafification carries elementary presheaf
tensors to tmulSection. The comparison sheafificationCompPullback is defined
by uniqueness of left adjoints, so it carries the presheaf adjunction unit to
the sheaf adjunction unit. The monoidal localization defining pullbackMonoidal
transports exactly this presheaf cotensorator. Applying the transported formula
therefore gives the displayed equality. This concerns only one morphism and
two sections; it requires neither composition coherence nor a unit-object
coherence assertion. Zero sections, zero rings, empty opens and identity
morphisms all obey the same coefficient-1 formula. -/
theorem pullback_δ_app_unit_tmulSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (Functor.OplaxMonoidal.δ (pullback f) M N).app (f ⁻¹ᵁ U)
        (pullbackUnitApp f (M ⊗ N) U (tmulSection s t)) =
      tmulSection (pullbackUnitApp f M U s) (pullbackUnitApp f N U t) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
