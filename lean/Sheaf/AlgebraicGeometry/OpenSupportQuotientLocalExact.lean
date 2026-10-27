/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalSupportQuotientExact
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-!
# Affine locality for quotients by supported sections

Source: Stacks Project, Divisors, Definition 080D (1) and the local reduction in
Tag 080W (blueprint: lem-trf-open-support-quotient-affine-local-exact).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Quotient by the sections vanishing on the specified open.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-open-support-quotient-affine-local-exact). -/
def openSupportQuotient {Y : Scheme.{u}} (U : Y.Opens) (M : Y.Modules) : Y.Modules :=
  cokernel (kernel.ι ((restrictAdjunction U.ι).unit.app M))

/-- The induced map on quotients by supported sections.
Source: Stacks Project, Definition 080D (1)
(blueprint: lem-trf-open-support-quotient-affine-local-exact). -/
def openSupportQuotientMap {Y : Scheme.{u}} (U : Y.Opens)
    {M N : Y.Modules} (b : M ⟶ N) : openSupportQuotient U M ⟶ openSupportQuotient U N :=
  cokernel.map (kernel.ι ((restrictAdjunction U.ι).unit.app M))
    (kernel.ι ((restrictAdjunction U.ι).unit.app N))
    (kernel.map ((restrictAdjunction U.ι).unit.app M)
      ((restrictAdjunction U.ι).unit.app N) b
      (((restrictFunctor U.ι) ⋙ pushforward U.ι).map b)
      ((restrictAdjunction U.ι).unit.naturality b).symm)
    b (kernel.lift_ι _ _ _).symm

/-- Affine-local exactness of principal supported-section quotients implies exactness
of the corresponding global supported-section quotient sequence. This statement has
no blowup or universal base-change hypothesis.
Source: Stacks Project, Definition 080D (1), Tag 080W, affine reduction and locality
(blueprint: lem-trf-open-support-quotient-affine-local-exact).

Proof: On an open immersion z, tensor pullback is the usual restriction, with its
canonical comparison. Restriction preserves kernels and cokernels. On an open W
in the chart, the restriction-unit kernel consists of sections vanishing on
W intersect z^{-1}(U). The displayed equality z^{-1}(U)=D(a) therefore identifies
this kernel with the principal supported-section kernel. For each chart object,
the invertible tilde/Gamma counit identifies the object with the associated sheaf
of its sections. Naturality of the counit identifies both arrows. Taking kernels
and cokernels gives isomorphisms from the restricted global quotients to the
principal support quotients, commuting with the arrows: check the squares after
precomposition with the cokernel projections, which are epimorphisms.
The assumed short exact principal quotient sequence consequently identifies with
the restricted global quotient sequence on each chart. The charts cover Y because
there is a chart whose range contains every point. Their composites vanish
locally and hence globally. The first arrow is locally injective; every germ in
the middle kernel locally comes from the first term; and every germ in the last
term locally lifts from the middle. These local properties are respectively
monomorphism, exactness, and epimorphism for sheaves of modules. They prove the
claimed global short exact sequence. The empty scheme is covered vacuously;
D(a) may be empty or the whole chart, and no regularity assumption is used. -/
theorem openSupportQuotient_shortExact_of_affine
    {Y : Scheme.{u}} (U : Y.Opens) (H : ShortComplex Y.Modules)
    (hlocal : ∀ y : Y, ∃ (R : CommRingCat.{u}) (z : Spec R ⟶ Y)
      (_ : IsOpenImmersion z) (a : R),
      y ∈ Set.range z ∧ z ⁻¹ᵁ U = PrimeSpectrum.basicOpen a ∧
      IsIso ((tensorPullback z).obj H.X₁).fromTildeΓ ∧
      IsIso ((tensorPullback z).obj H.X₂).fromTildeΓ ∧
      IsIso ((tensorPullback z).obj H.X₃).fromTildeΓ ∧
      ∃ w : principalSupportQuotientMap a
          (moduleSpecΓFunctor.map ((tensorPullback z).map H.f)) ≫
        principalSupportQuotientMap a
          (moduleSpecΓFunctor.map ((tensorPullback z).map H.g)) = 0,
        (ShortComplex.mk
          (principalSupportQuotientMap a
            (moduleSpecΓFunctor.map ((tensorPullback z).map H.f)))
          (principalSupportQuotientMap a
            (moduleSpecΓFunctor.map ((tensorPullback z).map H.g))) w).ShortExact) :
    ∃ w : openSupportQuotientMap U H.f ≫ openSupportQuotientMap U H.g = 0,
      (ShortComplex.mk (openSupportQuotientMap U H.f)
        (openSupportQuotientMap U H.g) w).ShortExact := by
  sorry

end AlgebraicGeometry.Scheme.Modules
