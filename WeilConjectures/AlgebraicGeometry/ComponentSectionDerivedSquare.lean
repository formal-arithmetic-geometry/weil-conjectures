/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentSectionMap

/-! # Derived realization square for the constructed component section map
Source: Hemo--Richarz--Scholbach, Remark 3.2 and Proposition 4.3(3)
(blueprint: lem-zl-component-section-derived-square).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]
/-- Component inverse image commutes with constant section-ring realization by extension
along the explicitly constructed map on global sections. This statement needs neither
invertibility of that map nor any scalar normalization or weak contractibility.
Source: HRS Section 3, equations (3.1)--(3.2), Remark 3.2, Proposition 4.3(3)
(blueprint: lem-zl-component-section-derived-square).

Proof: choose a functorial flat-term K-flat resolution P over the source section ring.
The constant sheaf of P is K-flat. Strong monoidal inverse image takes the constant
integer unit to the integer unit and commutes with coproducts and cokernels, hence
identifies pullback of the constant module P with the corresponding constant target
module. The coefficient action on this identification is the pullback of global
sections, which is exactly componentSectionMap by the tensor-unit construction.
Associativity of balanced tensor identifies both ordinary realizations: the forward
map sends b tensor (a tensor p) to ba tensor p; its inverse sends b tensor p to
b tensor (1 tensor p). The balance relation proves that the two maps are inverses;
linearity and naturality hold on pure tensors and therefore everywhere. The maps
commute with every differential, so they are natural inverse maps on unbounded
cochain complexes. Inverse image preserves flat terms and K-flatness, and the tensor
descent theorem makes both constructions send quasi-isomorphisms between these
resolutions to isomorphisms. Descend the comparison through cochain localization.
The universal K-flat comparisons of Evaluation.extensionModel and moduleDerivedExtension
identify the descended functors with the displayed fixed functors. Transport through
the exact sectionwise/internal module equivalences. This gives the entire natural
isomorphism, without assuming boundedness or requiring the section map to be an iso.
For the zero ring all tensor modules vanish, so the same maps apply. -/
theorem component_section_derived_square
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T)) :
    Nonempty (Evaluation.F ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ.X (affineComponentSpace T))
        (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal ⋙ componentDerived Λ.X T α ≅
      RingDerivedScalarExtension.moduleDerivedExtension (componentSectionMap Λ T α) ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
