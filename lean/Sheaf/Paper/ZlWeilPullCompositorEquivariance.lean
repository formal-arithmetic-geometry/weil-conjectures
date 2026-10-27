/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V9
-/
module

public import Sheaf.Paper.SfCommonStageDirectImage
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCompIso

/-! # Equivariance of the normalized common-stage pullback compositor

Source: the composition clause of prop-weil-operations, reduced to the integral
pullback associativity and its scalar-extension normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The specified compositor intertwines the specified Frobenius squares.
Source: latest blueprint, lem-fix-weil-operations.proof.md, first paragraph,
and prop-weil-operations, composition clause; Stacks 099N(5).
(blueprint: lem-zl-weil-pull-compositor-equivariance).

Proof: on an integral representative, replace each zlPullComp by the localized
zlIntegralPullComp using zlPullComp_existsUnique. Expand zlFrobeniusSquare as
inverse compositor, equality of the two geometric Frobenius scheme maps, and
compositor. The associativity equation of integralPullbackComposition for the
three triples (F_X,f,g), (f,F_Y,g), (f,g,F_Z) identifies the two paths after
cancelling adjacent inverse compositors. The geometric base-change map_comp
transport is the equality used in sfModelPullComposition, so its equality
comparisons agree on both paths by proof irrelevance. Localize the integral
identity. Pullback-identities scalar compatibility transports it to any larger
coefficient stage. The representative formula for commonStageDerivedPullback
identifies the transported arrows with the actual mapped arrows. Every common
stage object is a localized integral representative; componentwise equality
therefore gives the natural-transformation equation below. No choice of a
Frobenius-stable lattice is used. The calculation applies to zero objects and
empty schemes as well as arbitrary nonreduced finite-type models. -/
theorem zlWeilPullCompositorEquivariance
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerRight (sfModelPullComposition D l hl Ω f g).hom
        (sfCommonStageWeilFrobeniusPullback D l hl X Ω) ≫
      (CategoryTheory.Endofunctor.IsoAlgebra.compCommIso
        (zlFrobeniusSquare D l hl Ω g) (zlFrobeniusSquare D l hl Ω f)).hom =
    (zlFrobeniusSquare D l hl Ω (f ≫ g)).hom ≫
      Functor.whiskerLeft (sfCommonStageWeilFrobeniusPullback D l hl Z Ω)
        (sfModelPullComposition D l hl Ω f g).hom := by sorry

end WeilConjectures
