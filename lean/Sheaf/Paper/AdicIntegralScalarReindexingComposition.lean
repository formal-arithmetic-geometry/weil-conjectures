/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Composition of balanced integral scalar reindexing

This square concerns ambient integral derived modules and extension of scalars only.
It contains neither common-stage realization comparisons nor completion-unit inverses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- The balanced scalar comparison respects the section-normalized compositors.
Source: Bhatt--Scholze, Remark 6.8.15, explicit inverse-image formula;
Stacks 03EL, 07A4 and 0941. This is its scalar-composition refinement.
Proof: on ordinary modules, evaluate both routes on a pure tensor a tensor x.
The three balanced comparisons replace a by its coefficient reindexing, and the
module compositors leave x unchanged. The function normalization of RingReindex
identifies the two coefficient values. The tensor universal property extends the
identity from pure sections to module maps. Apply it termwise to complexes.
The representative equations of the three IntegralReindex data identify their
derived maps after the universal scalar-extension cochain counits. The exact
inverse-image factorization and its compositor identify the remaining factors.
Uniqueness for the total left derived functor transports this cochain equality
to every ambient derived module. Invert the forward square and whisker its
isomorphisms to obtain the displayed inverse equation. No completeness or
constructibility is used.
(blueprint: lem-sf-adic-integral-scalar-reindexing-composition)
-/
theorem integralScalarReindexing_composition
    (C : FamilyCore l D) (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (h_sections : ∀ (M : modules l V.base.left (C.data V).realization)
      (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
      HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : DerivedCategory (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left)) :
    (C.integral T V (g ≪≫ h) E).derived.inv.app K ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((pbcDerivedExtend (coefficientMap l V.base.left (C.data V).realization E)).obj K) =
    (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map
        ((podCompletedDerivedComp l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          h.hom g.hom).hom.app K) ≫
      (C.integral T U g E).derived.inv.app
        ((podCompletedDerivedInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K) ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.integral U V h E).derived.inv.app K) := by
  sorry

end WeilConjectures.AdicQbarRealization
