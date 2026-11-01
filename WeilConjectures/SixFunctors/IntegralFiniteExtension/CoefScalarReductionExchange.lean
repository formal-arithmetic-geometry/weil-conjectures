/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The canonical mixed scalar and quotient map

Source: lem-coef-integral-finite-extension, compatibility with finite quotients.
(blueprint: def-sf-scalar-reduction-exchange)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

/-- The single quotient with commutativity retained.
Source: finite dualizing quotient construction
(blueprint: def-sf-scalar-reduction-exchange). -/
def scalarQuotient {m n : ℕ} (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E X m ⟶ integralCoefficientCommRingSheaf l E X n :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (finiteDualizingQuotientBase l E h)))

/-- Both paths send a residue representative x to the class of its image in L.
Source: blueprint, finite coefficient quotient square
(blueprint: def-sf-scalar-reduction-exchange).
Proof: constant sheafification preserves composition. On the coefficient rings,
quotient induction reduces the square to the same integer inclusion on x. -/
theorem scalarQuotient_square {m n : ℕ} (h : n ≤ m) :
    integralScalarQuotientSheafMap l E L ι X m ≫ scalarQuotient l L X h =
      scalarQuotient l E X h ≫ integralScalarQuotientSheafMap l E L ι X n := by
  unfold integralScalarQuotientSheafMap scalarQuotient
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro ⟨x⟩
  induction x using Quotient.inductionOn' with
  | h x => rfl

/-- Single-quotient restriction agrees with the normalized tower restriction.
Source: finiteDualizingRestriction_eq
(blueprint: def-sf-scalar-reduction-exchange).
Proof: finiteDualizingRestriction_eq identifies the ordinary restrictions;
congruence identifies their derived functors, including the dependent instances. -/
theorem scalarQuotient_restrict {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E X h = pbcDerivedRestrict (scalarQuotient l E X h) := by
  unfold normalizedDVRRes pbcDerivedRestrict
  congr 1
  exact finiteDualizingRestriction_eq l E X h

/-- The restriction square determined by identity on coefficient sections.
Source: blueprint, scalar restriction and quotient compatibility
(blueprint: def-sf-scalar-reduction-exchange). -/
def scalarRestrictionSquare {m n : ℕ} (h : n ≤ m) :
    pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n) ⋙
        normalizedDVRRes l E X h ≅
      normalizedDVRRes l L X h ⋙
        pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m) :=
  (Functor.isoWhiskerLeft _ (eqToIso (scalarQuotient_restrict l E X h))) ≪≫
    pbcDerivedRestrictComp (scalarQuotient l E X h)
      (integralScalarQuotientSheafMap l E L ι X n)
      (integralScalarQuotientSheafMap l E L ι X m ≫ scalarQuotient l L X h)
      (scalarQuotient_square l E L ι X h).symm ≪≫
    (pbcDerivedRestrictComp (integralScalarQuotientSheafMap l E L ι X m)
      (scalarQuotient l L X h) _ rfl).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (scalarQuotient_restrict l L X h).symm) _

/-- The mixed scalar/quotient map is the scalar-adjunction transpose of the
restricted scalar unit followed by the specified restriction square. It is a map,
without an assertion of invertibility (the coefficient square need not be flat).
Source: blueprint, tensor reassociation before finite counit transposition
(blueprint: def-sf-scalar-reduction-exchange). -/
def scalarReductionExchange {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E X h ⋙
        pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m) ⟶
      pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
        normalizedDVRRes l L X h :=
  ((mateEquiv
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n))
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X m))).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionSquare l E L ι X h).hom)).natTrans

end WeilConjectures.IntegralFiniteExtension
