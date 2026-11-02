/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence

/-! # The normalized tower in pro-etale quotient coordinates

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-quotient-coordinate-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The actual quotient coordinates admit normalized consecutive arrows and a joint
scalar realization of the strict completed quotient tower. No etale origins are chosen.

Source: Stacks Project, Tag 09C6, the actual quotient arrows K_(n+1) to K_n;
Tag 06YY, computation and balancing of derived scalar extension; Tags 03CY and 05RU.
(blueprint: lem-weil-pbc-finite-perfect-adic-quotient-coordinate-tower).

Proof: take one flat-term K-flat representative P of M. At level n use its ordinary
sheafified tensor with the completed finite quotient ring. The section map
b tensor x maps to q(b) tensor x gives the consecutive semilinear arrow. The
scalar-extension adjunct is the balancing isomorphism, with inverse sending
b tensor x to b tensor (1 tensor x). Transport these quotient-linear objects and
arrows through phi and the fixed constant-scalar encoding, then restrict to V.
The coefficient encoding is an exact equivalence and inverse image commutes with
derived scalar extension, so the transported arrows are universal.

For each U,W,f, restrict this same representative, transport along the slice
equivalence, and use the counit of associated module sheafification. These maps
identify the scalar realizations with the restrictions of the same strict ordinary
tensor tower. On underlying abelian sheaves, the canonical scalar compositor is
fixed by the sheafification unit; both composites send b tensor x to q(b) tensor x.
Thus the consecutive square commutes before localization, not merely on objects.
The derived counits are invertible on P. Their naturality and the counit identifying
the specified strict representative of completedAdicReduction carry the entire
square to the displayed RestrictedTower, simultaneously at all levels. Independence
of P follows from the universal localization comparisons, which commute with these
actual chain maps. The argument includes the empty chart and the zero ring, and
uses no boundedness or finiteness condition on the cohomology of M. -/
theorem finitePerfectAdic_quotient_coordinate_tower
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) :
    ∃ dJ : ∀ n : ℕ, finitePerfectAdicQuotientCoordinates X d φ M V (n + 1) ⟶
      (normalizationRestrict (ProEt.topology V.left)
        (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj
          (finitePerfectAdicQuotientCoordinates X d φ M V n),
      (∀ n : ℕ, Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (dJ n)))) ∧
    ∃ actualJ : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
      (finitePerfectAdicScalarRealization X d V U W f n).obj
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).mapDerivedCategory.obj
            (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≅
      (finitePerfectAdicRestrictedTower X d W
        ((completedAdicReduction X d).obj M)).obj (op n),
      ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
      (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
        ((ProEtale.upperStar
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))))
            U.hom).mapDerivedCategory.map
            (dJ n) ≫
          (localIsomorphismProEtaleCoefficients U.hom
            (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
              (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≫
        (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
          ((ProEtale.upperStar
            (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
              U.hom).mapDerivedCategory.obj
                (finitePerfectAdicQuotientCoordinates X d φ M V n)) ≫
          (actualJ U W f n).hom =
        (actualJ U W f (n + 1)).hom ≫
          (finitePerfectAdicRestrictedTower X d W
            ((completedAdicReduction X d).obj M)).map
              (homOfLE (Nat.le_succ n)).op := by sorry

end AlgebraicGeometry.Scheme
